require import Int Bool Real SmtMap Perms Binomial AlgTactic StdBigop StdOrder DBool. 
require import List Distr Core FSet AllCore Logic. 
require import Logic. 
require import LeftOrRight. 
require (*  *) SeleneDefinition_sign. 
require (*  *) ROM.

clone include SeleneDefinition_sign. 

(* eager random oracle *)
clone include ROM with
  type in_t       <- h_in,
  type out_t      <- h_out,
  op dout(x:h_in) <- dh_out. 

clone FiniteEager as HRO. 

(*** Strong consistency extractor ***)
(* Takes as input a ballot (pc, c) and a secret data sd *)
(* and returns an identity and a vote.  *)
module type Extractor(H:HOracle.POracle) = {
  proc extract(b: ((ident * upkey * supkey*commitment) * cipher*signature), 
               sd:(ident,opening) fmap * eskey * skey) 
         : (ident * vote option)
}. 

(* strong consistency oracle type *)
module type SCons_Oracle = {
  proc h(inp: h_in) : h_out
  proc g(inp: g_in) : g_out
}.

(* strong consistency oracle instantiation *)
module SCons_Oracle(V: VotingSystem, 
                    H: HOracle.POracle, G: GOracle.POracle) = {
  proc h = H.o
  proc g = G.o
}.

(* Strong consistency first property:                       *)
(* Extract applied to a ballot b <- Vote(pd, id, pc, sc, v) *)
(* returns (id, v) with overwhelming probability                  *)

module SConsis1(V:VotingSystem, Ex:Extractor, H:HOracle.Oracle, G:GOracle.Oracle) = {
  module V = V(H,G)
  module Ex = Ex(H)

  proc main(id:ident, v:vote) : bool = {

    var b, id', v', d, supk, susk;
    
    H.init();
    G.init();

    (* generate public and secret data *)
    (BP.pk,BP.sk) <@ V.setup();
    (supk, susk)  <@ V.register(id, BP.pk, BP.sk);

   
    (* create ballot for voter id and vote v *)
          b       <@ V.vote(BP.pk, id, supk, susk, v);

    (* extract tracker and vote from ballot *)
       (id',v') <@ Ex.extract((b.`1,b.`2,b.`3), BP.sk);

         d  <- v' = Some v;
 
    return d;
  }
}. 


(* Strong consistency second property: *)
(* If the bulletin board BB is valid, then for any (pc, b) in BB *)
(* we have that ValidInd((pc, b), pk) returns true.              *)
(* We split this into two games, one where we run the validboard *)
(* algorithm, and one where we loop through the bulletin board   *)
(* and check to see if each ballot satisfies validInd.           *)

module type SConsis2_adv(O:SCons_Oracle) = {
  proc main(pd : (epkey * pkey * aux)) : ((ident*upkey*supkey*commitment) * cipher*signature) list
}. 

module SConsis2_L(V:VotingSystem, C:ValidIndS, A:SConsis2_adv, H:HOracle.Oracle, G:GOracle.Oracle) = {
 
  module O = SCons_Oracle(V,H,G)
  module V = V(H,G)
  module A = A(O)

  proc main() : bool = {

    var bb, d;
    
    bb <- [];

    H.init();
    G.init();

    (BP.pk, BP.sk) <@ V.setup();
         bb        <@ A.main(BP.pk);
         d         <@ V.validboard(bb, BP.pk);

    return d;

  }

}. 

module SConsis2_R(V:VotingSystem, C:ValidIndS, A:SConsis2_adv, H:HOracle.Oracle, G:GOracle.Oracle) = {

  module O = SCons_Oracle(V,H,G)
  module V = V(H,G)
  module A = A(O)

  proc main() : bool = {
    
    var bb, d, i, b;
    
    bb <- [];

    H.init();
    G.init();

    (BP.pk, BP.sk) <@ V.setup();
         bb        <@ A.main(BP.pk);
    
    i <- 0;
    d <- true;
    while (i < size bb /\ d) {
        b <- nth witness bb i;
        d <@ C(H).valid(b, BP.pk.`1);
      i <- i + 1;
    }

    return d;
  }
}. 


(* Strong consistency third property: *)
(* For an adversarially created bulletinboard BB, let r <- Tally(BB,sd) *)
(* and let r' <- Rho(extract(bb[1],sd), ..., extract(bb[n],sd)).        *)
(* The adversary wins if r = r'.                                        *)

(* We split the experiment in two, one where we use the tally algorithm *)
(* and one where we use the extract algorithm and the result function   *)

(* In the experiments, we also make sure that the result is computed    *)
(* only if all the ballots on the ballot board are valid                *)

module type SConsis3_adv(O:SCons_Oracle) = {
  proc main(pd:(epkey*pkey*aux)) : ((ident * upkey * supkey*commitment) * cipher*signature) list
}. 

module SConsis3_L(V:VotingSystem, C:ValidIndS, A:SConsis3_adv, H:HOracle.Oracle, G:GOracle.Oracle) = {
  
  module O = SCons_Oracle(V,H,G)
  module V = V(H,G)
  module A = A(O)

  proc main() : vote list option = {
    
    var i, bb, b, bv, vtL, vtL', p;

    H.init();
    G.init();

    (* create public and secret data *)
    (BP.pk, BP.sk) <@ V.setup();

    (* adversary creates bulletin board *)
         bb        <@ A.main(BP.pk);

    (* check if the ballots on the board are valid *)
    i <- 0;
    bv <- true;
    while (i < size bb) {
      b <- nth witness bb i;
      if (bv) {
        bv <@ C(H).valid(b, BP.pk.`1);
      }
      i <- i + 1;
    }

    (* compute result using the tally algorithm *)
    vtL <- None;
    if (bv) {
      (vtL', p) <@ V.tally(bb, BP.pk, BP.sk);
         vtL     <- Some vtL';
    }
  return Some (oget vtL).`1;
  }
}.

module SConsis3_R(V:VotingSystem, Ex:Extractor, C:ValidIndS, A:SConsis3_adv, 
                  H:HOracle.Oracle, G:GOracle.Oracle) = {
  
  module O = SCons_Oracle(V,H,G)
  module V = V(H,G)
  module A = A(O)

  proc main() : vote list option = {

    var i, bb, b, bv, vtL, vtL', vtL't, tr, v, iv;
    
    H.init();
    G.init();

    (* create public and secret data *)
    (BP.pk, BP.sk) <@ V.setup();

    (* adversary creates bulletin board *)
         bb        <@ A.main(BP.pk);

    (* check if the ballots on the board are valid *)
    i  <- 0;
    bv <- true;
    while (i < size bb) {
      b <- nth witness bb i;
      if (bv) {
        bv <@ C(H).valid(b, BP.pk.`1);
      }
      i <- i + 1;
    }

    (* compute result using the extract operator *)
    vtL    <- None;
    vtL'   <- [];
    vtL't  <- [];
    if (bv) {
      i <- 0;
      while (i < size bb) {
        b     <- nth witness bb i;
        iv    <@ Ex(H).extract(b, BP.sk);
        v     <- iv.`2;
        tr    <@ PKEtr.ElGamal.dec(BP.sk.`3, oget BP.pk.`3.`3.[iv.`1]);
        vtL't  <- (oget v, oget tr) :: vtL't;
        i     <- i + 1;
      }
      vtL' <$ (duniform (allperms vtL't));
      vtL   <- Some ((unzip1 vtL'), (unzip2 vtL'));
      
    }
    return Some (oget vtL).`1;
  }

}.

section StrongConsistency.

declare module H  <: HOracle.Oracle { -BP }. 
declare module G  <: GOracle.Oracle { -BP, -H, -HRO.ERO }. 
declare module Ev <: PKEvo.Scheme { -BP, -H, -G, -HRO.ERO }.  
declare module C  <: ValidIndS { -BP, -H, -G, -Ev, -HRO.ERO }. 
declare module P  <: Prover { -BP, -H, -G, -Ev, -C }. 
declare module Ve <: Verifier { -BP, -H, -G, -Ev, -C, -P }.
declare module CP <: CommitmentProtocol { -BP, -H, -G, -Ev, -C, -P, -Ve, -HRO.ERO }.
declare module SS <: SignatureScheme {-BP, -H, -G, -Ev, -C, -P, -Ve, -HRO.ERO, -CP}.

declare module Asc2 <: SConsis2_adv { -BP, -H, -G, -Ev, -C, -P, -Ve, -CP, -SS, -HRO.ERO }. 
declare module Asc3 <: SConsis3_adv { -BP, -H, -G, -Ev, -C, -P, -Ve, -CP, -SS }.  

(* useful lemmas *)
lemma duni_ap_weight (l : 'a list) : weight (duniform (allperms l)) = 1%r.  
proof. 
case (l = []) => l_empty.  
have -> : (allperms l = [[]]). rewrite /allperms. 
have -> : size l = 0 by rewrite l_empty => //. 
by rewrite nseq0 allperms_r0.   
rewrite is_losslessP.  
by rewrite duniform_ll. 
trivial. 
have H0 : exists s, s \in allperms l.  exists l. rewrite allpermsP perm_eq_refl. 
rewrite is_losslessP. rewrite duniform_ll => /#. 
by trivial.
qed. 

lemma duni_ap_ll (l : 'a list) : is_lossless (duniform (allperms l)) 
by rewrite /is_lossless; exact/duni_ap_weight.  

(** lossless assumptions **)

(* Random oracles *)
declare axiom Hi_ll : islossless H.init. 
declare axiom Ho_ll : islossless H.o. 

declare axiom Gi_ll : islossless G.init. 
declare axiom Go_ll : islossless G.o. 

(* ValidIndS *)
declare axiom C_vi_ll   : islossless H.o => islossless C(H).valid.
declare axiom C_vi_ll_e : islossless C(HRO.ERO).valid. 

(* encryption of votes *)
declare axiom Ev_kgen_ll  : islossless H.o => islossless Ev(H).kgen. 
declare axiom Ev_kgen_ll' : islossless Ev(HRO.ERO).kgen. 

(* commitment protocol *)
declare axiom CP_gen_ll : islossless CP.gen. 

(* proof system *)
declare axiom PS_p_ll (G <: GOracle.POracle) : islossless G.o => islossless P(G).prove.  

(* signature protocol *)
declare axiom SS_s_ll : islossless SS.sign.
declare axiom SS_g_ll : islossless SS.gen.

(* SConis2 adversary *)
declare axiom Asc2_ll (O <: SCons_Oracle {-Asc2}) : 
  islossless H.o => islossless G.o => islossless Asc2(O).main. 

(* SConsis3 adversary *)
declare axiom Asc3_ll (O <: SCons_Oracle {-Asc3}) : 
  islossless H.o => islossless G.o => islossless Asc3(O).main. 

(* Concrete extractor taking a ballot (pc, c) and secret data BP.sk *)
(* and returns a vote and identity belonging to that voter          *)
module Extract(Ev:PKEvo.Scheme, H:HOracle.POracle) = {
  proc extract(b:((ident * upkey * supkey*commitment) * cipher*signature), 
               sd:(ident,opening) fmap * eskey * skey) = {
    var v;
    var id, c;
    
    id  <- b.`1.`1;
    c   <- b.`2;
    v   <@ Ev(H).dec(sd.`2, id, c);
    return (id,v);
  } 
}. 

(*** Proof of property 1: probability of the extract algorithm returning the correct result ***)
(*** is bounded below by the correctness property of the encryption system                  ***)

lemma sconsis1 (pc : ident) (v : vote) &m : 
    Pr[PKEvo.Correctness(Ev,H).main(v,pc) @ &m : res] <=
    Pr[SConsis1(Selene(Ev,P,Ve,C,CP,SS),Extract(Ev),H,G).main(pc,v) @ &m : res]. 
proof. 
byequiv(_: ={glob Ev, glob H} /\ arg{1}.`1 = arg{2}.`2 /\ arg{1}.`2 = arg{2}.`1 ==> _) => //.
proc;inline*. 
wp. call(_: ={glob H}); first sim. 
wp. 
call{2} SS_s_ll.
call(_: ={glob H}); first sim. 
wp. 
call{2} SS_g_ll.
wp.
while{2} (0 <= i{2} <= card BP.setidents{2}) (card BP.setidents{2} - i{2}).
  progress. auto. progress. by rewrite FDistr.dt_ll. smt(). smt(). smt(). 
wp. while{2} (0 <= i{2} <= card BP.setidents{2}) (card BP.setidents{2} - i{2}). 
  progress. wp;call(CP_gen_ll);auto;progress. by rewrite FDistr.dt_ll. smt(). smt(). smt(). 
wp;rnd{2};while{2} (0 <= i{2} <= card BP.setidents{2}) (card BP.setidents{2} - i{2}). 
  progress. auto;progress. smt(). smt(). smt(). 
wp;rnd{2}. call(_: ={glob H}). wp. call{2} Gi_ll. call(_:true). 
auto;progress. smt(@FSet). smt(). 
rewrite duni_ap_ll. smt(@FSet). smt(). smt(@FSet). smt(). 
qed. 

(* validInd operator *)
declare op validInd : epkey -> ((ident * upkey * supkey*commitment) * cipher*signature) 
                            -> (h_in, h_out) fmap -> bool.

declare axiom validInd_ax (gc:(glob C)) (pd1:epkey) (b:(ident*upkey*supkey*commitment)*cipher*signature) : 
  phoare[C(HRO.ERO).valid : (glob C) = gc /\ arg = (b, pd1) ==>
        (glob C) = gc /\ res = validInd pd1 b HRO.ERO.m] = 1%r. 

(*** Proof of property 2: valid board implies that every ballot is well formed ***)


equiv sconsis2 :
      SConsis2_L(Selene(Ev,P,Ve,C,CP,SS),C,Asc2,HRO.ERO,G).main ~ 
      SConsis2_R(Selene(Ev,P,Ve,C,CP,SS),C,Asc2,HRO.ERO,G).main : 
      ={glob H, glob G, glob Ev, glob C, glob CP, glob SS, glob Asc2, BP.setidents} ==> res{1} => res{2}. 
proof. 
  proc.
  seq 5 5: ( ={ glob HRO.ERO, glob G, glob Ev, glob C, glob CP, glob SS, glob Asc2,
                BP.setidents, bb, BP.pk, BP.sk});
    first by sim.
  inline*.
  wp; sp.
  
  while{2} (   0<=i{2} <= size bb{2}
            /\ d{2} = (forall b, b \in (take i{2} bb{2}) 
                        => validInd BP.pk.`1{2} b HRO.ERO.m{2})
           )
           (size bb{2} - i{2}); progress.
    sp; wp.
    exists* (glob C), BP.pk.`1, b; elim *=> gc epk bx.
    call (validInd_ax gc epk bx).
    auto =>/>; progress.
    + smt(). smt().
    + rewrite eq_iff; progress.
      + move: H4. 
        rewrite (take_nth witness); 
          first by rewrite H H1. 
        rewrite mem_rcons //=.
        elim => Hx.
        + by rewrite Hx H3.
        by rewrite (H2 _ Hx).
      rewrite (H3 _ _). search take nth. 
      rewrite (take_nth witness); 
          first by rewrite H H1. 
      by rewrite mem_rcons //=.
    + smt().  

   while{1} (  0<=i{1} <= size bb0{1}
            /\ e2{1} = (forall b, b \in (take i{1} bb0{1}) 
                        => validInd pd.`1{1} b HRO.ERO.m{1})
           )
           (size bb0{1} - i{1}); progress.
    progress.
    sp 5; wp.
    exists* (glob C), pd.`1, b; elim *=> gc epk bx.
    call (validInd_ax gc epk bx).
    auto =>/>; progress.
    + smt(). smt(). smt().
    + rewrite eq_iff; progress.
      + move: H7. 
        rewrite (take_nth witness); 
          first by rewrite H H1. 
        rewrite mem_rcons //=.
        elim => Hx.
        + by rewrite Hx H6.
        by rewrite (H3 _ Hx).
      rewrite (H6 _ _).  
      rewrite (take_nth witness); 
          first by rewrite H H1. 
      by rewrite mem_rcons //=.
    + smt().

  auto=>/>; progress.
  + by rewrite size_ge0.
  + by rewrite take0.
  + smt().
  + smt().
  + by rewrite take0.
  + smt().
  + (* link e2{1} and d{2} based on i_L and i_R used in take *)
    have Hxo: i_L = size bb{2}.
      by smt().
    case (i_R = size bb{2}) => [Heq | Hneq].
    + smt().

    (* now we are going for contradiction in the hyphothesis *)
    move: H2.
    rewrite negb_and negb_forall //=. 
    move: H4; rewrite /CoreInt.le Hneq //=; move => H4.
    rewrite H4 //=.
    elim => a.
    rewrite negb_imply.
    have := H6 a.
    rewrite Hxo take_size. 
    move => Ha. 
    case (a \in take i_R bb{2}) => Ham.
    + rewrite (Ha _); first by rewrite (mem_take _ _ _ Ham). 
      by done. 
    by done. 
qed.


lemma sconsis2_pr &m : 
    Pr[SConsis2_L(Selene(Ev,P,Ve,C,CP,SS),C,Asc2,HRO.ERO,G).main() @ &m : res] <=
    Pr[SConsis2_R(Selene(Ev,P,Ve,C,CP,SS),C,Asc2,HRO.ERO,G).main() @ &m : res]. 
proof. 
by byequiv sconsis2. 
qed. 



equiv consis3 &m :
  SConsis3_L(Selene(Ev,P,Ve,C,CP,SS), C, Asc3, H, G).main ~ 
  SConsis3_R(Selene(Ev,P,Ve,C,CP,SS), Extract(Ev), C, Asc3, H, G).main : 
  ={glob H, glob G, glob C, glob Ev, glob Asc3, BP.setidents, glob CP} ==> ={res}. 
proof. 
proc;inline*. 
 
(* Everything down to the tallying is equivalent *) 
seq 26 28 : (
  ={glob H, glob G, glob C, glob CP, glob Ev, glob Asc3,  BP.pk, BP.sk, bb, BP.setidents, bv, vtL} 
    /\  (vtL't{2} = [])
); first wp;sim.   

if => //;last first.  

seq 5 1 : (
  ={glob H, glob G, glob C, glob CP, glob Ev, glob Asc3, BP.pk, BP.sk, bb, BP.setidents, bv, vtL}
  /\ (vtL't{2} = []) /\ (bv{1}) /\ (bb0{1} = bb{1}) 
  /\ (pd{1} = BP.pk{1}) /\ (sd{1} = BP.sk{2}) /\ (i1{1} = i{2})
  /\ (rL{1} = []) /\ pd{1} = BP.pk{1}
).
auto;progress. 
 
wp;call{1} (PS_p_ll G Go_ll).
 
seq 1 1 : (
  ={glob H, glob G, glob C, glob CP, glob Ev, glob Asc3, BP.pk, BP.sk, BP.setidents, bv, vtL}
  /\ i1{1} = i{2} /\ vtL't{2} = rL{1} /\ pd{1} = BP.pk{1}
).

while (={BP.pk, BP.sk, glob Ev, glob H} /\ bb0{1} = bb{2} /\ i1{1} = i{2} /\ vtL't{2} = rL{1}
  /\ (sd{1} = BP.sk{2} /\ pd{1} = BP.pk{1})
).

sp;wp. call(_: ={glob H}); first sim. auto;progress.  
    auto;progress. rnd. progress.
qed.
