require import Int Bool Real SmtMap Perms Binomial AlgTactic StdBigop StdOrder DBool. 
require import List Distr Core FSet AllCore Logic. 
require import Logic. 
require import LeftOrRight. 
require (*  *) SeleneDefinition. 
require (*  *) ROM.

clone include SeleneDefinition. 

(* eager random oracle *)
clone include ROM with
  type in_t       <- h_in,
  type out_t      <- h_out,
  op dout(x:h_in) <- dh_out. 

clone FiniteEager as HRO. 

(* VFR adversary for Selene *)
module type VFR_adv(H:HOracle.POracle, G:GOracle.POracle) = {
  proc main(pk: (epkey * PKEtr.pkey * aux)) : ((ident * upkey * commitment) * cipher) list
}.

(* Voting friendly relation for Selene *)
module type VotingRelationS (Ev:PKEvo.Scheme, H:HOracle.POracle) = {
  proc main(s:((epkey * PKEtr.pkey * aux) * 
              ((ident * upkey * commitment) * cipher) list * (vote list * tracker list)),
            w:(((ident,opening) fmap * eskey * skey) * ((ident * upkey * commitment) * cipher) list)) : bool
}. 

(* VFR experiment *)
module VFRS (Ev:PKEvo.Scheme, A:VFR_adv, R:VotingRelationS, CP:CommitmentProtocol,
             H:HOracle.Oracle, G:GOracle.Oracle) = {

  proc main() : bool = {
    var r', r, t, i, j, rel, b, id, et1, et2, et3, ev, v, tr, c;
    var bb, rL;
    var vpk, vsk, tpk, tsk, upk, usk;
    var trL, tpTr, pTr, pPk, pCo, pOp, pi1, pi2;

    trL  <- [];
    tpTr <- [];
    pTr  <- empty;
    pPk  <- empty;
    pCo  <- empty;
    pOp  <- empty;

    pi2 <- [];
    
    rL   <- [];
    bb   <- [];

    H.init();
    G.init();

    (vpk,vsk) <@ Ev(H).kgen();
    (tpk,tsk) <@ PKEtr.ElGamal.kg();

    (* Create the trivial encryption *)
    i <- 0;
    while (i < card BP.setidents) {
      et1  <@ PKEtr.ElGamal.enc_t(tpk, nth witness (elems BP.setidents) i);
      tpTr <- et1 :: tpTr;

      i <- i + 1;
    }

    trL <$ duniform (allperms (elems BP.setidents));

    (* Create a fresh encryption of a random tracker to every identity,
        this is output of the re-encryption mixnet *)
    i <- 0;
    while (i < card BP.setidents) {
      id        <- nth witness (elems BP.setidents) i;
      et1       <@ PKEtr.ElGamal.enc(tpk, nth witness trL i); 
      pTr.[id] <- et1;

      (* Generate the commitment keys *)
      (upk, usk) <@ CP.gen();
      pPk.[id] <- upk;

      i <- i + 1;
    }

    pi1 <- setupTrackers((tpTr, pTr),(trL, tsk));

    (* Generation of Tracker number commitments *)
   i <- 0;
   while (i < card BP.setidents) {
      id <- nth witness (elems BP.setidents) i;
      
      t <$ FDistr.dt; 
      et1 <@ PKEtr.ElGamal.enc(tpk, (oget pPk.[id])^t);
      et2 <@ PKEtr.ElGamal.enc(tpk, PKEtr.G.g^t);

      et3 <@ PKEtr.ElGamal.mult(et1, oget pTr.[id]);
        c <@ PKEtr.ElGamal.dec(tsk, et3);

      pi2 <- setupCommitments((et1,et2,c),(t,tsk)) :: pi2;

      pCo.[id] <- oget c;
      pOp.[id] <- (nth witness trL i, t);
      
      i <- i + 1;
   }

    BP.sk <- (pOp,vsk,tsk);

    bb  <@ A(H,G).main((vpk,tpk,(BP.setidents, tpTr, pTr, pPk, pCo,pi1,pi2)));

    j <- 0;
    while (j < size bb) {
      b  <- nth witness bb j;
      ev <- b.`2;
      id <- b.`1.`1;
      v  <@ Ev(H).dec(vsk, id, ev);
      tr <@ PKEtr.ElGamal.dec(tsk, oget pTr.[id]);
      rL <- (oget v, oget tr) :: rL;
      j  <- j + 1;
    }

    r' <$ duniform (allperms rL);
    r  <- (unzip1 r', unzip2 r');

    rel <@ R(Ev,H).main(((vpk,tpk,(BP.setidents, tpTr, pTr, pPk, pCo,pi1,pi2)), sPublish bb, r), ((pOp,vsk,tsk), bb));
    
    return !rel;
  }
}.

(******* CCA adversary ********)

module BCCA(V:VotingSystem, CP:CommitmentProtocol, A:DU_MB_BPRIV_adv, S:Simulator, IO:Ind1CCA_Oracles) = {

    var bb : (ident * (ident * upkey * commitment) * cipher) list

    module V = V(HRO.ERO, S)

    module O = {
      
      proc h = IO.o
      proc g = S.o

      proc vote(id:ident, v0 v1 : vote) = {
        var c;

        if (id \in BP.setH) {
          c <@ IO.enc(id, v0, v1);
          BP.vmap.[id] <- (c, c, v0, v0) :: (odflt [] BP.vmap.[id]);
          bb <- (id, oget BP.pubmap.[id], c) :: bb;
        }
      }

    proc verify(id:ident) = {
      var ok, sv;
      if (id \in BP.setidents){
        BP.setchecked <- BP.setchecked `|` (fset1 id);
        sv <- odflt [] (BP.vmap.[id]);
        ok <@ V.verifyvote(id, (oget (ohead sv)).`2, (oget (ohead sv)).`3, 
                           BP.bb, BP.bbstar, oget BP.pubmap.[id], oget BP.secmap.[id]);
        if (ok) {
          BP.sethappy <- BP.sethappy `|` (fset1 id);
        }
      }
      return BP.sethappy;
    }

    proc board() = {
      return sPublish (rem_ids bb);
    }
  }

  module A = A(O)

  proc main(pk:epkey) : bool = {

    var i, id, upk, usk, trL, d, ct, cL, mL, et1, et2, et3, vt;
    var valid, valid', da, t, c;
    var j, rL, b, sv, k, v, ev, tr';
    var pTr, tpk, tsk, tpTr, pPk, pCo, pOp, pi1, pi2;

    BP.vmap    <- empty;
    BP.pubmap  <- empty;
    BP.secmap  <- empty;
    BP.secmapD <- empty;
    BP.setchecked <- fset0;
    BP.sethappy   <- fset0;

    bb <- [];
    
    S.init();

    trL  <- [];
    tpTr <- [];
    pi2 <- [];
    pTr  <- empty;
    pPk  <- empty;
    pCo  <- empty;
    pOp  <- empty;

    (tpk, tsk) <@ ElGamal.kg();

    (* trivial encryption *)
    i <- 0;
    while (i < card BP.setidents) {
      et1  <@ PKEtr.ElGamal.enc_t(tpk, nth witness (elems BP.setidents) i);
      tpTr <- et1 :: tpTr;

      i <- i + 1;
    }

    trL <$ duniform (allperms (elems BP.setidents));

    (* Create a fresh encryption of a random tracker to every identity *)
    i <- 0;
    while (i < card BP.setidents) {
      id       <- nth witness (elems BP.setidents) i;
      et1       <@ PKEtr.ElGamal.enc(tpk, nth witness trL i); 
      pTr.[id] <- et1;

      (* Generate the commitment keys *)
      (upk, usk) <@ CP.gen();
      pPk.[id] <- upk;

      i <- i + 1;
    }

    pi1 <- setupTrackers((tpTr, pTr),(trL, tsk));
    
    (* Generation of Tracker number commitments *)
   i <- 0;
   while (i < card BP.setidents) {
      id <- nth witness (elems BP.setidents) i;
      
      t <$ FDistr.dt; 
      et1 <@ PKEtr.ElGamal.enc(tpk, (oget pPk.[id])^t);
      et2 <@ PKEtr.ElGamal.enc(tpk, PKEtr.G.g^t);

      et3 <@ PKEtr.ElGamal.mult(et1, oget pTr.[id]);
      c <@ PKEtr.ElGamal.dec(tsk, et3);

      pi2 <- setupCommitments((et1,et2,c),(t,tsk)) :: pi2;

      pCo.[id] <- oget c;
      pOp.[id] <- (nth witness trL i, t);
      
      i <- i + 1;
   }

    BP.pk <- (pk, tpk, (BP.setidents, tpTr, pTr, pPk, pCo, pi1, pi2));

    (* register *)
      i <- 0;
      while (i < card BP.setidents) {
        id  <- nth witness (elems BP.setidents) i;
        d   <- oget pOp.[id];
        upk <- oget pPk.[id];
        ct  <- oget pCo.[id];
        BP.secmap.[id] <- d;
        BP.pubmap.[id] <- (id, upk, ct);
        if (id \in BP.setD) {
          BP.secmapD.[id] <- oget BP.secmap.[id];
        }
        i <- i + 1;
      }

      (* adversary creates BP.bb *)
      BP.bb <@ A.create_bb(BP.pk, BP.secmapD, BP.pubmap, BP.setHcheck);

      (* check if adversary board is valid *)
      valid <@ V.validboard(BP.bb, BP.pk);

      (* tally *)
      
      (* make BP.bb ready for decryption *)
      cL <- map (fun x: ((ident * upkey * commitment) * cipher) => (x.`2, x.`1.`1)) BP.bb;
      
      (* decrypt everything in BP.bb *)
      mL <@ IO.dec(cL);

      j <- 0;
      rL <- [];
      while (j < size BP.bb) {
        b    <- nth witness BP.bb j;
        ev   <- b.`2;
        id   <- b.`1.`1;
        if ( (ev, id) \in BS.encL) {
          (* Get the vote from BP.vmap that matches the ballot *)
          sv <- odflt [] BP.vmap.[id]; (* get list for voter id *)
          k  <- find (fun (x : cipher * cipher * vote * vote) => x.`1 = ev) sv; (* first index where b appears *)
          v  <- Some (oget (onth sv k)).`4; (* the vote at that index *)
        } else {
          v  <- nth witness mL j;  
        }
        tr'  <@ ElGamal.dec(tsk, oget BP.pk.`3.`3.[id]);
        rL   <- (oget v, oget tr') :: rL;
        j    <- j + 1;
      }

      vt    <$ duniform (allperms rL);
      BP.r  <- (unzip1 vt, unzip2 vt);

      (* if statements: adversary makes a guess if everything looks fine *)
      if (!(BP.setHcheck \subset fdom BP.vmap)) {
        BP.d <$ {0,1};
      } else {
        if (!valid) {
          BP.d <$ {0,1};
        } else {
            BP.pi   <@ S.prove(BP.pk, sPublish BP.bb, BP.r); 
             da     <@ A.initial_guess();
          BP.bbstar <@ A.get_tally(BP.r, BP.pi);
          valid'    <@ V.verifytally((BP.pk, sPublish BP.bb, BP.bbstar.`1), BP.bbstar.`2);
          if (!valid') {
            BP.d <$ {0,1};
          } else {
            BP.d <@ A.final_guess();
            if (!(BP.setHcheck \subset BP.sethappy)) {
              BP.d <- da; 
            } 
            if (!(BP.setHcheck \subset BP.setchecked)) {
              BP.d <$ {0,1};
            }
          }
        }
      }

    return BP.d;
  }
}.

(************************************************************)
(********************* DU-MB-BPRIV **************************)
(************************************************************)

section DU_MB_BPRIV.

declare module G  <: GOracle.Oracle { -BP, -HRO.ERO, -BPS, -BS, -BCCA }.   
declare module Ev <: PKEvo.Scheme { -BP, -HRO.ERO, -G, -BPS, -BS, -BCCA}.  
declare module S  <: Simulator { -BP, -HRO.ERO, -G, -Ev, -BPS, -BS, -BCCA }. 
declare module Ve <: Verifier { -BP, -HRO.ERO, -G, -Ev, -S, -BPS, -BS, -BCCA }. 
declare module P  <: Prover { -BP, -HRO.ERO, -G, -Ev, -S, -Ve, -BPS, -BS, -BCCA }. 
declare module R  <: VotingRelationS { -BP, -HRO.ERO, -G, -Ev, -S, -Ve, -P, -BPS, -BS, -BCCA }.
declare module C  <: ValidIndS { -BP, -HRO.ERO, -G, -Ev, -S, -Ve, -P, -BPS, -BS, -R, -BCCA }. 
declare module A  <: DU_MB_BPRIV_adv { -BP, -HRO.ERO, -G, -Ev, -S, -Ve, -P, -C, -BPS, -BS, -R, -BCCA}. 
declare module CP <: CommitmentProtocol { -BP, -HRO.ERO, -G, -Ev, -S, -Ve, -P, -C, -BPS, -BS, -A, -R, -BCCA}. 

(*** Lossless assumptions ***)

(** Oracles **)
declare axiom Gi_ll : islossless G.init. 
declare axiom Go_ll : islossless G.o. 


(** MB-BPRIV adversary **)
declare axiom A_a1_ll (O <: DU_MB_BPRIV_oracles { -A }):
  islossless O.vote => islossless O.board => islossless O.h => islossless O.g => islossless A(O).create_bb. 
declare axiom A_a2_ll (O <: DU_MB_BPRIV_oracles { -A }): 
  islossless O.board => islossless O.h => islossless O.g => islossless A(O).get_tally. 
declare axiom A_a3_ll (O <: DU_MB_BPRIV_oracles { -A }): 
  islossless O.verify => islossless O.h => islossless O.g => islossless A(O).final_guess. 
declare axiom A_a4_ll (O <: DU_MB_BPRIV_oracles { -A }): 
  islossless O.h => islossless O.g => islossless A(O).initial_guess. 


(** Proof system **)
declare axiom PS_p_ll (G <: GOracle.POracle { -P }) : islossless G.o => islossless P(G).prove. 
declare axiom PS_v_ll (G <: GOracle.POracle { -Ve }) : islossless G.o => islossless Ve(G).verify. 


(** Encryption **)
declare axiom Ev_kg_ll  (H <: HOracle.POracle { -Ev }) : islossless H.o => islossless Ev(H).kgen. 
declare axiom Ev_enc_ll (H <: HOracle.POracle { -Ev }) : islossless H.o => islossless Ev(H).enc. 
declare axiom Ev_dec_ll (H <: HOracle.POracle { -Ev }) : islossless H.o => islossless Ev(H).dec. 
 
lemma Et_kg_ll  : islossless ElGamal.kg. 
proof. 
by proc;auto;rewrite FDistr.dt_ll. 
qed. 

lemma Et_enc_ll : islossless ElGamal.enc. 
proof. 
by proc;auto;rewrite FDistr.dt_ll. 
qed. 

lemma Et_dec_ll : islossless ElGamal.dec. 
by proc;auto.
qed.  

(** Encryption with HRO.ERO **)
lemma Ev_kg_ll'  : islossless Ev(HRO.ERO).kgen by apply (Ev_kg_ll HRO.ERO HRO.ERO_o_ll). 
lemma Ev_enc_ll' : islossless Ev(HRO.ERO).enc by apply (Ev_enc_ll HRO.ERO HRO.ERO_o_ll).  
lemma Ev_dec_ll' : islossless Ev(HRO.ERO).dec by apply (Ev_dec_ll HRO.ERO HRO.ERO_o_ll).  

(** ZK simulator **)
declare axiom Si_ll : islossless S.init. 
declare axiom So_ll : islossless S.o. 
declare axiom Sp_ll : islossless S.prove. 

(** Commitment protocol **)
declare axiom CP_gen_ll  : islossless CP.gen. 
declare axiom CP_com_ll  : islossless CP.commit. 
declare axiom CP_open_ll : islossless CP.open. 

(** VFR **)
declare axiom R_m_ll : islossless R(Ev,HRO.ERO).main.

(** ValidInd operator **)
declare axiom C_vi_ll (H <: HOracle.POracle { -C }) : islossless H.o => islossless C(H).valid.

(*** Useful and necessary axioms and lemmas ***)
local equiv So_ll2: S.o ~ S.o : ={arg, glob S} ==> ={res, glob S}.
proof. by proc true. qed.  

(* encryption does not change state of encryption scheme *)
declare axiom Ev_e_eq (ge: (glob Ev)):
   phoare[Ev(HRO.ERO).enc : (glob Ev) = ge ==> (glob Ev) = ge] = 1%r. 

(*** Axioms linking key generation and get_epk operator ***)
declare axiom Ev_kgen_get_epk:
 equiv [Ev(HRO.ERO).kgen ~ Ev(HRO.ERO).kgen : ={glob HRO.ERO, glob Ev} ==> ={glob HRO.ERO, glob Ev, res} /\ res{1}.`1 = get_epk res{1}.`2]. 

(*** Sampling a list from list of all permutations doesn't fail ***)
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

lemma in_rem_ids (id:ident) (pc:ident*upkey*commitment) (c:cipher) 
                  (bb:(ident*(ident*upkey*commitment)*cipher) list) : (id, pc, c) \in bb => (pc, c) \in rem_ids bb.  
proof. 
move => in_bb. 
rewrite /rem_ids.
rewrite mapP. exists (id, pc, c). apply in_bb. 
qed. 

(* Decryption operator for votes *)
declare op dec_cipher_vo: eskey -> ident -> cipher  -> 
              (h_in, h_out) SmtMap.fmap -> vote option.

(* Decryption operator for trackers *)
declare op dec_cipher_tr: eskey -> cipher  -> tracker option.

declare axiom Eenc_dec_vo (sk2: eskey) (pk2: epkey) (l2: ident) (p2: vote): 
    (pk2 = get_epk sk2) =>
    equiv [Ev(HRO.ERO).enc ~ Ev(HRO.ERO).enc : 
          ={glob HRO.ERO, glob Ev, arg} /\ arg{1}=( pk2, l2, p2) 
          ==> 
          ={glob HRO.ERO, glob Ev,  res} /\
          Some p2 = dec_cipher_vo sk2 l2 res{1} HRO.ERO.m{1}]. 

 (* axioms for linking E.dec to dec_cipher operator *)   
declare axiom Edec_Odec_vo (ge: (glob Ev)) (sk2: eskey) (l2: ident) (c2: cipher):
    phoare [Ev(HRO.ERO).dec:  
           (glob Ev) =ge /\ arg = (sk2, l2, c2)
           ==>   
           (glob Ev) =ge /\
           res = dec_cipher_vo sk2 l2 c2 HRO.ERO.m ] = 1%r.

local lemma Edec_Odec_eq_vo (sk2: eskey)(l2: ident) (c2: cipher):
  equiv [Ev(HRO.ERO).dec ~ Ev(HRO.ERO).dec :
          ={glob HRO.ERO, glob Ev, arg}/\ arg{1} = (sk2, l2, c2)
           ==>   
           ={glob HRO.ERO, glob Ev, res} /\
           res{1} = dec_cipher_vo sk2 l2 c2 HRO.ERO.m{1} ].
proof.
  proc*=>//=. 
  exists* (glob Ev){1}; elim* => ge.
  call{1} (Edec_Odec_vo ge sk2 l2 c2 ).
  call{2} (Edec_Odec_vo ge sk2 l2 c2 ). 
  by auto.
qed.

(* Operator to reverse the order of tuples *)
op flip (bb : (ident * cipher) list) = map (fun b : (ident * cipher) => (b.`2, b.`1)) bb.

(* Operator removing the first element of a three tuple *)
op rem_fst3 (x : ('a * 'b * 'c)) = (x.`2, x.`3).

(* Operator removing the first element of a four tuple *)
op rem_fst4 (x : ('a * 'b * 'c * 'd)) = (x.`2, x.`3, x.`4). 

(****************************************************************************************************)
(****************************************************************************************************)
(****************************************************************************************************)

(******************************************************************************************************)
(************************ Constructed adversaries from du-mb-bpriv adversary **************************)
(******************************************************************************************************)

(****** ZK adversary *******)

module type VotingAdvZK (H:HOracle.Oracle, O:GOracle.POracle) = {
  proc a1() : ((epkey * pkey * aux) * ((ident * upkey * commitment) *
                  cipher) list * (vote list * tracker list)) * (((ident,opening) fmap * eskey * PKEtr.skey) *
                  ((ident * upkey * commitment) * cipher) list) {H.init, H.o, O.o}
  proc a2(pi : (prf option)) : bool {H.o, O.o}
}.

module BZK(Ev:PKEvo.Scheme, P:Prover, C:ValidIndS, Ve:Verifier, 
           A:DU_MB_BPRIV_adv, CP:CommitmentProtocol,
           H:HOracle.Oracle, G:GOracle.POracle) = {

    module O   = DU_MB_BPRIV_oracles(Selene(Ev,P,Ve,C, CP),H,G,Left)
    module Smv = Selene(Ev,P,Ve,C,CP,H,G)

    proc a1() : ((epkey * pkey * aux) * ((ident * upkey * commitment) *
                  cipher) list * (vote list * tracker list)) * (((ident,opening) fmap * eskey * skey) *
                  ((ident * upkey * commitment) * cipher) list) = {

      var i, id, ct, d, upk, vt;
      var rL, j, b, ev, v, tr';

      BP.vmap    <- empty;
      BP.pubmap  <- empty;
      BP.secmap  <- empty;
      BP.secmapD <- empty;            
      BP.bb0     <- [];
      BP.bb1     <- [];
      BP.setchecked <- fset0;
      BP.sethappy   <- fset0;

      H.init();

      (BP.pk, BP.sk) <@ Smv.setup();

      i <- 0;
      while (i < card BP.setidents) {
        id  <- nth witness (elems BP.setidents) i;
        d   <- oget BP.sk.`1.[id];
        upk <- oget BP.pk.`3.`4.[id];
        ct  <- oget BP.pk.`3.`5.[id];
        BP.secmap.[id] <- d;
        BP.pubmap.[id] <- (id, upk, ct);

        if (id \in BP.setD) {
          BP.secmapD.[id] <- oget BP.secmap.[id];
        }

        i <- i + 1;
      }

      BP.bb <@ A(O).create_bb(BP.pk, BP.secmapD, BP.pubmap, BP.setHcheck);

      rL <- [];

      j <- 0;
      while (j < size BP.bb) {
            
        b    <- nth witness BP.bb j;
        ev   <- b.`2;
        id   <- b.`1.`1;
        v    <@ Ev(H).dec(BP.sk.`2, id, ev);
        tr'  <@ ElGamal.dec(BP.sk.`3, oget BP.pk.`3.`3.[id]);

        rL   <- (oget v, oget tr') :: rL;

         j   <- j + 1;
      }
          
      vt   <$ (duniform (allperms rL));
      BP.r <- (unzip1 vt, unzip2 vt);
      
      
      return ((BP.pk, sPublish BP.bb, BP.r), (BP.sk, BP.bb));
    }

    proc a2(pi:prf option) : bool = {
      var valid, valid', d;
      
      valid <@ Smv.validboard(BP.bb, BP.pk);

      if (!(BP.setHcheck \subset fdom BP.vmap)) {
        BP.d <$ {0,1};
      } else {
        if (!valid) {
          BP.d <$ {0,1};
        } else {
              d     <@ A(O).initial_guess();
          BP.bbstar <@ A(O).get_tally(BP.r, oget pi);
          valid'    <@ Smv.verifytally((BP.pk, sPublish BP.bb, BP.bbstar.`1), BP.bbstar.`2);
          if (!valid') {
            BP.d <$ {0,1};
          } else {
            BP.d <@ A(O).final_guess();
          if (!(BP.setHcheck \subset BP.sethappy)) {
            BP.d <- d; 
          } 
          if (!(BP.setHcheck \subset BP.setchecked)) {
            BP.d <$ {0,1};
          }
        }
      }
    }
    return BP.d;
    }
}. 

(******* Losslessness for BZK ********)
local lemma BZK_a1_ll (H <: HOracle.Oracle { -BP, -A}) (G <: GOracle.POracle { -A }) : 
    islossless H.init => islossless H.o => islossless G.o =>
    islossless BZK(Ev,P,C,Ve,A,CP,H,G).a1. 
proof. 
move => Hi_ll Ho_ll Go_ll. 
proc;inline*. 
wp;rnd. while(0 <= j <= size BP.bb) (size BP.bb - j). 
progress. 
wp. call(Ev_dec_ll H Ho_ll). 
auto;progress => /#.   
wp. 
call(A_a1_ll (<: BZK(Ev,P,C,Ve,A,CP,H,G).O)).
proc;inline*. 
if => //;wp;call(Ev_enc_ll H Ho_ll);wp;call(Ev_enc_ll H Ho_ll);wp;auto. 
proc;inline*;auto. 
while (0 <= i <= card BP.setidents) (card BP.setidents - i);progress;auto. smt(). 
  while (0 <= i0 <= card BP.setidents) (card BP.setidents - i0);progress;auto.
 progress;[by rewrite FDistr.dt_ll | smt() | smt() | smt()]. 
while(0 <= i0 <= card BP.setidents) (card BP.setidents - i0);progress;auto. 
call(CP_gen_ll);auto;progress;[by rewrite FDistr.dt_ll | smt() | smt() | smt()]. 
while(0 <= i0 <= card BP.setidents) (card BP.setidents - i0);progress;auto. smt(). 
call(Ev_kg_ll H Ho_ll). 
wp;call(_:true);wp;skip;progress. by rewrite FDistr.dt_ll.
rewrite /card size_ge0; smt(); rewrite /card size_ge0; smt(); rewrite size_ge0;
  smt(); apply duni_ap_weight; apply duni_ap_weight. 
smt(). by rewrite duni_ap_weight. smt(@FSet). smt(). smt(@FSet). smt().
smt(@FSet). smt(). rewrite size_ge0. smt(). 
by rewrite duni_ap_weight.  
qed. 

local lemma BZK_a2_ll (H <: HOracle.Oracle { -A, -BP }) (G <: GOracle.POracle { -A, -BP }) :
  islossless H.o => islossless G.o => islossless BZK(Ev,P,C,Ve,A,CP,H,G).a2. 
proof. 
move => Ho_ll Go_ll. 
proc. 
seq 1 : true => //.  
inline*.  
wp;while(0 <= i <= size bb) (size bb - i);progress. 
wp. 
call(C_vi_ll H Ho_ll). wp;skip;progress => /#.   
auto;progress. rewrite size_ge0. smt(). 
if => //; first rnd;skip;progress. rewrite dboolE => />.   
if => //. rnd;progress. by auto;progress;rewrite dboolE. 
seq 3 : true => //. 
inline*.
wp;call(PS_v_ll G Go_ll);wp;call(A_a2_ll (<: BZK(Ev,P,C,Ve,A,CP,H,G).O)). 
proc;inline*;auto.  
auto;progress. 
call(A_a4_ll (<: BZK(Ev,P,C,Ve,A,CP,H,G).O));auto. 
if => //; first rnd;skip;progress. rewrite dboolE => />.  
seq 1 : valid' => //. 
call(A_a3_ll (<: BZK(Ev,P,C,Ve,A,CP,H,G).O)). 
proc;inline*;auto. 
if =>//.
wp; call(CP_open_ll);wp;skip;progress. 
trivial. 
if => //.  sp. if => //. rnd;skip;progress;rewrite dboolE => />. 
if => //. rnd;skip;progress. rewrite dboolE => />.   
hoare;call(_:true); [1..3: by auto]; first trivial.
qed. 

local lemma BZK_a2_ll' (H <: HOracle.Oracle { -A, -BP }) (G <: GOracle.POracle { -A, -BP })
                        (P <: Prover { -Ev, -C, -Ve, -A, -ZK_L, -BPS, -BP, -H, -G }) :
  islossless H.o => islossless G.o => islossless P(G).prove => islossless BZK(Ev,P,C,Ve,A,CP,H,G).a2. 
proof. 
move => Ho_ll Go_ll Pp_ll. 
proc. 
seq 1 : true => //.  
inline*.  
wp;while(0 <= i <= size bb) (size bb - i);progress. 
wp.  
call(C_vi_ll H Ho_ll);wp;skip;progress => /#.
auto;progress. rewrite size_ge0. smt(). 
if => //; first rnd;skip;progress. rewrite dboolE => />.  
if => //. rnd;skip;progress;rewrite dboolE => />. 
seq 3 : true => //. 
inline*.
wp;call(PS_v_ll G Go_ll);wp;call(A_a2_ll (<: BZK(Ev,P,C,Ve,A,CP,H,G).O)). 
proc;inline*;auto.  
auto;progress. 
call(A_a4_ll (<: BZK(Ev,P,C,Ve,A,CP,H,G).O));auto. 
if => //; first rnd;skip;progress. rewrite dboolE => />.  
seq 1 : valid' => //. 
call(A_a3_ll (<: BZK(Ev,P,C,Ve,A,CP,H,G).O)). 
proc;inline*;auto. 
if=>//; wp.
call(CP_open_ll);wp;skip;progress. 
trivial. 
if => //;sp. 
if => //;rnd;skip;progress;rewrite dboolE => //. 
if => //; first rnd;skip;progress. rewrite dboolE => />. 
hoare;call(_:true); [1..3: by auto]; first trivial.
qed. 

(****** VFR  adversary ******)

module BVFR(V:VotingSystem, A:DU_MB_BPRIV_adv, CP:CommitmentProtocol, H:HOracle.POracle, G:GOracle.POracle) = {
  
  module L = DU_MB_BPRIV_oracles(V,H,G,Left)

  proc main(pk: epkey * PKEtr.pkey * aux) : ((ident * upkey * commitment) * cipher) list = {
    
    var i, id, upk, ct, d;
    
    BP.vmap    <- empty;
    BP.pubmap  <- empty;
    BP.secmap  <- empty;
    BP.secmapD <- empty;
    BP.bb0     <- [];
    BP.bb1     <- [];
    BP.pk      <- pk;

    i <- 0;
      while (i < card BP.setidents) {
        id  <- nth witness (elems BP.setidents) i;
        d   <- oget BP.sk.`1.[id];
        upk <- oget BP.pk.`3.`4.[id];
        ct  <- oget BP.pk.`3.`5.[id];
        BP.secmap.[id] <-  d;
        BP.pubmap.[id] <- (id, upk, ct);

        if (id \in BP.setD) {
          BP.secmapD.[id] <- oget BP.secmap.[id];
        }

        i <- i + 1;
      }
   BP.bb <@ A(L).create_bb(BP.pk, BP.secmapD, BP.pubmap, BP.setHcheck);
   return BP.bb; 
  }
}. 


(*******************************************************************************************************)
(********** Proof that SeleneMV satisfies DU-MB-BPRIV, structured as a sequence of games. **************)
(********** We start from the left side.                                                  **************)
(*******************************************************************************************************)


(************* We first inline some of the algorithms in the original game to prepare ***************)
(************* for further modification.                                              ***************)

local module G0L' (Ev:PKEvo.Scheme, P:Prover, Ve:Verifier, C:ValidIndS, CP:CommitmentProtocol,
                   A:DU_MB_BPRIV_adv, H:HOracle.Oracle, G:GOracle.Oracle) = {

    module O   = DU_MB_BPRIV_oracles(Selene(Ev,P,Ve,C,CP), H, G, Left)
    module A   = A(O)
    module Smv = Selene(Ev,P,Ve,C,CP,H,G)

    proc main() : bool = {
      var i;
      var id, upk, ct, d, da;
      var valid, valid';
      var rL, j, b, ev, v, tr', vt;

      BP.vmap       <- empty;
      BP.pubmap     <- empty;
      BP.secmap     <- empty;
      BP.secmapD    <- empty;
      BP.bb0        <- [];
      BP.bb1        <- [];
      BP.setchecked <- fset0;
      BP.sethappy   <- fset0;
      
      H.init();
      G.init();
      
      (* setup *)
      (BP.pk, BP.sk) <@ Smv.setup();

      (* register *)
      i <- 0;
      while (i < card BP.setidents) {
        id  <- nth witness (elems BP.setidents) i;
         d  <- oget BP.sk.`1.[id];
        upk <- oget BP.pk.`3.`4.[id];
        ct  <- oget BP.pk.`3.`5.[id];
        BP.secmap.[id] <- d;
        BP.pubmap.[id] <- (id, upk, ct);

        if (id \in BP.setD) {
          BP.secmapD.[id] <- oget BP.secmap.[id];
        }

        i <- i + 1;
      }

      (* adversary creates bulletin board *)
      BP.bb <@ A.create_bb(BP.pk, BP.secmapD, BP.pubmap, BP.setHcheck);

      if (!(BP.setHcheck \subset fdom BP.vmap)) {
        BP.d <$ {0,1};
      } else {
        valid <@ Smv.validboard(BP.bb, BP.pk);
        if (!valid) {
          BP.d <$ {0,1};
        } else {
          (* We now tally *)
          rL <- [];

          j <- 0;
          while (j < size BP.bb) {
            
            b    <- nth witness BP.bb j;
            ev   <- b.`2;
            id   <- b.`1.`1;
            v    <@ Ev(H).dec(BP.sk.`2, id, ev);
            tr'  <@ ElGamal.dec(BP.sk.`3, oget BP.pk.`3.`3.[id]);

            rL  <- (oget v, oget tr') :: rL;

            j <- j + 1;
          }
          vt    <$ (duniform (allperms rL));
          BP.r  <- (unzip1 vt, unzip2 vt);
          BP.pi <@ P(G).prove((BP.pk, sPublish BP.bb, BP.r), (BP.sk, BP.bb));
            da  <@ A.initial_guess();
          BP.bbstar <@ A.get_tally(BP.r, BP.pi);
          valid'    <@ Smv.verifytally((BP.pk, sPublish BP.bb, BP.bbstar.`1), BP.bbstar.`2);
          if (!valid') {
            BP.d <$ {0,1};
          } else {
            BP.d <@ A.final_guess();
          if (!(BP.setHcheck \subset BP.sethappy)) {
            BP.d <- da; 
          } 
          if (!(BP.setHcheck \subset BP.setchecked)) {
            BP.d <$ {0,1};
          }
         }
        }
      }
      return BP.d;
    }
}.

(********* G0L' is equivalent to original attack game on the left side **********)
local lemma DU_MB_BPRIV_L_G0L'_equiv &m : 
  BP.setidents{m} = BP.setH{m} `|` BP.setD{m} =>
    Pr[DU_MB_BPRIV_L(Selene(Ev,P,Ve,C,CP), A, HRO.ERO, G).main() @ &m : res]
    = Pr[G0L'(Ev,P,Ve,C,CP,A,HRO.ERO,G).main() @ &m : res]. 
proof. 
move => ?. 
byequiv => //;proc;inline*. 

(* Lets do everything up until the creation of BP.bb first *)
seq 34 34 : (={glob CP, glob A, glob C, glob P, glob Ev, glob G, glob HRO.ERO, glob Ve,
              BP.setHcheck, BP.secmapD, BP.setidents, BP.setD, BP.setH, BP.bb, BP.pk, BP.sk,
              BP.bb0, BP.bb1, BP.setchecked, BP.sethappy, BP.secmap, BP.pubmap, BP.vmap}). 
call(_: ={HRO.ERO.m, glob G, BP.secmap, BP.pubmap, BP.setH, BP.pk, glob Ev, BP.bb0, BP.bb1, BP.vmap}); [1..4: by sim].  
while ( ={i,  BP.setidents, BP.pk, BP.sk, glob CP, BP.secmap, BP.pubmap, BP.setD, BP.secmapD}); first sim. 
by auto. 
 
  wp. while (={i0, BP.setidents, glob HRO.ERO, tpk, pTr, pPk, pCo, tsk, pOp, trL, pi1, pi2}); first sim. 
wp. while(={glob CP, i0, BP.setidents, tpk, trL, pTr, pPk, pi2}); first sim. 
wp;rnd. while(={i0, BP.setidents, tpTr, tpk, pi2}); first sim. 
auto;call(_:true);auto;call(_:true). 
while (={w, glob HRO.ERO}); first by sim. 
auto;progress.

(* Now for the ifs *)   
if => //; first by rnd.

(* Dealing with everything up to the valid check *)
seq 8 8 : (
 ={glob CP, glob A, glob C, glob P, glob Ev, glob G, glob HRO.ERO, glob Ve,
      BP.setHcheck, BP.secmapD, BP.setidents, BP.setD, BP.setH, BP.bb, BP.pk,
      BP.sk, BP.bb0, BP.bb1, BP.setchecked, BP.sethappy, BP.secmap, valid,
      BP.pubmap, BP.vmap} /\
  ! ! (BP.setHcheck{1} \subset fdom BP.vmap{1})
). 
wp;while(={i1, e1, e2, e3, bb, BP.pubmap, glob C, glob HRO.ERO} /\ pd0{1} = pd{2}); first by sim.  
auto;progress.  

if => //; first rnd;skip;progress. 
swap{1} 9 -1.
(* Everything after the second valid check should be more or less straight forward *)
seq 23 18 : ((={glob CP, glob A, glob C, glob P, glob Ev, glob G, glob HRO.ERO, glob Ve,
       BP.setHcheck, BP.secmapD, BP.setidents, BP.setD, BP.setH, BP.bb, BP.r,
       BP.pk, BP.sk, BP.bb0, BP.bb1, BP.setchecked, BP.sethappy, BP.secmap,
       valid, BP.pubmap, BP.vmap, valid', BP.bbstar}  /\
   ! ! (BP.setHcheck{1} \subset fdom BP.vmap{1})) /\ (d{1} = da{2}) /\ pi{1} = BP.pi{2} /\
  ! !valid{1}); last first; first sim.  
wp;call(_: ={glob G}); first by sim. 
wp;call(_: ={BP.bb0, BP.bb1, glob HRO.ERO, glob G, BP.bb}); [proc;inline*;auto | sim | sim | trivial]. 
wp;call(_: ={glob G, glob HRO.ERO}); first sim. sim. 
wp.  call(_: ={glob G});first by sim. 
wp;rnd. 
while (={rL, glob Ev, glob HRO.ERO} /\ i2{1} = j{2} /\ BP.bb{2} = bb0{1} 
         /\ sd0{1} = BP.sk{2} /\ pd1{1} = BP.pk{2}); first by sim. 
auto;progress. 
qed. 


(*********************** We now move the tally and the valid check outside of the ifs **********************)
(*********************** to make it ready for the ZK part                             **********************)

module G0L(Ev:PKEvo.Scheme, P:Prover, Ve:Verifier, C:ValidIndS, CP:CommitmentProtocol,
                   A:DU_MB_BPRIV_adv, H:HOracle.Oracle, G:GOracle.Oracle) = {

  module O = DU_MB_BPRIV_oracles(Selene(Ev,P,Ve,C,CP),H,G,Left)
  module A = A(O)
  module Smv = Selene(Ev,P,Ve,C,CP,H,G)

  proc main() : bool = {
      var i;
      var id, upk, ct, d, da, vt;
      var valid, valid';
      var rL, j, b, ev, v, tr';
    
      BP.vmap       <- empty;
      BP.pubmap     <- empty;
      BP.secmap     <- empty;
      BP.secmapD    <- empty;
      BP.bb0        <- [];
      BP.bb1        <- [];
      BP.setchecked <- fset0;
      BP.sethappy   <- fset0;
      
      H.init();
      G.init();
      
      (* setup *)
      (BP.pk, BP.sk) <@ Smv.setup();

      (* register *)
      i <- 0;
      while (i < card BP.setidents) {
        id  <- nth witness (elems BP.setidents) i;
        d   <- oget BP.sk.`1.[id];
        upk <- oget BP.pk.`3.`4.[id];
        ct  <- oget BP.pk.`3.`5.[id];
        BP.secmap.[id] <- d;
        BP.pubmap.[id] <- (id, upk, ct);

        if (id \in BP.setD) {
          BP.secmapD.[id] <- oget BP.secmap.[id];
        }

        i <- i + 1;
      }

      (* adversary creates bulletin board *)
      BP.bb <@ A.create_bb(BP.pk, BP.secmapD, BP.pubmap, BP.setHcheck);

      (* is BP.bb valid? *)
      valid <@ Smv.validboard(BP.bb, BP.pk);

       (* We now tally *)
          rL <- [];

          j <- 0;
          while (j < size BP.bb) {
            
            b    <- nth witness BP.bb j;
            ev   <- b.`2;
            id   <- b.`1.`1;
            v    <@ Ev(H).dec(BP.sk.`2, id, ev);
            tr'  <@ ElGamal.dec(BP.sk.`3, oget BP.pk.`3.`3.[id]);

            rL  <- (oget v, oget tr') :: rL;

            j <- j + 1;
          }
          vt   <$ (duniform (allperms rL));
          BP.r <- (unzip1 vt, unzip2 vt);
          

      if (!(BP.setHcheck \subset fdom BP.vmap)) {
        BP.d <$ {0,1};
      } else {
        if (!valid) {
          BP.d <$ {0,1};
        } else {
          BP.pi <@ P(G).prove((BP.pk, sPublish BP.bb, BP.r), (BP.sk, BP.bb));
             da     <@ A.initial_guess();
          BP.bbstar <@ A.get_tally(BP.r, BP.pi);
          valid'    <@ Smv.verifytally((BP.pk, sPublish BP.bb, BP.bbstar.`1), BP.bbstar.`2);
          if (!valid') {
            BP.d <$ {0,1};
          } else {
            BP.d <@ A.final_guess();
          if (!(BP.setHcheck \subset BP.sethappy)) {
            BP.d <- da; 
          } 
          if (!(BP.setHcheck \subset BP.setchecked)) {
            BP.d <$ {0,1};
          }
         }
        }
      }
      return BP.d;
  }
}.

(***** We now prove that G0L' and G0L are equivalent *****)
local lemma G0L'_G0L_equiv &m : 
     BP.setidents{m} = BP.setH{m} `|` BP.setD{m} =>
    Pr[G0L'(Ev,P,Ve,C,CP,A,HRO.ERO,G).main() @ &m : res] = Pr[G0L(Ev,P,Ve,C,CP,A,HRO.ERO,G).main() @ &m : res]. 
proof. 
move => ?. 
byequiv => //;proc.  

(* The games are equivalent up to the point where the adversary creates BP.bb *)
seq 14 14 : (={glob CP, glob A, glob C, glob P, glob Ve, glob Ev, glob G,
               BP.setHcheck, BP.secmapD, BP.setD, BP.setidents, BP.setH, BP.pk, BP.sk, BP.vmap, BP.pubmap, BP.bb,
               BP.secmap, BP.bb0, BP.bb1, BP.setchecked, BP.sethappy, glob HRO.ERO}); first by sim. 

(* First case: !BP.setHcheck \subset fdom BP.vmap *)
case (!BP.setHcheck{1} \subset fdom BP.vmap{1}).
rcondt{1} 1;progress; rcondt{2} 7;progress.  
wp;rnd;while(0 <= j <= size BP.bb).
wp;call(_:true);auto. 
call(_:true);auto. progress => /#.  
inline*.  
wp; while(0 <= i0 <= size bb). 
wp.  
call(_:true);auto. 
auto;progress => /#. 
auto;progress.
rnd. 
wp;rnd{2}.
while{2} (0 <= j{2} <= size BP.bb{2}) (size BP.bb{2} - j{2}). 
progress. 
wp;call(Et_dec_ll).  
call(Ev_dec_ll HRO.ERO). 
proc;auto. 
auto;progress => /#.  
inline*. 
wp;while{2} (0 <= i0{2} <= size bb{2}) (size bb{2} - i0{2});progress. 
wp. 
call(C_vi_ll HRO.ERO); first proc;auto. 
auto;progress => /#.  
auto;progress. rewrite size_ge0. smt(). rewrite size_ge0. smt(). 
 apply duni_ap_ll. 

rcondf{1} 1;progress;rcondf{2} 7;progress. 
wp;rnd;while(0 <= j <= size BP.bb).
wp;call(_:true);auto. 
call(_:true);auto. progress => /#.  
inline*.  
wp; while(0 <= i0 <= size bb). 
wp. 
call(_:true);auto. 
auto;progress => /#. 
auto;progress.

(* The valid checks are equivalent *)
seq 1 1 : (={glob CP, glob A, glob C, glob P, glob Ve, glob Ev, glob G,
      BP.setHcheck, BP.secmapD, BP.setD, BP.setidents, BP.setH, BP.pk, BP.sk,
      BP.vmap, BP.pubmap, BP.secmap, BP.bb0, BP.bb1, BP.setchecked, BP.bb,
      BP.sethappy, HRO.ERO.m, valid} /\
  (BP.setHcheck{1} \subset fdom BP.vmap{1})).
inline*.
wp;while(={i0, e1, e2, e3, pd, bb, HRO.ERO.m, BP.pubmap, glob C}); first sim. 
auto;progress. 

(* Case on whether or not the board is valid *)
case (!valid{1}). 
rcondt{1} 1;progress. 
rcondt{2} 6;progress.   
wp;rnd;while(0 <= j <= size BP.bb). 
wp;call(_:true);auto. 
call(_:true);auto. 
progress => /#.  
auto;progress.
rnd.  
 
wp;rnd{2}. while{2} (0 <= j{2} <= size BP.bb{2}) (size BP.bb{2} - j{2}). 
progress. 
wp;call(Et_dec_ll). 
call(Ev_dec_ll HRO.ERO); first proc;auto. 
auto;progress => /#.  
auto;progress;first rewrite size_ge0. smt(). 
apply duni_ap_ll. 

rcondf{1} 1;progress;rcondf{2} 6;progress. 
wp;rnd;while(0 <= j <= size BP.bb).  
wp;call(_:true); first auto. 
call(_:true);auto;progress => /#. 
auto;progress.

(* The rest is completely equivalent *)
by sim. 
qed. 


(************ We now simulate the proof of correct tally, still in the left world *************)
local module G1L(Ev:PKEvo.Scheme, Ve:Verifier, C:ValidIndS, CP:CommitmentProtocol,
                   A:DU_MB_BPRIV_adv, H:HOracle.Oracle, S:Simulator) = {

  module O = DU_MB_BPRIV_oracles(Selene(Ev,P,Ve,C,CP),H,S,Left)
  module A = A(O)
  module Smv = Selene(Ev,P,Ve,C,CP,H,S)

  proc main() : bool = {
      var i;
      var id, upk, ct, d, da, vt;
      var valid, valid';
      var rL, j, b, ev, v, tr';

      BP.vmap       <- empty;
      BP.pubmap     <- empty;
      BP.secmap     <- empty;
      BP.secmapD    <- empty;
      BP.bb0        <- [];
      BP.bb1        <- [];
      BP.setchecked <- fset0;
      BP.sethappy   <- fset0;
      
      H.init();
      S.init();
      
      (* setup *)
      (BP.pk, BP.sk) <@ Smv.setup();

      (* register *)
      i <- 0;
      while (i < card BP.setidents) {
        id  <- nth witness (elems BP.setidents) i;
        d   <- oget BP.sk.`1.[id];
        upk <- oget BP.pk.`3.`4.[id];
        ct  <- oget BP.pk.`3.`5.[id];
        BP.secmap.[id] <-  d;
        BP.pubmap.[id] <- (id, upk, ct);

        if (id \in BP.setD) {
          BP.secmapD.[id] <- oget BP.secmap.[id];
        }

        i <- i + 1;
      }

      (* adversary creates bulletin board *)
      BP.bb <@ A.create_bb(BP.pk, BP.secmapD, BP.pubmap, BP.setHcheck);

      (* is BP.bb valid? *)
      valid <@ Smv.validboard(BP.bb, BP.pk);

       (* We now tally *)
          rL <- [];

          j <- 0;
          while (j < size BP.bb) {
            
            b    <- nth witness BP.bb j;
            ev   <- b.`2;
            id   <- b.`1.`1;
            v    <@ Ev(H).dec(BP.sk.`2, id, ev);
            tr'  <@ ElGamal.dec(BP.sk.`3, oget BP.pk.`3.`3.[id]);

            rL  <- (oget v, oget tr') :: rL;

            j <- j + 1;
          }
          vt   <$ (duniform (allperms rL));
          BP.r <- (unzip1 vt, unzip2 vt);
          

      if (!(BP.setHcheck \subset fdom BP.vmap)) {
        BP.d <$ {0,1};
      } else {
        if (!valid) {
          BP.d <$ {0,1};
        } else {
          BP.pi <@ S.prove((BP.pk, sPublish BP.bb, BP.r));
             da     <@ A.initial_guess();
          BP.bbstar <@ A.get_tally(BP.r, BP.pi);
          valid'    <@ Smv.verifytally((BP.pk, sPublish BP.bb, BP.bbstar.`1), BP.bbstar.`2);
          if (!valid') {
            BP.d <$ {0,1};
          } else {
            BP.d <@ A.final_guess();
            if (!(BP.setHcheck \subset BP.sethappy)) {
              BP.d <- da; 
            } 
            if (!(BP.setHcheck \subset BP.setchecked)) {
              BP.d <$ {0,1};
            }
          }
        }
      }
      return BP.d;
  }
}.

(***** Left game for ZK without checking the relation *****)
local module ZKFL(Ev:PKEvo.Scheme, R:VotingRelationS, P:Prover, A:VotingAdvZK, H:HOracle.Oracle, G:GOracle.Oracle) = {
    proc main() : bool = {
      var p;
      
      G.init();
      
      (BPS.s, BPS.w) <@ A(H,G).a1();
         BPS.rel     <@ R(Ev,H).main(BPS.s, BPS.w);
           p         <@ P(G).prove(BPS.s, BPS.w);
         BPS.p       <- Some p;
         BPS.b       <@ A(H,G).a2(BPS.p);

      return BPS.b;
      
    }
}.

(***** Right game for ZK without checking the relation *****)
local module ZKFR(Ev:PKEvo.Scheme, R:VotingRelationS, A:VotingAdvZK, H:HOracle.Oracle, S:Simulator) = {
    proc main() : bool = {
      var p;
      
      S.init();
      
      (BPS.s, BPS.w) <@ A(H,S).a1();
         BPS.rel     <@ R(Ev,H).main(BPS.s, BPS.w);
           p         <@ S.prove(BPS.s);
         BPS.p       <- Some p;
         BPS.b       <@ A(H,S).a2(BPS.p);

      return BPS.b;
      
    }
}.

(************************* Relate ZKFL to ZK_L from ProofSystem.ec **********************)
local lemma ZKFL_ZKL &m : 
     BP.setidents{m} = BP.setH{m} `|` BP.setD{m} =>
    `|Pr[ZKFL(Ev,R,P,BZK(Ev,P,C,Ve,A,CP),HRO.ERO,G).main() @ &m : res] -
      Pr[ZK_L(R(Ev,HRO.ERO),P,BZK(Ev,P,C,Ve,A,CP,HRO.ERO), G).main() @ &m : res]| <=
      Pr[ZK_L(R(Ev,HRO.ERO),P,BZK(Ev,P,C,Ve,A,CP,HRO.ERO), G).main() @ &m : !BPS.rel] .  
proof. 
move => ?. 
byequiv (_: ={glob A, glob C, glob CP, glob R, glob P, glob Ve, glob Ev, glob G, 
              BP.setHcheck, BP.secmapD, BP.pubmap, BP.secmap,
              BP.setD, BP.setidents, BP.d, BP.setH, BP.bb0, BP.bb1, 
              BP.r, BP.sethappy, glob HRO.ERO, BP.setchecked, BP.sk,
              BP.vmap, BP.pk, BP.bb} ==> 
              ={BPS.rel} /\ (BPS.rel{2} => ={res})) : (!BPS.rel) => //;last first. 
progress;apply H in H0. rewrite -H0 H1. 
rewrite H0 H1. 
proc. 
seq 3 3 : (
    ={glob P, glob R, glob HRO.ERO, glob G, glob A, glob Ev, glob C, glob CP, glob Ve, BPS.s, BPS.w, BPS.rel,
      BP.secmapD, BP.setD, BP.setidents, BP.setH, BP.bb0, BP.bb1, BP.setHcheck, BP.r, BP.d, BP.pubmap, BP.secmap, BP.sk,
      BP.sethappy, BP.setchecked, BP.vmap,BP.pk, BP.bb}
).
call(_: ={glob HRO.ERO, glob Ev}); first by sim.
call(_: ={glob HRO.ERO, glob G, glob A, glob Ev, glob CP, BP.secmapD, BP.setD, 
          BP.setidents, BP.pk, BP.bb, BP.pubmap, BP.setHcheck,
          BP.secmap, BP.setH, BP.bb0, BP.bb1, BP.r, BP.sethappy, 
          BP.setchecked, BP.vmap, BP.sk, BP.d}). sim.  
call(_:true). skip;progress.  
if{2} => //; first by sim. 
call{1} (BZK_a2_ll' HRO.ERO G P HRO.ERO_o_ll Go_ll); first apply (PS_p_ll G Go_ll). 
call{2} (BZK_a2_ll' HRO.ERO G P HRO.ERO_o_ll Go_ll); first apply (PS_p_ll G Go_ll). 
by wp; call{1} (PS_p_ll G Go_ll).
qed. 

(************************ Relate ZKFR to ZK_R from ProofSystem.ec ***********************)
local lemma ZKFR_ZKR &m : 
     BP.setidents{m} = BP.setH{m} `|` BP.setD{m} =>
    `|Pr[ZKFR(Ev,R,BZK(Ev,P,C,Ve,A,CP),HRO.ERO,S).main() @ &m : res] -
      Pr[ZK_R(R(Ev,HRO.ERO),S,BZK(Ev,P,C,Ve,A,CP,HRO.ERO)).main() @ &m : res]| <=
      Pr[ZK_R(R(Ev,HRO.ERO),S,BZK(Ev,P,C,Ve,A,CP,HRO.ERO)).main() @ &m : !BPS.rel] .  
proof. 
move => ?. 
byequiv (_: ={glob A, glob C, glob CP, glob R, glob S, glob Ve, glob Ev, 
              BP.setHcheck, BP.secmapD, BP.pubmap, BP.secmap,
              BP.setD, BP.setidents, BP.d, BP.setH, BP.bb0, BP.bb1, 
              BP.r, BP.sethappy, glob HRO.ERO, BP.setchecked, BP.sk,
              BP.vmap, BP.pk, BP.bb} ==> 
              ={BPS.rel} /\ (BPS.rel{2} => ={res})) : (!BPS.rel) => //;last first. 
progress;apply H in H0.   
rewrite -H0 H1. 
rewrite H0 H1. 

proc. 
seq 3 3 : (
    ={glob S, glob R, glob HRO.ERO, glob A, glob Ev, glob C, glob CP, glob Ve, BPS.s, BPS.w, BPS.rel, BP.sk,
      BP.secmapD, BP.setD, BP.setidents, BP.setH, BP.bb0, BP.bb1, BP.setHcheck, BP.r, BP.d, BP.pubmap, BP.secmap,
      BP.sethappy, BP.setchecked, BP.vmap,BP.pk, BP.bb}
).
call(_: ={glob HRO.ERO, glob Ev}); first by sim. 
call(_: ={glob HRO.ERO, glob S, glob A, glob Ev, glob CP, BP.secmapD, BP.setD, BP.setidents, BP.pk, BP.bb, BP.pubmap, BP.d,
          BP.secmap, BP.setH, BP.bb0, BP.bb1, BP.r, BP.sethappy, BP.setchecked, BP.vmap, BP.sk, BP.setHcheck}). sim. 
call(_:true). skip;progress. 
if{2} => //; first by sim. 
call{1} (BZK_a2_ll HRO.ERO S HRO.ERO_o_ll So_ll).  
call{2} (BZK_a2_ll HRO.ERO S HRO.ERO_o_ll So_ll). 
by wp; call{1} (Sp_ll).
qed. 

(*************** Lemma bounding the probability that the relation does not hold in ZK_L by ***************)
(***************     the probability of returning true in the VFR game.                    ***************)

local lemma ZKL_rel &m (H <: HOracle.Oracle { -A,  -BPS,  -BP,  -BS,  -Ve,  -Ev, -C, -R, -CP })
                       (G <: GOracle.Oracle { -A,  -BPS,  -BP,  -BS,  -Ve,  -Ev, -C, -R, -CP, -H })
                       (P <: Prover { -Ev,  -C,  -Ve,  -A,  -R,  -BPS,  -BP,  -BS,  -H,  -G,  -CP}) :
  BP.setidents{m} = BP.setH{m} `|` BP.setD{m} =>
  islossless H.o => islossless G.o => islossless P(G).prove =>
    Pr[ZK_L(R(Ev,H), P, BZK(Ev,P,C,Ve,A,CP,H), G).main() @ &m : !BPS.rel]
    <= Pr[VFRS(Ev, BVFR(Selene(Ev,P,Ve,C,CP), A, CP), R, CP, H, G).main() @ &m : res]. 
proof. 
move => ? Ho_ll Go_ll Pp_ll.
byequiv (_: ={glob A, glob Ev, glob P, glob CP, glob Ve, glob C, glob H, glob G, glob R, BP.setHcheck,
              BP.setidents, BP.setD, BP.secmapD, BP.setH, BP.bb0, BP.bb1} ==> _ ) => //.
proc. 
call{1} (BZK_a2_ll' H G P Ho_ll Go_ll Pp_ll). 
inline*. 
seq 39 40 : (BPS.rel{1} = rel{2}). 

  swap{1} [11..16] -10. swap{1} 16 -9. swap{2} [10..11] -3. swap{1} 33 -24. swap{1} 18 -9.
  swap{2} [25..30] -14.  swap{2} [30..31] -1. sp.
  call(_: ={glob H}). sim.
  wp;rnd.  
while (={j, rL, glob H, glob Ev} /\ BP.bb{1} = bb{2} /\ BP.sk{1}.`2 = vsk{2} 
         /\ BP.sk{1}.`3 = tsk{2} /\ BP.pk{1}.`3.`3 = pTr{2}). 
auto. call(_: ={glob H}); first by sim. auto;progress. 
 wp.  
call(_: ={BP.pk, BP.secmapD, BP.pubmap, BP.setH, BP.secmap, BP.bb0, BP.bb1,
          glob Ev, glob P, glob Ve, glob C, glob CP, glob H, glob G}); [1..4: by sim]. 
while (i{1} = i0{2} /\ ={BP.setidents, glob CP, BP.secmap, BP.pubmap, BP.setD, BP.secmapD, BP.sk, BP.pk}); first by sim. 
wp.  
while (={BP.setidents, tpk, pTr, pPk, pOp, pPk, tpTr, pCo, tsk, pi2} 
        /\ i0{1} = i{2} /\ trL{1} = trL{2}); first by sim;progress. 
wp. 
while (={BP.setidents, glob CP, pTr, tpk, trL, pOp, pPk, tpTr} /\ i0{1} = i{2}); first sim;progress.
wp;rnd. while(={BP.setidents, tpTr, tpk, pCo} /\ i0{1} = i{2}); first sim;progress. auto. 
call(_:true).
auto.  
call(_:true). call(_:true).   
auto;progress.
if{1}; last by auto. 
wp;call{1} (Pp_ll); first by trivial.
qed. 
 

(************** Lemma bounding ZKFL - ZK_L by VFR advantage ****************)

local lemma ZKFL_ZKL_VFR &m :
     BP.setidents{m} = BP.setH{m} `|` BP.setD{m} =>
    `|Pr[ZKFL(Ev,R,P,BZK(Ev,P,C,Ve,A,CP),HRO.ERO,G).main() @ &m : res] - 
      Pr[ZK_L(R(Ev,HRO.ERO),P,BZK(Ev,P,C,Ve,A,CP,HRO.ERO),G).main() @ &m : res]| <=
      Pr[VFRS(Ev,BVFR(Selene(Ev,P,Ve,C,CP),A,CP),R,CP,HRO.ERO,G).main() @ &m : res]. 
proof. 
move => id_union. 
have := ZKFL_ZKL &m. move => H0.  
have H1 : Pr[ZK_L(R(Ev,HRO.ERO),P,BZK(Ev,P,C,Ve,A,CP,HRO.ERO), G).main() @ &m : !BPS.rel] <= 
          Pr[VFRS(Ev,BVFR(Selene(Ev,P,Ve,C,CP),A,CP),R,CP,HRO.ERO,G).main() @ &m : res]. 
rewrite (ZKL_rel &m HRO.ERO G P id_union HRO.ERO_o_ll Go_ll (PS_p_ll G Go_ll)). 
smt().
qed. 

(*************** Lemma bounding the probability that the relation does not hold in ZK_R by ***************)
(***************     the probability of returning true in the VFR game.                    ***************)

local lemma ZKR_rel &m (H <: HOracle.Oracle { -A, -BPS, -BP, -BS, -Ve, -Ev, -C, -CP, -R})
                       (S <: Simulator { -Ev, -C, -CP, -Ve, -A, -R, -BPS, -BP, -BS, -H}) :
     BP.setidents{m} = BP.setH{m} `|` BP.setD{m} =>
     islossless H.o => islossless S.o => islossless S.prove =>
     Pr[ZK_R(R(Ev,H), S, BZK(Ev,P,C,Ve,A,CP,H)).main() @ &m : !BPS.rel] <=
     Pr[VFRS(Ev, BVFR(Selene(Ev,P,Ve,C,CP),A,CP), R, CP, H, S).main() @ &m : res]. 
proof. 
move => ? Ho_ll So_ll Sp_ll.
byequiv (_: ={glob A, glob Ev, glob S, glob CP, glob Ve, glob C, glob H, glob R, BP.setHcheck,
              BP.setidents, BP.setD, BP.secmapD, BP.setH, BP.bb0, BP.bb1} ==> _ ) => //.
proc. 
call{1} (BZK_a2_ll H S Ho_ll So_ll). 
inline*. 
seq 39 40 : (BPS.rel{1} = rel{2}). 

swap{1} [11..16] -10. swap{1} 16 -9. swap{2} [9..10] -2. swap{2} [25..30] -14. swap{1} 33 -14. 
call(_: ={glob H}); first by sim. 
wp;rnd.   
while (={j, rL, glob H, glob Ev} /\ BP.bb{1} = bb{2} /\ BP.sk{1}.`2 = vsk{2} 
         /\ BP.sk{1}.`3 = tsk{2} /\ BP.pk{1}.`3.`3 = pTr{2}). 
auto. call(_: ={glob H}); first by sim. auto;progress. 
 wp.  
call(_: ={BP.pk, BP.secmapD, BP.pubmap, BP.setH, BP.secmap, BP.bb0, BP.bb1,
          glob Ev, glob Ve, glob C, glob CP, glob H, glob S}); [1..4: by sim]. 
while (i{1} = i0{2} /\ ={BP.setidents, glob CP, BP.secmap, 
       BP.pubmap, BP.setD, BP.secmapD, BP.sk, BP.pk}); first by sim. 
wp.  
while (={BP.setidents, tpk, pTr, pPk, pOp, pPk, tpTr, pCo, tsk, pi2} 
       /\ i0{1} = i{2} /\ trL{1} = trL{2}); first by sim;progress. 
wp. 
while (={BP.setidents, glob CP, pTr, tpk, trL, pOp, pPk, tpTr} /\ i0{1} = i{2}); first sim;progress.
wp;rnd. while(={BP.setidents, tpTr, tpk, pCo} /\ i0{1} = i{2}); first sim;progress. auto. 
call(_:true).
auto.  
call(_:true). swap{2} 8 8.  call(_:true).   
auto;progress. 
if{1}; last by auto. 
wp;call{1} (Sp_ll); first by trivial.
qed. 

(************** Lemma bounding ZKFR - ZK_R by VFR advantage ****************)

local lemma ZKFR_ZKR_VFR &m :
     BP.setidents{m} = BP.setH{m} `|` BP.setD{m} =>
    `|Pr[ZKFR(Ev,R,BZK(Ev,P,C,Ve,A,CP),HRO.ERO,S).main() @ &m : res] - 
      Pr[ZK_R(R(Ev,HRO.ERO),S,BZK(Ev,P,C,Ve,A,CP,HRO.ERO)  ).main() @ &m : res]| <=
      Pr[VFRS(Ev,BVFR(Selene(Ev,P,Ve,C,CP),A,CP),R,CP,HRO.ERO,S).main() @ &m : res]. 
proof. 
move => id_union.
have := ZKFR_ZKR &m. move => H0.  
have H1 : Pr[ZK_R(R(Ev,HRO.ERO),S,BZK(Ev,P,C,Ve,A,CP,HRO.ERO)  ).main() @ &m : !BPS.rel] <= 
          Pr[VFRS(Ev,BVFR(Selene(Ev,P,Ve,C,CP),A,CP),R,CP,HRO.ERO,S).main() @ &m : res]. 
rewrite (ZKR_rel &m HRO.ERO S id_union HRO.ERO_o_ll So_ll Sp_ll). 
smt().
qed. 


(*********** Lemma proving that G0L and ZKFL(BZK) are equivalent *************)
local lemma G0L_ZKFL_equiv &m :
     BP.setidents{m} = BP.setH{m} `|` BP.setD{m} =>
    Pr[G0L(Ev,P,Ve,C,CP,A,HRO.ERO,G).main() @ &m : res] =
    Pr[ZKFL(Ev,R,P,BZK(Ev,P,C,Ve,A,CP),HRO.ERO,G).main() @ &m : res]. 
proof. 
move => ?. 
byequiv => //. 
proc;inline*. 
wp. swap{1} 12 -11. 

(* Everything up to creating BP.bb *)
seq 34 34 : (
  ={glob HRO.ERO, glob A, glob C, glob CP, glob P, glob Ve, glob Ev, glob G,
    BP.setHcheck, BP.secmapD, BP.setD, BP.setidents, BP.setH, BP.bb0, BP.bb1, BP.bb,
    BP.sethappy, BP.vmap, BP.pk, BP.sk, BP.setchecked, BP.secmap, BP.pubmap}
); first by sim. 
swap{2} [11..18] -10. 

(** Everything that happens before the ifs **)
seq 13 14 : (
  ={BP.setHcheck, BP.vmap, valid, BP.setchecked, BP.sethappy, BP.bb0, BP.bb1, 
    BP.r, BP.bb, BP.secmap, BP.pubmap, BP.pk, BP.sk, BP.setidents, vt,
    glob HRO.ERO, glob A, glob G, glob Ev, glob P, glob Ve, glob C, glob CP, valid} 
    /\ (BPS.s{2} = (BP.pk{2}, sPublish BP.bb{2}, BP.r{2}))
    /\ (BPS.w{2} = (BP.sk{2}, BP.bb{2}))
). 
wp.
rnd. while( ={j, BP.bb, glob Ev, rL, glob HRO.ERO, BP.pk, BP.sk}); first by sim.  
auto. 
while(={i1, e1, e2, e3, glob C, glob HRO.ERO, BP.pubmap, pd, bb}); first by sim. 
auto;progress.  

(**** Case: setHcheck subset of fdom vmap?? ****)
case(!(BP.setHcheck{1} \subset fdom BP.vmap{1})). 
rcondt{1} 1;progress. 
rcondt{2} 5;progress. 
wp;call(_:true). auto. 
call(_:true). auto.  auto.  
auto;progress. 
call{2} (PS_p_ll G Go_ll). call{2} R_m_ll. 
auto;progress. 

rcondf{1} 1;progress. 
rcondf{2} 5;progress. 
wp;call(_:true); first by auto. 
call(_:true); auto. 

(**** Case: bb valid ??? ****)
case (!valid{1}). 
rcondt{1} 1;progress. 
rcondt{2} 5;progress. 
wp;call(_:true); first by auto. 
call(_:true); auto.  
auto;progress. 
call{2}(PS_p_ll G Go_ll). 
call{2} R_m_ll. 
auto;progress. 

rcondf{1} 1;progress. 
rcondf{2} 5;progress. 
wp;call(_:true); first by auto. 
call(_:true); auto. 
auto;progress.  
sim. 

call(_: ={glob HRO.ERO, glob G, BP.bb0, BP.bb1}); [1..3: by sim].  

call(_: ={glob G, glob HRO.ERO}); [1..2: by sim].  
auto;progress. 
wp;call(_: ={glob G}); first sim.  
call{2} (R_m_ll). 
auto;progress. 
qed. 

(************ Lemma proving that G1L and ZKFR(BZK) are equivalent ***********)
local lemma G1L_ZKFR_equiv &m : 
     BP.setidents{m} = BP.setH{m} `|` BP.setD{m} =>
    Pr[G1L(Ev,Ve,C,CP,A,HRO.ERO,S).main() @ &m : res] = 
    Pr[ZKFR(Ev,R,BZK(Ev,P,C,Ve,A,CP),HRO.ERO,S).main() @ &m : res]. 
proof. 
move => ?. 
byequiv => //. 
proc;inline*. 
wp. swap{1} 12 -11. 

(* Everything up to creating BP.bb *)
seq 34 34 : (
  ={glob HRO.ERO, glob A, glob C, glob CP, glob Ve, glob Ev, glob S,
    BP.setHcheck, BP.secmapD, BP.setD, BP.setidents, BP.setH, BP.bb0, BP.bb1, BP.bb,
    BP.sethappy, BP.vmap, BP.pk, BP.sk, BP.setchecked, BP.secmap, BP.pubmap}
); first by sim. 
swap{2} [11..18] -10. 

seq 13 14 : (
  ={BP.setHcheck, BP.vmap, valid, BP.setchecked, BP.sethappy, BP.bb0, BP.bb1, 
    BP.r, BP.bb, BP.secmap, BP.pubmap, BP.pk, BP.sk, BP.setidents, vt,
    glob HRO.ERO, glob A, glob S, glob Ev, glob Ve, glob C, glob CP, valid} 
    /\ (BPS.s{2} = (BP.pk{2}, sPublish BP.bb{2}, BP.r{2}))
    /\ (BPS.w{2} = (BP.sk{2}, BP.bb{2}))
). 
wp.
rnd. while( ={j, BP.bb, glob Ev, rL, glob HRO.ERO, BP.pk, BP.sk}); first by sim.  
auto. 
while(={i1, e1, e2, e3, glob C, glob HRO.ERO, BP.pubmap, pd, bb}); first by sim. 
auto;progress. 

(**** Case: setHcheck subset of fdom vmap?? ****)
case(!(BP.setHcheck{1} \subset fdom BP.vmap{1})). 
rcondt{1} 1;progress. 
rcondt{2} 5;progress. 
wp;call(_:true);auto. 
call(_:true); auto.   
auto;progress. 
call{2} (Sp_ll). call{2} R_m_ll. 
auto;progress. 

rcondf{1} 1;progress. 
rcondf{2} 5;progress. 
wp;call(_:true). 
call(_:true); auto.  
auto;progress. 

(**** Case: bb valid ??? ****)
case (!valid{1}). 
rcondt{1} 1;progress. 
rcondt{2} 5;progress. 
wp;call(_:true). 
call(_:true); auto.  
auto;progress. 
call{2} Sp_ll. 
call{2} R_m_ll. 
auto;progress. 

rcondf{1} 1;progress. 
rcondf{2} 5;progress. 
wp;call(_:true).  
call(_:true); auto. 
auto;progress. sim. 

call(_: ={glob HRO.ERO, glob S, BP.bb0, BP.bb1}); [1..3: by sim].  

call(_: ={glob S, glob HRO.ERO}); [1..2: by sim].  
auto;progress. 
wp;call(_: true).   
call{2} (R_m_ll). 
auto;progress. 
qed. 
 

(****** Lemma proving that |G0L - G1L| is bounded by |ZK_L - ZK_R| + 2 * VFR ********)
local lemma G0L_G1L_zk_vfr &m : 
  BP.setidents{m} = BP.setH{m} `|` BP.setD{m} =>
    `|Pr[G0L(Ev,P,Ve,C,CP,A,HRO.ERO,G).main() @ &m : res]
      - Pr[G1L(Ev,Ve,C,CP,A,HRO.ERO,S).main() @ &m : res]| 
      <= 
        Pr[VFRS(Ev,BVFR(Selene(Ev,P,Ve,C,CP),A,CP),R,CP,HRO.ERO,G).main() @ &m : res]
      + Pr[VFRS(Ev,BVFR(Selene(Ev,P,Ve,C,CP),A,CP),R,CP,HRO.ERO,S).main() @ &m : res]
     + `|Pr[ZK_L(R(Ev,HRO.ERO),P,BZK(Ev,P,C,Ve,A,CP,HRO.ERO),G).main() @ &m : res]
         - Pr[ZK_R(R(Ev,HRO.ERO),S,BZK(Ev,P,C,Ve,A,CP,HRO.ERO)).main() @ &m : res]|.
proof. 
move => id_union. 
rewrite (G0L_ZKFL_equiv &m id_union) (G1L_ZKFR_equiv &m id_union). 
have H0 : forall (x y z w : real), `|x-y| <= `|x-z| + `|z-w| + `|w-y|  by smt(). 
have H1 := H0 Pr[ZKFL(Ev, R, P, BZK(Ev, P, C, Ve, A, CP), HRO.ERO, G).main() @ &m : res]
              Pr[ZKFR(Ev, R, BZK(Ev, P, C, Ve, A, CP), HRO.ERO, S).main() @ &m : res]
              Pr[ZK_L(R(Ev, HRO.ERO), P, BZK(Ev, P, C, Ve, A, CP, HRO.ERO), G).main() @ &m : res]
              Pr[ZK_R(R(Ev, HRO.ERO), S, BZK(Ev, P, C, Ve, A, CP, HRO.ERO)).main() @ &m : res]. 
have H2 := (ZKFL_ZKL_VFR &m). 
have H3 := (ZKFR_ZKR_VFR &m). 
smt(). 
qed. 

(****************************************************************************************************)
(************************************** End of ZK part **********************************************)
(****************************************************************************************************)

(****************************************************************************************************)
(***** Stop decrypting honest ciphertexts, use v0 value from BP.vmap instead.                   *****)
(***** Decrypt ciphertexts created by adversary as usual. Also reduce to a single board.        *****)
(***** We remove one of the boards to make it ready for a reduction to IND1CCA security.        *****)
(****************************************************************************************************)

local module G2L (Ev:PKEvo.Scheme, Ve:Verifier, C:ValidIndS, CP:CommitmentProtocol, 
                  A:DU_MB_BPRIV_adv, H:HOracle.Oracle, S:Simulator) = {

  var bb : (ident * (ident * upkey * commitment) * cipher) list

  module Smv = Selene(Ev,P,Ve,C,CP,H,S)

  module O = {
    proc h = H.o
    proc g = S.o

    proc vote_core(id, v, sl) = {
    var p, b, spr, spo;  

      (p, b, spr, spo) <@ Smv.vote(BP.pk, id, oget BP.pubmap.[id], sl, v);
    
      return (p, b, spr, spo);

    }

    proc vote(id:ident, v0 v1 : vote) = {
      var p, b, spr, spo;
  
      if (id \in BP.setH) {
        (p, b, spr, spo) <@ vote_core(id, v0, oget BP.secmap.[id]);

        BP.vmap.[id] <- (b, spr, spo, v0) :: (odflt [] BP.vmap.[id]);

        bb <- (id, oget BP.pubmap.[id], b) :: bb; 
      }
    }

    proc verify(id:ident) : ident fset = {
      var ok, sv;
      if (id \in BP.setidents){
        BP.setchecked <- BP.setchecked `|` (fset1 id);
        sv <- odflt [] (BP.vmap.[id]);
        ok <@ Smv.verifyvote(id, (oget (ohead sv)).`2, (oget (ohead sv)).`3, BP.bb, BP.bbstar, 
                                  oget BP.pubmap.[id], oget BP.secmap.[id]);
        if (ok) {
          BP.sethappy <- BP.sethappy `|` (fset1 id);
        }
      }
      return BP.sethappy;
    }

    proc board()  = {
      return sPublish (rem_ids bb);
    }

  }
  
  module A = A(O)

  proc main() : bool = {
      var i;
      var id, upk, ct, d, da, vt;
      var valid, valid';
      var rL, j, b, ev, v, tr';
      var sv, k;

      BP.vmap       <- empty;
      BP.pubmap     <- empty;
      BP.secmap     <- empty;
      BP.secmapD    <- empty;
      G2L.bb        <- [];
      BP.setchecked <- fset0;
      BP.sethappy   <- fset0;
      
      H.init();
      S.init();
      
      (* setup *)
      (BP.pk, BP.sk) <@ Smv.setup();

      (* register *)
      i <- 0;
      while (i < card BP.setidents) {
        id  <- nth witness (elems BP.setidents) i;
        d   <- oget BP.sk.`1.[id];
        upk <- oget BP.pk.`3.`4.[id];
        ct  <- oget BP.pk.`3.`5.[id];
        BP.secmap.[id] <-  d;
        BP.pubmap.[id] <- (id, upk, ct);

        if (id \in BP.setD) {
          BP.secmapD.[id] <- oget BP.secmap.[id];
        }

        i <- i + 1;
      }

      (* adversary creates bulletin board *)
      BP.bb <@ A.create_bb(BP.pk, BP.secmapD, BP.pubmap, BP.setHcheck);

      (* is BP.bb valid? *)
      valid <@ Smv.validboard(BP.bb, BP.pk);

       (* We now tally *)
          rL <- [];

          j <- 0;
          while (j < size BP.bb) {
            
            b    <- nth witness BP.bb j;
            ev   <- b.`2;
            id   <- b.`1.`1;
            if ( (id, oget BP.pubmap.[id], ev) \in  bb) {
              (* Get the vote from BP.vmap that mathes the ballot *)
              sv <- odflt [] BP.vmap.[id]; (* get list for voter id *)
              k  <- find (fun (x:cipher*cipher*vote*vote) => x.`1 = ev) sv; (* first index where b appears *)
              v  <- Some (oget (onth sv k)).`4; (* the vote at that index *)
            } else {
              v    <@ Ev(H).dec(BP.sk.`2, id, ev);
            }

            tr'  <@ ElGamal.dec(BP.sk.`3, oget BP.pk.`3.`3.[id]);

            rL  <- (oget v, oget tr') :: rL;

            j <- j + 1;
          }
          vt   <$ (duniform (allperms rL));
          BP.r <- (unzip1 vt, unzip2 vt);

      if (!(BP.setHcheck \subset fdom BP.vmap)) {
        BP.d <$ {0,1};
      } else {
        if (!valid) {
          BP.d <$ {0,1};
        } else {
           BP.pi <@ S.prove((BP.pk, sPublish BP.bb, BP.r));
             da     <@ A.initial_guess();
          BP.bbstar <@ A.get_tally(BP.r, BP.pi);
          valid'    <@ Smv.verifytally((BP.pk, sPublish BP.bb, BP.bbstar.`1), BP.bbstar.`2);
          if (!valid') {
            BP.d <$ {0,1};
          } else {
            BP.d <@ A.final_guess();
            if (!(BP.setHcheck \subset BP.sethappy)) {
              BP.d <- da; 
            } 
            if (!(BP.setHcheck \subset BP.setchecked)) {
              BP.d <$ {0,1};
            }
          }
        }
      }
    return BP.d;
  }
}.

(*** Prove that G1L is equivalent to G2L ***)
 
local lemma G1L_G2L_equiv &m : 
     BP.setidents{m} = BP.setH{m} `|` BP.setD{m} =>
    Pr[G1L(Ev,Ve,C,CP,A,HRO.ERO,S).main() @ &m : res] = Pr[G2L(Ev,Ve,C,CP,A,HRO.ERO,S).main() @ &m : res]. 
proof. 
move => ?. 
byequiv (_: ={glob A, glob C, glob CP, glob Ve, glob S, glob Ev, BP.setHcheck, BP.secmapD, BP.setD,
              BP.setidents, BP.setH} ==> _) => //.
proc. 

(******** Everything up until the adversary creates BP.bb is more or less equivalent **********)
seq 14 13 : (
  ={glob A, glob C, glob CP, glob Ve, glob S, glob Ev, glob HRO.ERO, 
    BP.setHcheck, BP.secmapD, BP.setD, BP.setidents, BP.setH, BP.vmap, 
    BP.pk, BP.sk, BP.bb, BP.sethappy, BP.setchecked, BP.pubmap, BP.secmap}
    /\  ( BP.bb0{1} = G2L.bb{2})

    /\ (forall (id:ident) (pc:ident*upkey*commitment) (c:cipher), (id, pc, c) \in G2L.bb{2}  =>  
            Some (oget (onth (odflt [] BP.vmap{2}.[id]) (find (fun (x : cipher*cipher*vote*vote) => x.`1 = c) 
                                               (odflt [] BP.vmap{2}.[id])))).`4
             = dec_cipher_vo BP.sk{2}.`2 id c HRO.ERO.m{2})

    /\ (forall (id:ident) pc (c:cipher), (id, pc, c) \in G2L.bb{2} => 
                                          (pc, c) \in rem_ids G2L.bb{2})

    /\ (forall (id:ident) (c:cipher) pc, 
                 (id, pc, c) \in ( BP.bb0{1}) => 
                    is_some BP.vmap{1}.[id])

    /\ (forall id pc c, (id, pc, c) \in G2L.bb{2} => pc = oget BP.pubmap{2}.[id])
).

call(_: ={glob HRO.ERO, glob S, glob C, glob CP, glob Ev, BP.pk, BP.secmapD, BP.pubmap, BP.sk,
          BP.secmap, BP.setH, BP.setidents, BP.vmap} /\ (BP.bb0{1} = G2L.bb{2})
         /\ (BP.pk{1}.`1 = get_epk BP.sk{1}.`2)

         /\ (forall (id:ident) (c:cipher) pc, (id, pc ,c) \in G2L.bb{2} => 
            Some (oget (onth (odflt [] BP.vmap{2}.[id]) 
           (find (fun (x : cipher*cipher*vote*vote) => x.`1 = c) (odflt [] BP.vmap{2}.[id])))).`4
             = dec_cipher_vo BP.sk{2}.`2 id c HRO.ERO.m{2})

         /\ (forall (id:ident) (c:cipher) pc, 
                 (id, pc, c) \in ( BP.bb0{1}) => 
                    is_some BP.vmap{1}.[id])

         /\ (forall id pc c, (id, pc, c) \in G2L.bb{2} => pc = oget BP.pubmap{2}.[id])
).

proc. 
inline*. 
if => //. 
seq 13 9 : (
  ={id, v0, v1, id1, ev,id0, HRO.ERO.m, glob S, glob C, 
     glob CP, glob Ev, BP.pk, BP.secmapD, BP.pubmap, BP.sk, 
     BP.secmap, BP.setH, BP.setidents, BP.vmap}
    /\ v2{2} = v0{2} /\ v{1} = v0{2} /\ pc{1} = oget BP.pubmap{1}.[id{1}]

    /\ Some v0{2} = dec_cipher_vo BP.sk{2}.`2 id{2} ev{2} HRO.ERO.m{2}

   /\ (BP.bb0{1} = G2L.bb{2})

   /\ (BP.pk{1}.`1 = get_epk BP.sk{2}.`2)

  /\ (forall (id3 : ident) (c : cipher) pc,
      (id3, pc, c) \in G2L.bb{2} =>
      Some
        (oget
           (onth (odflt [] BP.vmap{2}.[id3])
              (find (fun (x : cipher * cipher * vote * vote) => x.`1 = c)
                 (odflt [] BP.vmap{2}.[id3])))).`4 =
      dec_cipher_vo BP.sk{2}.`2 id3 c HRO.ERO.m{2}) 

  /\ (forall (id3 : ident) (c : cipher) pc,
     (id3, pc, c) \in BP.bb0{1} =>
     is_some BP.vmap{1}.[id3])

 /\ (id{1} \in BP.setH{1})   

   /\ (forall id pc c, (id, pc, c) \in G2L.bb{2} => pc = oget BP.pubmap{2}.[id])
).

sp. 
exists* BP.sk{1}, BP.pk{1}, v{1}, id1{1}; elim* => sk1 pk1 v1 id1. 
pose kp := pk1.`1 = get_epk sk1.`2. 
have em_kp : kp \/ !kp by exact/orbN. 
elim em_kp. progress. 
call (Eenc_dec_vo sk1.`2 pk1.`1 id1 v1);auto;progress.  
move => h. 
conseq (_: _ ==> !(pk1.`1 = get_epk sk1.`2));progress. 
call{1} (Ev_enc_ll HRO.ERO HRO.ERO_o_ll). call{2} (Ev_enc_ll HRO.ERO HRO.ERO_o_ll). 
auto;progress. 
auto;progress. 
exists* (glob Ev){1}; elim* => gev. 
call{1} (Ev_e_eq gev). 
auto;progress. 
  
case (id3 = id{2}) => ideq. 
rewrite ideq.  
rewrite get_set_eqE. trivial. simplify. 

case (ev{2} = c) => ceq. simplify. by rewrite H -ideq ceq. 
 
have H10 : !(find (fun (x : cipher * cipher * vote * vote) => x.`1 = c) (odflt [] BP.vmap{2}.[id3]) + 1 = 0). 
have ? : 0 <= (find (fun (x:cipher*cipher*vote*vote) => x.`1 = c) (odflt [] BP.vmap{2}.[id3])) by rewrite find_ge0. 
rewrite addz1_neq0 => //.   
rewrite -ideq H10. simplify. 
have H11 : (id3, pc1, c) \in (G2L.bb{2}) by smt().    
apply H1 in H11; first smt(). 
  
rewrite get_set_neqE.  rewrite ideq => />.  
have H10 : (id3, pc1, c) \in (G2L.bb{2}) by smt(). 
apply H1 in H10.  rewrite H10 => />.
  
case(id3 = id{2}) => ideq. 
rewrite get_set_eqE. trivial. trivial.
rewrite get_set_neqE.  trivial. rewrite (H2 id3 c pc1). smt(). 

smt(@SmtMap).  

proc;inline*;auto.  
proc;auto. 
by conseq So_ll2.

(*** Registration is equivalent ***)   
while (={i, BP.setidents, glob CP, BP.secmap, BP.pubmap, BP.setD, BP.secmapD, BP.pk, BP.sk, BP.setH} 
).
auto. wp. 
inline*.
wp;while(={BP.setidents, i0, pPk, pTr, pCo, pOp, tsk, tpk, trL, pi2}); first sim.
wp;while(={i0, BP.setidents, trL, pTr, glob CP, pPk, tpk}); first sim. 
wp;rnd;while(={i0, BP.setidents, tpk, tpTr, trL}); first sim. 
wp;rnd;call Ev_kgen_get_epk.
auto;call(_:true). 
while (={w, glob HRO.ERO}); first by sim.
auto;progress. rewrite (H13 id1 c3 pc). apply H16. trivial. rewrite (in_rem_ids id1 pc c3) => />. 
  
(**** The ifs are equivalent ***)
seq 6 6 : (
  ={glob HRO.ERO, glob Ev, glob S, glob Ve, glob A, glob CP, BP.setHcheck, 
    BP.vmap, BP.pk, BP.sk, BP.bb, BP.setchecked, BP.setidents, vt,
    BP.r, BP.sethappy, BP.pubmap, BP.secmap, BP.vmap, valid}
  /\ (BP.bb0{1} = G2L.bb{2})
); last first. 
if => //; first rnd;progress.
if => //; first rnd;progress.  

seq 4 4 : (
    (={glob HRO.ERO, glob Ev, glob S, glob Ve, glob A, glob CP, BP.setHcheck, 
      BP.bbstar, BP.r, BP.pubmap, BP.secmap, BP.vmap, BP.setidents, 
       BP.vmap, BP.pk, BP.sk, BP.pi, BP.bb, BP.setchecked, BP.sethappy, valid, valid', da, BP.pi} /\
   ! ! (BP.setHcheck{1} \subset fdom BP.vmap{1})) /\
  ! !valid{1}
  /\ (BP.bb0{1} = G2L.bb{2})
).
inline*. 
wp. call(_: ={glob S}). conseq So_ll2. 
wp. call(_: ={glob HRO.ERO, glob S} /\ BP.bb0{1} = G2L.bb{2}); [proc;inline*;auto | sim | sim | auto;progress]. 
call(_: ={glob HRO.ERO, glob S}); [1..2:by sim].  
call(_:true). 
auto;progress. 
if => //; first rnd;progress. 
seq 1 1 : (((={glob HRO.ERO, glob Ev, glob S, glob Ve, glob A, glob CP, BP.setHcheck, 
        BP.pubmap, BP.secmap, BP.vmap, BP.setidents,
        BP.bbstar, BP.r, BP.vmap, BP.pk, BP.sk, BP.pi, BP.bb, BP.setchecked, BP.d,
        BP.sethappy, valid, valid', da} /\
    ! ! (BP.setHcheck{1} \subset fdom BP.vmap{1})) /\
   ! !valid{1} /\ BP.bb0{1} = G2L.bb{2}) /\
  ! !valid'{1}
).

call(_: ={BP.bb, BP.bbstar, BP.pubmap, BP.secmap, BP.vmap, glob CP, glob HRO.ERO, 
         glob S, BP.setchecked, BP.sethappy, BP.setidents}); [1..3: by sim]. 
auto;progress. 
if => //;sp. if => //;first rnd;progress. 
if => //; first rnd;progress.  

(***** We now tally *****)
wp;rnd. 

while (={j, BP.bb, glob HRO.ERO, glob Ev, BP.vmap, rL, BP.sk, BP.pk, BP.pubmap}
  /\ (forall (id0 : ident) (c : cipher),
    (id0, oget BP.pubmap{2}.[id0], c) \in G2L.bb{2} =>
    Some
      (oget
         (onth (odflt [] BP.vmap{2}.[id0])
            (find (fun (x : cipher * cipher * vote * vote) => x.`1 = c)
               (odflt [] BP.vmap{2}.[id0])))).`4 =
    dec_cipher_vo BP.sk{2}.`2 id0 c HRO.ERO.m{2})

  /\  (forall (id0 : ident) (c : cipher) pc,
    (id0, pc, c) \in G2L.bb{2} =>
    (pc, c) \in rem_ids G2L.bb{2})

  /\ (forall (id3 : ident) (c : cipher) pc,
     (id3, pc, c) \in G2L.bb{2} =>
     is_some BP.vmap{1}.[id3])

   /\ (forall id pc c, (id, pc, c) \in G2L.bb{2} => pc = oget BP.pubmap{2}.[id])
).

wp;sp. 
if{2}; last first. 

call(_:true);first auto. 
exists* (glob Ev){1}, BP.sk{1}, id{1}, ev{1}. elim* => gev sk id ev. 
call(Edec_Odec_eq_vo sk.`2 id ev). auto;progress. 


call(_:true); first auto. 
exists* (glob Ev){1}, BP.sk{1}, id{1}, ev{1}. elim* => gev sk id ev. 
call{1} (Edec_Odec_vo gev sk.`2 id ev). 
auto;progress. 

have ? : is_some BP.vmap{2}.[(nth witness BP.bb{2} j{2}).`1.`1]. 
rewrite (H1 (nth witness BP.bb{2} j{2}).`1.`1 (nth witness BP.bb{2} j{2}).`2 
        (oget BP.pubmap{2}.[(nth witness BP.bb{2} j{2}).`1.`1])) => />. 

have H6 : Some (oget
   (onth (odflt [] BP.vmap{2}.[(nth witness BP.bb{2} j{2}).`1.`1])
      (find
         (fun (x : cipher * cipher * vote * vote) =>
            x.`1 = (nth witness BP.bb{2} j{2}).`2)
         (odflt [] BP.vmap{2}.[(nth witness BP.bb{2} j{2}).`1.`1])))).`4 =  
          dec_cipher_vo BP.sk{2}.`2 (nth witness BP.bb{2} j{2}).`1.`1 (nth witness BP.bb{2} j{2}).`2 HRO.ERO.m{2}.  
rewrite (H (nth witness BP.bb{2} j{2}).`1.`1 (nth witness BP.bb{2} j{2}).`2 ) => />. 
rewrite -H6; first trivial. 

inline*. wp. 
while (={i0, bb, e1, e2, e3, glob HRO.ERO, glob C, pd, BP.pubmap}). sim;progress. 
auto;progress. rewrite (H id00 (oget BP.pubmap{2}.[id00]) c) => />. 
by rewrite (in_rem_ids id00 pc c).   
qed. 


(****************************************************************************************************)
(****************************** Here come the games starting from the right *************************)
(****************************************************************************************************)

(*** We start by unpacking some procedures from the security game ***)
local module G0R' (Ev:PKEvo.Scheme, P:Prover, Ve:Verifier, C:ValidIndS, CP:CommitmentProtocol,
                   A:DU_MB_BPRIV_adv, H:HOracle.Oracle, G:GOracle.Oracle, S:Simulator) = {

    module O   = DU_MB_BPRIV_oracles(Selene(Ev,P,Ve,C,CP), H, S, Right)
    module A   = A(O)
    module Smv = Selene(Ev,P,Ve,C,CP,H,S)

    proc main() : bool = {
      var i;
      var id, upk, ct, d, da, vt;
      var valid, valid';
      var rL, j, b, ev, v, tr';

      BP.vmap       <- empty;
      BP.pubmap     <- empty;
      BP.secmap     <- empty;
      BP.secmapD    <- empty;
      BP.bb0        <- [];
      BP.bb1        <- [];
      BP.setchecked <- fset0;
      BP.sethappy   <- fset0;
      
      H.init();
      G.init();
      S.init();
      
      (* setup *)
      (BP.pk, BP.sk) <@ Smv.setup();

      (* register *)
      i <- 0;
      while (i < card BP.setidents) {
        id  <- nth witness (elems BP.setidents) i;
         d  <- oget BP.sk.`1.[id];
        upk <- oget BP.pk.`3.`4.[id];
        ct  <- oget BP.pk.`3.`5.[id];
        BP.secmap.[id] <-  d;
        BP.pubmap.[id] <- (id, upk, ct);

        if (id \in BP.setD) {
          BP.secmapD.[id] <- oget BP.secmap.[id];
        }

        i <- i + 1;
      }

      (* adversary creates bulletin board *)
      BP.bb <@ A.create_bb(BP.pk, BP.secmapD, BP.pubmap, BP.setHcheck);

      if (!(BP.setHcheck \subset fdom BP.vmap)) {
        BP.d <$ {0,1};
      } else {
        valid <@ Smv.validboard(BP.bb, BP.pk);
        if (!valid) {
          BP.d <$ {0,1};
        } else {
          (* Recover the board *)
          BP.bb'       <@ Recover'.rec(rem_ids BP.bb0, rem_ids BP.bb1, BP.bb);
          (* We now tally the recovered board *)
          rL <- [];

          j <- 0;
          while (j < size BP.bb') {
            
            b    <- nth witness BP.bb' j;
            ev   <- b.`2;
            id   <- b.`1.`1;
            v    <@ Ev(H).dec(BP.sk.`2, id, ev);
            tr'  <@ ElGamal.dec(BP.sk.`3, oget BP.pk.`3.`3.[id]);

            rL  <- (oget v, oget tr') :: rL;

            j <- j + 1;
          }
          vt     <$ (duniform (allperms rL));
          BP.r   <- (unzip1 vt, unzip2 vt);
          BP.pi  <@ P(G).prove((BP.pk, sPublish BP.bb', BP.r), (BP.sk, BP.bb'));
          BP.pi' <@ S.prove(BP.pk, sPublish BP.bb, BP.r);
            da   <@ A.initial_guess();
          BP.bbstar <@ A.get_tally(BP.r, BP.pi');
          valid'    <@ Smv.verifytally((BP.pk, sPublish BP.bb, BP.bbstar.`1), BP.bbstar.`2);
          if (!valid') {
            BP.d <$ {0,1};
          } else {
            BP.d <@ A.final_guess();
            if (!(BP.setHcheck \subset BP.sethappy)) {
              BP.d <- da; 
            } 
            if (!(BP.setHcheck \subset BP.setchecked)) {
              BP.d <$ {0,1};
            }
          }
        }
      }
      return BP.d;
    }
}.

(*** Proof that G0R' is equivalent to the right side attack game ***)
local lemma DU_MB_BPRIV_R_G0R'_equiv &m : 
  BP.setidents{m} = BP.setH{m} `|` BP.setD{m} =>
    Pr[DU_MB_BPRIV_R(Selene(Ev,P,Ve,C,CP),A,HRO.ERO,G,S,Recover').main() @ &m : res] 
    = Pr[G0R'(Ev,P,Ve,C,CP,A,HRO.ERO,G,S).main() @ &m : res]. 
proof.  
move => ?. 
byequiv => //. 
proc;inline*.  

(*** Let's do the if statements first ***)
seq 35 35 : (
  ={glob HRO.ERO, glob S, glob C, glob CP, glob P, glob A, glob Ev, glob G, 
    glob Ve, BP.bb, BP.bb0, BP.bb1, BP.pk, BP.sk, BP.setidents, 
    BP.pubmap, BP.secmap, BP.vmap, BP.setHcheck, BP.sethappy, BP.setchecked}
); last first.
if => //;first rnd;progress.

seq 8 8 : (
   ={glob HRO.ERO, glob S, glob C, glob CP, glob P, glob A, glob Ev, glob Ve, glob G, BP.setidents, 
      BP.bb, BP.bb0, BP.bb1, BP.pubmap, BP.secmap, BP.vmap, BP.setHcheck, BP.pk, BP.sk,
      BP.sethappy, BP.setchecked, valid} /\
  ! ! (BP.setHcheck{1} \subset fdom BP.vmap{1})
). 
wp. while (={i1, bb, e1, e2, e3, glob C, BP.pubmap, HRO.ERO.m} /\ pd0{1} = pd{2}); first sim. 
auto;progress. 

if => //;first rnd;progress.  

(* Everything that happens before the second valid check *)
seq 31 26 : (
  (={glob HRO.ERO, glob S, glob C, glob CP, glob P, glob A, glob Ev, glob Ve, 
     glob G, valid', BP.r, BP.pi, BP.pi', BP.bbstar, BP.setidents,
       BP.bb, BP.bb0, BP.bb1, BP.pubmap, BP.secmap, BP.vmap, BP.setHcheck, BP.sk,
       BP.pk, BP.sethappy, BP.setchecked, valid} /\
   ! ! (BP.setHcheck{1} \subset fdom BP.vmap{1})) /\ d{1} = da{2} /\
  ! !valid{1}
).
wp. call(_: ={glob S});first sim.  
wp. call(_: ={glob HRO.ERO, glob S, BP.bb0, BP.bb1}); [1..3: by sim]. 
call(_: ={glob HRO.ERO, glob S}); [1..2: by sim].    
call(_: true).   
wp; call(_: ={glob G}). sim. wp;rnd. 
while(i3{1} = j{2} /\ bb3{1} = BP.bb'{2} /\ sd0{1} = BP.sk{2} 
      /\ pd1{1} = BP.pk{2} /\ ={glob Ev, glob HRO.ERO, rL});first sim.  
wp. 
while (={i2, bb2, bb0, bb1, bb'}). sim;progress.  
auto;progress. 

if => //; first rnd;progress. 

seq 1 1 : (
  ((={glob HRO.ERO, glob S, glob C, glob CP, glob P, glob A, BP.d, BP.bbstar,
        glob Ev, glob Ve, valid', BP.r, BP.pi, BP.pi', BP.bb, BP.bb0, BP.bb1,
        BP.pubmap, BP.secmap, BP.vmap, BP.setHcheck, BP.sk, BP.pk, BP.setidents,
        BP.sethappy, BP.setchecked, valid} /\
    ! ! (BP.setHcheck{1} \subset fdom BP.vmap{1})) /\ d{1} = da{2} /\
   ! !valid{1}) /\
  ! !valid'{1}
).

call(_: ={glob HRO.ERO, BP.bbstar, BP.bb, BP.vmap, BP.secmap, BP.pubmap, BP.setidents, 
          BP.sethappy, BP.setchecked, glob CP, glob S}); [1..3: by sim]; first auto.  
if => //;sp. if => //;first rnd;progress. 
if => //; first rnd;progress.  

(*** Now we do the creation of BP.bb and everything that comes before ***)

call(_: ={glob HRO.ERO, glob S, BP.secmap, BP.pubmap, BP.setH, BP.pk, 
          glob Ev, BP.vmap, BP.bb0, BP.bb1});first sim; progress. 
sim;progress.  sim. sim. 
while (={i, BP.setidents, BP.pk, BP.sk, glob CP, BP.secmap, BP.pubmap, BP.setD, BP.secmapD}). 
sim;auto;progress.
wp;while(={i0, BP.setidents, tpk, tsk, pPk, pTr, pCo, pOp, trL,pi2}); first sim.  
wp;while(={i0, BP.setidents, trL, pTr, glob CP, pPk, tpk}); first sim. 
wp;rnd;while(={i0, BP.setidents, tpk, tpTr, trL}); first sim. 
wp;rnd;call(_:true);auto;call(_:true);call(_:true). 
while (={w, glob HRO.ERO}); first sim. 
auto;progress. 
qed.

(**** We now move the tally and the valid check outside of the if statements ****)
local module G0R(Ev:PKEvo.Scheme, Ve:Verifier, C:ValidIndS, CP:CommitmentProtocol, 
                 A:DU_MB_BPRIV_adv, H:HOracle.Oracle, S:Simulator) = {

    module O   = DU_MB_BPRIV_oracles(Selene(Ev,P,Ve,C,CP), H, S, Right)
    module A   = A(O)
    module Smv = Selene(Ev,P,Ve,C,CP,H,S)

    proc main() : bool = {
      var i;
      var id, upk, ct, d, da, vt;
      var valid, valid';
      var rL, j, b, ev, v, tr';
      
      BP.vmap       <- empty;
      BP.pubmap     <- empty;
      BP.secmap     <- empty;
      BP.secmapD    <- empty;
      BP.bb0        <- [];
      BP.bb1        <- [];
      BP.setchecked <- fset0;
      BP.sethappy   <- fset0;
      
      H.init();
      S.init();
      
      (* setup *)
      (BP.pk, BP.sk) <@ Smv.setup();

      (* register *)
      i <- 0;
      while (i < card BP.setidents) {
        id  <- nth witness (elems BP.setidents) i;
         d  <- oget BP.sk.`1.[id];
        upk <- oget BP.pk.`3.`4.[id];
        ct  <- oget BP.pk.`3.`5.[id];
        BP.secmap.[id] <- d;
        BP.pubmap.[id] <- (id, upk, ct);

        if (id \in BP.setD) {
          BP.secmapD.[id] <- oget BP.secmap.[id];
        }

        i <- i + 1;
      }

      (* adversary creates bulletin board *)
      BP.bb <@ A.create_bb(BP.pk, BP.secmapD, BP.pubmap, BP.setHcheck);

      (* check if BP.bb is valid *)
      valid <@ Smv.validboard(BP.bb, BP.pk);

      (* Recover the board *)
      BP.bb'       <@ Recover'.rec(rem_ids BP.bb0, rem_ids BP.bb1, BP.bb);
      (* We now tally the recovered board *)
      rL <- [];

      j <- 0;
      while (j < size BP.bb') {
            
        b    <- nth witness BP.bb' j;
        ev   <- b.`2;
        id   <- b.`1.`1;
        v    <@ Ev(H).dec(BP.sk.`2, id, ev);
        tr'  <@ ElGamal.dec(BP.sk.`3, oget BP.pk.`3.`3.[id]);

        rL   <- (oget v, oget tr') :: rL;

         j  <- j + 1;
      }
      
      vt   <$ (duniform (allperms rL));
      BP.r <- (unzip1 vt, unzip2 vt);
      

      if (!(BP.setHcheck \subset fdom BP.vmap)) {
        BP.d <$ {0,1};
      } else {
        if (!valid) {
          BP.d <$ {0,1};
        } else {
           BP.pi'   <@ S.prove(BP.pk, sPublish BP.bb, BP.r);
             da     <@ A.initial_guess();
          BP.bbstar <@ A.get_tally(BP.r, BP.pi');
          valid'    <@ Smv.verifytally((BP.pk, sPublish BP.bb, BP.bbstar.`1), BP.bbstar.`2);
          if (!valid') {
            BP.d <$ {0,1};
          } else {
            BP.d <@ A.final_guess();
            if (!(BP.setHcheck \subset BP.sethappy)) {
              BP.d <- da; 
            } 
            if (!(BP.setHcheck \subset BP.setchecked)) {
              BP.d <$ {0,1};
            }
          }
        }
      }
      return BP.d;
    }
}.

(*** We prove that G0R' and G0R are equivalent ***)
local lemma G0R'_G0R_equiv &m : 
    BP.setidents{m} = BP.setH{m} `|` BP.setD{m} =>
    Pr[G0R'(Ev,P,Ve,C,CP,A,HRO.ERO,G,S).main() @ &m : res] = Pr[G0R(Ev,Ve,C,CP,A,HRO.ERO,S).main() @ &m : res]. 
proof. 
move => ?. 
byequiv => //. 
proc.   

(* The games are equivalent up to creating BP.bb *)
seq 15 14 : (
  ={glob HRO.ERO, glob CP, glob A, glob C, glob Ve, glob S, glob Ev,
    BP.setHcheck, BP.secmapD, BP.setD, BP.setidents, BP.setH, BP.vmap, BP.pubmap,
    BP.secmap, BP.bb0, BP.bb1, BP.setchecked, BP.sethappy, BP.pk, BP.sk, BP.bb,
    BP.setidents}
).

call(_:
  ={glob HRO.ERO, glob S, glob Ev, BP.pk, BP.sk, BP.pubmap, BP.secmap, BP.setH, BP.vmap,
    BP.bb0, BP.bb1}
); [1..4: by sim].  
while(={i, BP.setidents, glob CP, BP.pubmap, BP.setD, BP.secmapD, BP.sk, BP.secmap, BP.pk}); first sim. progress.   
wp. 
inline*.   
wp;while(={i0, BP.setidents, tpk, tsk, pPk, pTr, pCo, pOp, trL, pi2}); first sim.  
wp;while(={i0, BP.setidents, trL, pTr, glob CP, pPk, tpk}); first sim. 
wp;rnd;while(={i0, BP.setidents, tpk, tpTr, trL}); first sim. 
wp;rnd;call(_:true);auto;call(_:true);call{1} Gi_ll. 
while(={w, HRO.ERO.m}); first sim. 
auto;progress. 

(* First case: BP.setHcheck \notin fdom BP.vmap *)
(* The first case is true *)
case (!(BP.setHcheck{1} \subset fdom BP.vmap{1})).
rcondt{1} 1;progress. rcondt{2} 8;progress. 
inline*. wp;rnd.  
while (0 <= j <= size BP.bb'). 
wp;call(_:true);auto;progress => /#.  
wp;while(0 <= i1 <= size bb2);auto;progress;[smt() | smt() | wp].  
while(0 <= i0 <= size bb);auto. 
call(_:true);auto;progress => /#.  
progress.
rnd.   
wp;rnd{2}. 
while{2} (0 <= j{2} <= size BP.bb'{2}) (size BP.bb'{2} - j{2});progress. 
wp;call(Et_dec_ll);call(Ev_dec_ll HRO.ERO HRO.ERO_o_ll);wp;skip;progress;smt(). 
inline*. 
wp. while{2} (0 <= i1{2} <= size bb2{2}) (size bb2{2} - i1{2});progress;auto;progress;[1..3: by smt()]. 
while{2} (0 <= i0{2} <= size bb{2}) (size bb{2} - i0{2});progress. 
auto.  
call(C_vi_ll HRO.ERO HRO.ERO_o_ll);wp;skip;progress => /#. 
auto;progress; 
  [rewrite size_ge0 | smt() | rewrite size_ge0 | smt() | rewrite size_ge0 | smt() | rewrite duni_ap_ll].

(* The first case is now false *)
rcondf{1} 1;progress;rcondf{2} 8;progress. 
inline*. wp;rnd.  
while (0 <= j <= size BP.bb'). 
wp;call(_:true);auto;progress => /#.  
wp;while(0 <= i1 <= size bb2);auto;progress; [smt() | smt() | wp].  
while(0 <= i0 <= size bb);auto. 
call(_:true);auto;progress => /#.
progress.

(* The valid checks are equivalent *)
seq 1 1 : (={glob CP, glob A, glob C, glob Ve, glob Ev, glob S,
      BP.setHcheck, BP.secmapD, BP.setD, BP.setidents, BP.setH, BP.pk, BP.sk,
      BP.vmap, BP.pubmap, BP.secmap, BP.bb0, BP.bb1, BP.setchecked, BP.bb,
      BP.sethappy, HRO.ERO.m, valid, BP.setidents} /\
  (BP.setHcheck{1} \subset fdom BP.vmap{1})).
inline*.
wp;while(={i0, e1, e2, e3, pd, bb, HRO.ERO.m, BP.pubmap, glob C}); first sim. 
auto;progress. 

(* We now case on the board being valid, assume first this is false *)
case (!valid{1}). 
rcondt{1} 1;progress. 
rcondt{2} 7;progress. 
wp;rnd;while(0 <= j <= size BP.bb'). wp;call(_:true); first by auto. 
call(_:true);auto;progress => /#. 
inline*. 
wp;while(0 <= i0 <= size bb);auto;progress; [smt() | smt()].
rnd.  
wp;rnd{2}. 
while{2} (0 <= j{2} <= size BP.bb'{2}) (size BP.bb'{2} - j{2});progress. 
wp;call(Et_dec_ll);call(Ev_dec_ll HRO.ERO HRO.ERO_o_ll);wp;skip;progress;smt(). 
inline*. 
wp;while{2} (0 <= i0{2} <= size bb{2}) (size bb{2} - i0{2});progress;auto;progress; 
    [smt() | smt() | smt() | rewrite size_ge0 | smt() | rewrite  size_ge0 | smt() | rewrite duni_ap_ll].

(*** Now assume the board is  valid ***)
rcondf{1} 1;progress. rcondf{2} 7;progress. 
inline*;wp;rnd;while(0 <= j <= size BP.bb'). 
wp;call(_:true); first by auto. 
auto;progress => /#. 
wp;while(0 <= i0 <= size bb);auto;progress;[smt() | smt()].
inline*; first sim. 
call{1} (PS_p_ll G Go_ll). 
by sim. 
qed. 

(***** We now stop decrypting honest ciphertexts and use plain votes from BP.vmap instead. *****)
(***** Ciphertexts added by the adversary are decrypted as usual.                          *****)

local module G1R(Ev:PKEvo.Scheme, Ve:Verifier, C:ValidIndS, CP:CommitmentProtocol, 
                 A:DU_MB_BPRIV_adv, H:HOracle.Oracle, S:Simulator) = {
   
    module Smv = Selene(Ev,P,Ve,C,CP,H,S)

    module O = {
   
      proc h = H.o
      proc g = S.o

      proc vote_core(id, v, sl) = {
        var p, b, spr, spo;
        (p, b, spr, spo) <@ Smv.vote(BP.pk, id, oget BP.pubmap.[id], sl, v);
        return (p,b,spr, spo);
      }

      proc vote(id:ident, v0 v1 : vote) = {
      var p0, b0, s0pr, s0po;
      var p1, b1, s1pr, s1po;
  
      if (id \in BP.setH) {
        (p0, b0, s0pr, s0po) <@ vote_core(id, v0, oget BP.secmap.[id]);
        (p1, b1, s1pr, s1po) <@ vote_core(id, v1, oget BP.secmap.[id]);

        BP.vmap.[id] <- (b0, s1pr, s0po, v0) :: (odflt [] BP.vmap.[id]);

        BP.bb0 <- (id, oget BP.pubmap.[id], b0) :: BP.bb0;
        BP.bb1 <- (id, oget BP.pubmap.[id], b1) :: BP.bb1;
        }
      }

      proc verify(id:ident) = {
        var ok, sv;
        if (id \in BP.setidents){
          BP.setchecked <- BP.setchecked `|` (fset1 id);
          sv <- odflt [] (BP.vmap.[id]);
          ok <@ Smv.verifyvote(id, (oget (ohead sv)).`2, (oget (ohead sv)).`3, 
                               BP.bb, BP.bbstar, oget BP.pubmap.[id], oget BP.secmap.[id]);
          if (ok) {
            BP.sethappy <- BP.sethappy `|` (fset1 id);
          }
        }
        return BP.sethappy;
      }

      proc board() = {
        return sPublish (rem_ids BP.bb1);
      } 

    }

    module A = A(O)

    proc main() : bool = {
      var i;
      var id, upk, ct, d, da, vt;
      var valid, valid';
      var rL, j, b, ev, v, tr', sv, k;

      BP.vmap       <- empty;
      BP.pubmap     <- empty;
      BP.secmap     <- empty;
      BP.secmapD    <- empty;
      BP.bb0        <- [];
      BP.bb1        <- [];
      BP.setchecked <- fset0;
      BP.sethappy   <- fset0;
      
      H.init();
      S.init();
      
      (* setup *)
      (BP.pk, BP.sk) <@ Smv.setup();

      (* register *)
      i <- 0;
      while (i < card BP.setidents) {
        id  <- nth witness (elems BP.setidents) i;
         d  <- oget BP.sk.`1.[id];
        upk <- oget BP.pk.`3.`4.[id];
        ct  <- oget BP.pk.`3.`5.[id];
        BP.secmap.[id] <- d;
        BP.pubmap.[id] <- (id, upk, ct);

        if (id \in BP.setD) {
          BP.secmapD.[id] <- oget BP.secmap.[id];
        }

        i <- i + 1;
      }

      (* adversary creates bulletin board *)
      BP.bb <@ A.create_bb(BP.pk, BP.secmapD, BP.pubmap, BP.setHcheck);

      (* check if BP.bb is valid *)
      valid <@ Smv.validboard(BP.bb, BP.pk);

      (* Recover the board *)
      BP.bb'  <@ Recover'.rec(rem_ids BP.bb0, rem_ids BP.bb1, BP.bb);

      (* We now tally the recovered board *)
      rL <- [];
      j <- 0;

      while (j < size BP.bb') {
            
        b    <- nth witness BP.bb' j;
        ev   <- b.`2;
        id   <- b.`1.`1;
        if ( (id, oget BP.pubmap.[id], ev) \in BP.bb0) {
          (* Get the vote from BP.vmap that mathes the ballot *)
          sv <- odflt [] BP.vmap.[id]; (* get list for voter id *)
          k  <- find (fun (x:cipher*cipher*vote*vote) => x.`1 = ev) sv; (* first index where b appears *)
          v  <- Some (oget (onth sv k)).`4; (* the vote at that index *)
        } else {
          v    <@ Ev(H).dec(BP.sk.`2, id, ev);
        }

        tr'  <@ ElGamal.dec(BP.sk.`3, oget BP.pk.`3.`3.[id]);

        rL   <- (oget v, oget tr') :: rL;

         j  <- j + 1;
      }
      
      vt   <$ (duniform (allperms rL));
      BP.r <- (unzip1 vt, unzip2 vt);

      if (!(BP.setHcheck \subset fdom BP.vmap)) {
        BP.d <$ {0,1};
      } else {
        if (!valid) {
          BP.d <$ {0,1};
        } else {
             BP.pi' <@ S.prove(BP.pk, sPublish BP.bb, BP.r);
              da    <@ A.initial_guess();
          BP.bbstar <@ A.get_tally(BP.r, BP.pi');
          valid'    <@ Smv.verifytally((BP.pk, sPublish BP.bb, BP.bbstar.`1), BP.bbstar.`2);
          if (!valid') {
            BP.d <$ {0,1};
          } else {
            BP.d <@ A.final_guess();
            if (!(BP.setHcheck \subset BP.sethappy)) {
              BP.d <- da; 
            } 
            if (!(BP.setHcheck \subset BP.setchecked)) {
              BP.d <$ {0,1};
            }
          }
        }
      }
      return BP.d;
    }
}.
 
local lemma G0R_G1R_equiv &m : 
    BP.setidents{m} = BP.setH{m} `|` BP.setD{m} =>
    Pr[G0R(Ev,Ve,C,CP,A,HRO.ERO,S).main() @ &m : res] = 
    Pr[G1R(Ev,Ve,C,CP,A,HRO.ERO,S).main() @ &m : res]. 
proof. 
move => ?. 
byequiv => //. 
proc. 

(*** We first do everything up until the creation of BP.bb, showing that BP.bb is equal on both sides, 
    and that  the ciphertexts in bb0 are encryptions of the votes in vmap. ***)
seq 14 14 : ( 
  ={glob CP, glob A, glob C, glob Ve, glob S, glob Ev, glob HRO.ERO, 
    BP.sethappy, BP.setchecked, BP.setidents, BP.setHcheck, BP.secmapD, 
    BP.setD, BP.setidents, BP.setH, BP.pubmap, BP.secmap, BP.bb0, BP.bb1, BP.bb, BP.pk, BP.sk}

  /\ (BP.pk{1}.`1 = get_epk BP.sk{1}.`2) 

  /\ (fdom BP.vmap{1} = fdom BP.vmap{2})

  /\ (forall id i, rem_fst4 (oget (onth (odflt [] BP.vmap{1}.[id]) i)) = 
      rem_fst4 (oget (onth (odflt [] BP.vmap{2}.[id]) i)))

  /\ (forall (id : ident) (c : cipher) pc,  (id, pc, c) \in BP.bb0{2}  =>  
       Some (oget (onth (odflt [] BP.vmap{2}.[id]) 
       (find (fun (x : cipher * cipher * vote * vote) => x.`1 = c) (odflt [] BP.vmap{2}.[id])))).`4
        = dec_cipher_vo BP.sk{2}.`2 id c HRO.ERO.m{2})

  /\ (forall (id:ident) (c:cipher) pc, (id, pc, c) \in BP.bb0{1} => is_some BP.vmap{1}.[id])

  /\ (forall id pc c, (id, pc, c) \in BP.bb0{1} => pc = oget BP.pubmap{2}.[id])
).

call(_: ={glob HRO.ERO, glob S, glob C, glob CP, glob Ev, BP.pk, BP.secmapD, BP.pubmap, BP.sk,
          BP.secmap, BP.setH, BP.setidents, BP.bb0, BP.bb1} 

    /\ (BP.pk{1}.`1 = get_epk BP.sk{1}.`2)

    /\ (fdom BP.vmap{1} = fdom BP.vmap{2})

    /\ (forall id i, rem_fst4 (oget (onth (odflt [] BP.vmap{1}.[id]) i)) = 
        rem_fst4 (oget (onth (odflt [] BP.vmap{2}.[id]) i)))

    /\ (forall (id : ident) (c : cipher) pc,  (id, pc, c) \in BP.bb0{2}  =>  
       Some (oget (onth (odflt [] BP.vmap{2}.[id]) 
        (find (fun (x : cipher * cipher * vote * vote) => x.`1 = c) (odflt [] BP.vmap{2}.[id])))).`4
        = dec_cipher_vo BP.sk{2}.`2 id c HRO.ERO.m{2})

    /\ (forall (id:ident) (c:cipher) pc, (id, pc, c) \in BP.bb0{1} => is_some BP.vmap{1}.[id])

    /\ (forall id pc c, (id, pc, c) \in BP.bb0{1} => pc = oget BP.pubmap{2}.[id])
).

proc. if => //;inline*. 
swap{1} [16..20] -4. swap{2} [13..20] -4. 

seq 18 17 : (
  ={HRO.ERO.m, glob S, glob C, glob CP, glob Ev, BP.pk, BP.secmapD,
       BP.pubmap, BP.sk, BP.secmap, BP.setH, BP.setidents, BP.bb0, BP.bb1} 

  /\ (BP.pk{1}.`1 = get_epk BP.sk{1}.`2)

  /\ Some v0{2} = dec_cipher_vo BP.sk{2}.`2 id{2} ev{2} HRO.ERO.m{2}

  /\ ={id, v0, v1, pd0, pc, ev} /\ id1{1} = id2{2} /\ v{1} = v3{2} 

  /\ id2{1} = id3{2} /\ v2{1} = v4{2} /\ pc{1} = pb0{1} /\ id{1} = id0{2}

  /\ pc{1} = oget BP.pubmap{2}.[id0{2}] /\ pc0{1} = oget BP.pubmap{2}.[id0{2}]

  /\ fdom BP.vmap{1} = fdom BP.vmap{2} 
    
  /\ (forall (id4 : ident) (i : int), rem_fst4 (oget (onth (odflt [] BP.vmap{1}.[id4]) i)) = 
      rem_fst4 (oget (onth (odflt [] BP.vmap{2}.[id4]) i)))

  /\ (forall (id4 : ident) (c : cipher) pc, (id4, pc, c) \in BP.bb0{2} =>
      Some (oget (onth (odflt [] BP.vmap{2}.[id4]) 
           (find (fun (x : cipher * cipher * vote * vote) => x.`1 = c)
           (odflt [] BP.vmap{2}.[id4])))).`4 =
      dec_cipher_vo BP.sk{2}.`2 id4 c HRO.ERO.m{2}) 

  /\ (forall (id4 : ident) (c : cipher) pc, (id4, pc, c) \in BP.bb0{1} =>
     is_some BP.vmap{1}.[id4]) 

  /\ (id{1} \in BP.setH{1})

  /\ (forall id pc c, (id, pc, c) \in BP.bb0{1} => pc = oget BP.pubmap{2}.[id])
).

sp. 
exists* (glob Ev){1}, BP.sk{1}, pd{1}, id1{1}, v{1}.
elim* => ev sk pd id v. 
pose kp := pd.`1 = get_epk sk.`2. 
have em_kp : kp \/ !kp by exact/orbN. 
elim em_kp; move => h. 
call (Eenc_dec_vo sk.`2 pd.`1 id v) => //. 
conseq (_: _ ==> !(pd.`1 = get_epk sk.`2));progress. 
call(_: ={glob HRO.ERO}). sim. auto;progress. 
wp. call(_: ={glob HRO.ERO}); first sim.  auto;progress.
smt(@SmtMap).  

(*** Proof that BP.vmap without first element is equal on both sides ***)
case (id0{2} = id4); move => id_eq. 
rewrite id_eq. 
rewrite get_set_sameE get_set_sameE. 
case (i = 0) => i0. rewrite /rem_fst4 => /#. 
 
case (is_some BP.vmap{1}.[id4]);move => vmap1_is_some.
have vmap2_is_some : is_some BP.vmap{2}.[id4]; first by smt(@SmtMap). 
have is_some_odflt : forall (a : ((cipher * cipher * vote * vote) list) option), 
     is_some a => odflt [] a = oget a by smt().
rewrite is_some_odflt;first by smt(). 
rewrite is_some_odflt;first by smt(). 
rewrite /rem_fst => /#. 
smt(@SmtMap). smt(@SmtMap). 

(** Proof that vote stored in vmap is decryption of stored ciphertext **)
case (id0{2} = id4); move => id_eq.  
rewrite id_eq. 
rewrite get_set_sameE.
case (ev{2} = c); move => ev2_c_eq. 
rewrite ev2_c_eq. smt(@SmtMap). 

have in_bb0 : (id4, pc1, c) \in BP.bb0{2} by smt(). 
apply H3 in in_bb0. 
rewrite -in_bb0. rewrite (H3 id4 c pc1); first smt(). smt(@List @SmtMap). 

rewrite get_setE. 
have -> :  (if id4 = id0{2} then 
           Some ((ev{2}, result_R, v3{2}, v0{2}) :: odflt [] BP.vmap{2}.[id0{2}])
            else BP.vmap{2}.[id4]) = BP.vmap{2}.[id4] by smt().  
have in_bb0 : (id4, pc1, c) \in BP.bb0{2} by smt(). 
apply H3 in in_bb0; first smt(). 

(* is_some BP.vmap{1} *)
case(id4 = id0{2}) => ideq.  
rewrite get_set_eqE. rewrite ideq. trivial. trivial. 
rewrite get_set_neqE. rewrite ideq. trivial. rewrite (H4 id4 c pc1). smt(). 

(* pc = pubmap.[id] *)
smt(@SmtMap).  

(* board and random oracles *)
proc;inline*;auto. 
proc;inline*;auto. 
by conseq So_ll2. 
 
(* Everything that happens before A.a1 call *)
while ( ={i, BP.setidents, glob CP, BP.secmap, BP.pubmap, 
         BP.setD, BP.secmapD, BP.sk, BP.pk} ); first sim. 
wp;inline*.   
 wp;while(={i0, BP.setidents, tpk, tsk, pPk, pTr, pCo, pOp, trL, pi2}); first sim.  
wp;while(={i0, BP.setidents, trL, pTr, glob CP, pPk, tpk}); first sim. 
wp;rnd;while(={i0, BP.setidents, tpk, tpTr, trL}); first sim. 
wp;rnd;call Ev_kgen_get_epk;auto;call(_:true);
while(={w, glob HRO.ERO}); first sim. 
auto;progress. 

(*** The if statements are equivalent ***)
seq 7 7 : (
  ={glob HRO.ERO, glob S, glob Ve, glob CP, BP.setHcheck, valid, glob A, 
    BP.r,  BP.bb0, BP.bb1, BP.pk, BP.bb, BP.bb', BP.setidents,
    BP.pubmap, BP.secmap, BP.sethappy, BP.setchecked}
  /\ (fdom BP.vmap{1} = fdom BP.vmap{2})
  /\ (forall id i, rem_fst4 (oget (onth (odflt [] BP.vmap{1}.[id]) i)) = 
      rem_fst4 (oget (onth (odflt [] BP.vmap{2}.[id]) i)))
);last first. 

if => //;progress;[1..2: by smt()].  
rnd;skip;progress. 
if => //; first rnd;progress.  
inline*. 
  
seq 13 13 : (
  ((={HRO.ERO.m, glob S, glob Ve, glob CP, BP.setHcheck, valid, glob A, BP.r, 
      BP.pi', BP.bb0, BP.bb1, BP.pk, BP.bb, valid', BP.bbstar, BP.setidents,
     BP.pubmap, BP.secmap, BP.sethappy, BP.setchecked, da} /\
    fdom BP.vmap{1} = fdom BP.vmap{2}) 
    /\ (forall id i, rem_fst4 (oget (onth (odflt [] BP.vmap{1}.[id]) i)) = 
        rem_fst4 (oget (onth (odflt [] BP.vmap{2}.[id]) i)))
    /\ (BP.setHcheck{1} \subset fdom BP.vmap{1})) 
    /\ valid{1}
).

wp;call(_: ={glob S}). sim. wp. 
call(_: ={glob HRO.ERO, glob S, BP.bb0, BP.bb1}). 
proc;inline*;auto.  sim. sim.
call(_: ={glob HRO.ERO, glob S}); [1..2: by sim].
call(_:true).    
auto;progress. 

if => //;first rnd;progress. 

seq 1 1 : (
   (((={HRO.ERO.m, glob S, glob Ve, glob CP, BP.setHcheck, valid, glob A,
         BP.r, BP.pi', BP.d, BP.bbstar, da, BP.setidents, 
         BP.bb0, BP.bb1, BP.pk, BP.bb, valid', BP.pubmap, BP.secmap, 
         BP.sethappy, BP.setchecked} /\
         fdom BP.vmap{1} = fdom BP.vmap{2}) 
       /\ (forall id i, rem_fst4 (oget (onth (odflt [] BP.vmap{1}.[id]) i)) = 
          rem_fst4 (oget (onth (odflt [] BP.vmap{2}.[id]) i)))
   /\ (BP.setHcheck{1} \subset fdom BP.vmap{1})) /\
   ! !valid{1}) /\
  ! !valid'{1} 
).

call(_: ={glob HRO.ERO, glob S, BP.bbstar, BP.bb, BP.pubmap, BP.secmap, 
         glob CP, BP.sethappy, BP.setchecked, BP.setidents}
  /\ (forall id i, rem_fst4 (oget (onth (odflt [] BP.vmap{1}.[id]) i)) = 
     rem_fst4 (oget (onth (odflt [] BP.vmap{2}.[id]) i)))
  /\ (fdom BP.vmap{1} = fdom BP.vmap{2})
).

proc;inline*.
if =>//.   
seq 15 15 : (
  ={id, ok} /\ 
  ={HRO.ERO.m, glob S, BP.bbstar, BP.bb, BP.pubmap, BP.secmap, glob CP,
      BP.sethappy, BP.setchecked, BP.setidents}
   /\ (forall id i, rem_fst4 (oget (onth (odflt [] BP.vmap{1}.[id]) i)) = 
      rem_fst4 (oget (onth (odflt [] BP.vmap{2}.[id]) i)))
  /\ fdom BP.vmap{1} = fdom BP.vmap{2}
).

auto;call(_:true);wp;skip;progress. 
have ? : rem_fst4 (oget (onth (odflt [] BP.vmap{1}.[id{2}]) 0)) = 
         rem_fst4 (oget (onth (odflt [] BP.vmap{2}.[id{2}]) 0)) by smt(). 
 smt(@List).  
if => //; auto. 
 
proc. auto;progress. 
conseq So_ll2. progress. progress. auto;progress. 
if => //;sp. if => //;first rnd;progress. 
if => //;first rnd;progress. 
wp;rnd. 

while (
  ={j, BP.bb', glob Ev, BP.sk, BP.pk, rL, BP.bb0, BP.pubmap, glob HRO.ERO}
  /\ BP.pk{1}.`1 = get_epk BP.sk{1}.`2 /\
  fdom BP.vmap{1} = fdom BP.vmap{2} /\
  (forall (id0 : ident) (i0 : int),
     rem_fst4 (oget (onth (odflt [] BP.vmap{1}.[id0]) i0)) =
     rem_fst4 (oget (onth (odflt [] BP.vmap{2}.[id0]) i0))) /\
  (forall (id0 : ident) (c : cipher),
     (id0, oget BP.pubmap{2}.[id0], c) \in BP.bb0{2} =>
     Some
       (oget
          (onth (odflt [] BP.vmap{2}.[id0])
             (find (fun (x : cipher * cipher * vote * vote) => x.`1 = c)
                (odflt [] BP.vmap{2}.[id0])))).`4 =
     dec_cipher_vo BP.sk{2}.`2 id0 c HRO.ERO.m{2}) /\
  forall (id0 : ident) (c : cipher) pc,
    (id0, pc, c) \in BP.bb0{1} =>
    is_some BP.vmap{1}.[id0]
).

wp;sp. 
call(_:true); first by auto.  
if{2} => //. wp. 
exists* (glob Ev){1}, BP.sk{1}, id{1}, ev{1}; elim* => gev sk id ev.
call{1} (Edec_Odec_vo gev sk.`2 id ev). auto;progress.

have ? : is_some BP.vmap{1}.[(nth witness BP.bb'{2} j{2}).`1.`1]. 
rewrite (H3 (nth witness BP.bb'{2} j{2}).`1.`1 (nth witness BP.bb'{2} j{2}).`2 
         (oget BP.pubmap{2}.[(nth witness BP.bb'{2} j{2}).`1.`1])).  
rewrite H6. 
 
have ? : Some (oget (onth (odflt [] BP.vmap{2}.[(nth witness BP.bb'{2} j{2}).`1.`1]) 
                 (find (fun (x : cipher * cipher * vote * vote) 
                   => x.`1 = (nth witness BP.bb'{2} j{2}).`2)
                 (odflt [] BP.vmap{2}.[(nth witness BP.bb'{2} j{2}).`1.`1])))).`4
           = dec_cipher_vo BP.sk{2}.`2 (nth witness BP.bb'{2} j{2}).`1.`1 
                                       (nth witness BP.bb'{2} j{2}).`2 HRO.ERO.m{2}. 

rewrite (H2 (nth witness BP.bb'{2} j{2}).`1.`1 (nth witness BP.bb'{2} j{2}).`2). 
rewrite H6. 
trivial.
smt().  

call(_: ={glob HRO.ERO}).  sim. auto;progress. 

inline*. 
wp;while(={i1, bb2, bb0, bb1, bb'}); first sim. 

wp;while(={i0, bb, e1, e2, e3, glob HRO.ERO, glob C, pd, BP.pubmap}); first sim. 
auto;progress. rewrite (H2 id00 c (oget BP.pubmap{2}.[id00])). exact/H9.  trivial. 
qed. 


(*** We now stop recovering and set BP.bb' to be BP.bb ***)
local module G2R(Ev:PKEvo.Scheme, Ve:Verifier, C:ValidIndS, CP:CommitmentProtocol, 
                 A:DU_MB_BPRIV_adv, H:HOracle.Oracle, S:Simulator) = {

    module Smv = Selene(Ev,P,Ve,C,CP,H,S)

    module O = {
   
      proc h = H.o
      proc g = S.o

      proc vote_core(id, v, sl) = {
        var p, b, spr, spo;
        (p, b, spr, spo) <@ Smv.vote(BP.pk, id, oget BP.pubmap.[id], sl, v);
        return (p,b,spr, spo);
      }

      proc vote(id:ident, v0 v1 : vote) = {
      var p0, b0, s0pr, s0po;
      var p1, b1, s1pr, s1po;
  
      if (id \in BP.setH) {
        (p0, b0, s0pr, s0po) <@ vote_core(id, v0, oget BP.secmap.[id]);
        (p1, b1, s1pr, s1po) <@ vote_core(id, v1, oget BP.secmap.[id]);

        (* We now store b1, s1, v0, instead of b0, s1, v0 as we did in G1R *)
        BP.vmap.[id] <- (b1, s1pr, s0po, v0) :: (odflt [] BP.vmap.[id]);

        BP.bb0 <- (id, oget BP.pubmap.[id], b0) :: BP.bb0;
        BP.bb1 <- (id, oget BP.pubmap.[id], b1) :: BP.bb1;
        }
      }

      proc verify = G1R(Ev,Ve,C,CP,A,H,S).O.verify

      proc board() = {
        return sPublish (rem_ids BP.bb1);
      } 

    }

    module A = A(O)

    proc main() : bool = {
      var i;
      var id, upk, ct, d, da, vt;
      var valid, valid';
      var rL, j, b, ev, v, tr', sv, k;

      BP.vmap       <- empty;
      BP.pubmap     <- empty;
      BP.secmap     <- empty;
      BP.secmapD    <- empty;
      BP.bb0        <- [];
      BP.bb1        <- [];
      BP.setchecked <- fset0;
      BP.sethappy   <- fset0;
      
      H.init();
      S.init();
      
      (* setup *)
      (BP.pk, BP.sk) <@ Smv.setup();

      (* register *)
      i <- 0;
      while (i < card BP.setidents) {
        id  <- nth witness (elems BP.setidents) i;
         d  <- oget BP.sk.`1.[id];
        upk <- oget BP.pk.`3.`4.[id];
        ct  <- oget BP.pk.`3.`5.[id];
        BP.secmap.[id] <- d;
        BP.pubmap.[id] <- (id, upk, ct);

        if (id \in BP.setD) {
          BP.secmapD.[id] <- oget BP.secmap.[id];
        }

        i <- i + 1;
      }

      (* adversary creates bulletin board *)
      BP.bb <@ A.create_bb(BP.pk, BP.secmapD, BP.pubmap, BP.setHcheck);

      (* check if BP.bb is valid *)
      valid <@ Smv.validboard(BP.bb, BP.pk);

      (* We now tally the  board created by the adversary *)
      rL <- [];
      j <- 0;

      while (j < size BP.bb) {
            
        b    <- nth witness BP.bb j;
        ev   <- b.`2;
        id   <- b.`1.`1;
        if ( (id, oget BP.pubmap.[id], ev) \in BP.bb1) {
          (* Get the vote from BP.vmap that mathes the ballot *)
          sv <- odflt [] BP.vmap.[id]; (* get list for voter id *)
          k  <- find (fun (x:cipher*cipher*vote*vote) => x.`1 = ev) sv; (* first index where b appears *)
          v  <- Some (oget (onth sv k)).`4; (* the vote at that index *)
        } else {
          v    <@ Ev(H).dec(BP.sk.`2, id, ev);
        }

        tr'  <@ ElGamal.dec(BP.sk.`3, oget BP.pk.`3.`3.[id]);

        rL   <- (oget v, oget tr') :: rL;

         j  <- j + 1;
      }
      
      vt   <$ (duniform (allperms rL));
      BP.r <- (unzip1 vt, unzip2 vt);

      if (!(BP.setHcheck \subset fdom BP.vmap)) {
        BP.d <$ {0,1};
      } else {
        if (!valid) {
          BP.d <$ {0,1};
        } else {
           BP.pi'   <@ S.prove(BP.pk, sPublish BP.bb, BP.r);
             da     <@ A.initial_guess();
          BP.bbstar <@ A.get_tally(BP.r, BP.pi');
          valid'    <@ Smv.verifytally((BP.pk, sPublish BP.bb, BP.bbstar.`1), BP.bbstar.`2);
          if (!valid') {
            BP.d <$ {0,1};
          } else {
            BP.d <@ A.final_guess();
            if (!(BP.setHcheck \subset BP.sethappy)) {
              BP.d <- da; 
            } 
            if (!(BP.setHcheck \subset BP.setchecked)) {
              BP.d <$ {0,1};
            }
          }
        }
      }
      return BP.d;
    }
}.


local lemma G1R_G2R_equiv &m : 
    BP.setidents{m} = BP.setH{m} `|` BP.setD{m} =>
    Pr[G1R(Ev,Ve,C,CP,A,HRO.ERO,S).main() @ &m : res] = 
    Pr[G2R(Ev,Ve,C,CP,A,HRO.ERO,S).main() @ &m : res]. 
proof. 
move => id_union. 
byequiv => //;proc. 
 
(* We first have a look at everything that happens before the adversary creates BP.bb, and we prove *)
(* that for each identity that is registered, we have that pubmap.[id].`1 = id                      *)
seq 13 13 : (
  ={glob A, glob C, glob CP, glob Ve, glob S, glob Ev, HRO.ERO.m, 
    BP.setHcheck, BP.secmapD, BP.pk, BP.sk, BP.setidents, 
    BP.setD, BP.setidents, BP.setH, BP.vmap, BP.pubmap, BP.secmap, 
    BP.bb0, BP.bb1, BP.setchecked, BP.sethappy}

  /\ (BP.pk{1}.`1 = get_epk BP.sk{1}.`2)

  /\ (forall id, (oget (ohead (odflt [] BP.vmap{1}.[id]))).`3 = 
                 (oget (ohead (odflt [] BP.vmap{2}.[id]))).`3)

  /\ BP.bb0{1} = [] /\ BP.bb0{1} = BP.bb1{1}

  /\ BP.setidents{1} = BP.setH{1} `|` BP.setD{1}

  /\ (forall id, id \in BP.setidents{1} => is_some BP.pubmap{1}.[id])

  /\ (forall id, is_some BP.pubmap{1}.[id] => (oget BP.pubmap{1}.[id]).`1 = id)

  /\ (forall id pc c, (id, pc, c) \in BP.bb1{1} => pc = (oget BP.pubmap{1}.[id]))
). 
 
while(={i, BP.setidents, BP.pubmap, BP.secmap, BP.secmapD, 
           BP.setD, BP.sk, glob CP, BP.pk}

  /\ (forall j id, j <= i{1} => id \in (take j (elems BP.setidents{1})) 
      => is_some BP.pubmap{1}.[id])

  /\ (forall id, is_some BP.pubmap{1}.[id] => (oget BP.pubmap{1}.[id]).`1 = id)
  
).   

seq 6 6 : (
  (={i, BP.setidents, BP.pubmap, BP.secmap, BP.secmapD, BP.setD, BP.sk, id, BP.pk,
       glob CP} /\
   (forall (j0 : int) (id0 : ident),
      j0 <= i{1} + 1 =>
      id0 \in take j0 (elems BP.setidents{1}) => is_some BP.pubmap{1}.[id0]) /\
   forall (id0 : ident),
     is_some BP.pubmap{1}.[id0] => (oget BP.pubmap{1}.[id0]).`1 = id0) /\
  i{1} < card BP.setidents{1}
).

auto;progress.   

rewrite get_setE. 
case( id0 = nth witness (elems BP.setidents{2}) i{2}); first by smt(). move => id0_neq_nth. 
case: (0 < j0)=> [gt0_j0|/lezNgt /(take_le0<:ident>) /#].
case (j0 = i{2} + 1) => h. 
+ have h1 : id0 \in take i{2} (elems BP.setidents{2}). 
  + have h2 : (take j0 (elems BP.setidents{2})) <> [].  
    + smt().
    move: H4; rewrite h.
    rewrite (take_nth witness) 1:/#.
    by rewrite mem_rcons /= id0_neq_nth.
  smt().
smt().
smt(@SmtMap). 
if => //;auto;progress.

wp;inline*. 
wp;while(={i0, BP.setidents, tpk, tsk, pPk, pTr, pCo, pOp, trL, pi2}); first sim.  
wp;while(={i0, BP.setidents, trL, pTr, glob CP, pPk, tpk}); first sim. 
wp;rnd;while(={i0, BP.setidents, tpk, tpTr, trL}); first sim. 
wp;rnd;call Ev_kgen_get_epk;wp;call(_:true). 
while(={w, HRO.ERO.m}); first sim. 
auto;progress. smt(@List). smt(@SmtMap). smt(@SmtMap @List).

(**** We now look at the creation of BP.bb and the tally  ****)
(* We first look at the board created by the adversary and prove the following:  *)
(*                                                                               *)
(* 1.  pk corresponds to sk                                                      *)
(* 2.  public credential of ballot comes from pubmap                             *)
(* 3.  The domain of vmap is equal in both games                                 *)
(* 4.  The voters state is equal in the two games                                *)
(* 5.  v0 corresponds to the first ciphertext in vmap on the left side           *)
(* 6.  bb0 and bb1 agree on identitites                                          *)
(* 7.  bb0 and bb1 agree on public credentials                                   *)
(* 8.  bb0 and bb1 have the same size                                            *)
(* 9.  recovery and vmap on the left is equivalent to vmap on the right          *)
(* 10. b is in bb0/bb1, iff (b.`2, b.`3) in rem_ids bb0/bb1                      *)
(* 11. for b in bb1, id is the first element of public credential                *)
(* 12. for b in bb1, index of b = index of (b.`2, b.`3) in rem_ids bb1           *)
(* 13. enc vote in ith element of bb0 = enc vote of ith element of rem_ids bb0   *)
(*                                                                               *)

seq 1 1 : (

  ={glob A, glob S, glob C, glob CP, glob Ev, glob Ve, glob HRO.ERO, 
    BP.pk, BP.sk, BP.setHcheck, BP.setidents, BP.bb0, BP.bb1, BP.bb, 
    BP.sethappy, BP.setchecked, BP.setH, BP.secmap, BP.secmapD, BP.pubmap}

  /\ (* 1 *) (BP.pk{1}.`1 = get_epk BP.sk{1}.`2)

  /\ (* 2 *) (forall id pc c, (id, pc, c) \in BP.bb0{1} => pc = oget BP.pubmap{1}.[id])
  /\         (forall id pc c, (id, pc, c) \in BP.bb1{1} => pc = oget BP.pubmap{1}.[id])

  /\ (* 3 *) (fdom BP.vmap{1} = fdom BP.vmap{2})

  /\ (* 4 *) (forall id, (oget (ohead (odflt [] BP.vmap{1}.[id]))).`3 = 
             (oget (ohead (odflt [] BP.vmap{2}.[id]))).`3)

  /\ (* 5 *) (forall (id:ident) (c:cipher) pc, (id, pc, c) \in BP.bb0{1} => 
             Some (oget (onth (odflt [] BP.vmap{1}.[id]) 
             (find (fun (x : cipher * cipher * vote * vote) => x.`1 = c) 
             (odflt [] BP.vmap{1}.[id])))).`4
             = dec_cipher_vo BP.sk{2}.`2 id c HRO.ERO.m{2})

  /\ (* 6 *) (forall i, (nth witness BP.bb0{2} i).`1 = (nth witness BP.bb1{2} i).`1)

  /\ (* 7 *) (forall i, (nth witness BP.bb0{2} i).`2 = (nth witness BP.bb1{2} i).`2)
  /\         (forall i, (nth witness (rem_ids BP.bb0{1}) i).`1 = 
                        (nth witness (rem_ids BP.bb1{1}) i).`1)

  /\ (* 8 *) (size BP.bb0{2} = size BP.bb1{2})

  /\ (* 9 *) (forall (id:ident) (c:cipher) pc, (id, pc, c) \in BP.bb1{2} =>
             Some (oget (onth (odflt [] BP.vmap{1}.[id]) 
                  (find (fun (x:cipher*cipher*vote*vote) => 
                  x.`1 = (nth witness BP.bb0{2} (index (id, pc, c) BP.bb1{2})).`3)
                  (odflt [] BP.vmap{1}.[id])))).`4
             = Some (oget (onth (odflt [] BP.vmap{2}.[id]) 
                    (find (fun (x:cipher*cipher*vote*vote) => x.`1 = c)
                    (odflt [] BP.vmap{2}.[id])))).`4)   

  /\ (* 10 *) (forall b, b \in rem_ids BP.bb0{1} <=> (b.`1.`1, b.`1, b.`2) \in BP.bb0{1} ) 
  /\          (forall b, b \in rem_ids BP.bb1{1} <=> (b.`1.`1, b.`1, b.`2) \in BP.bb1{1} ) 

  /\ (* 11 *) (forall b, b \in BP.bb1{2} => b.`2.`1 = b.`1)

  /\ (* 12 *) (forall b, b \in BP.bb1{2} => 
                index b BP.bb1{2} = index (b.`2, b.`3) (rem_ids BP.bb1{2}))

  /\ (* 13 *) (forall i, 0 <= i < size BP.bb0{2} =>
               (nth witness (rem_ids BP.bb0{2}) i).`2 = (nth witness BP.bb0{2} i).`3)
).

(* A.a1 call *)
call (_: 
  ={glob S, glob C, glob CP, glob Ev, glob Ve, glob HRO.ERO, 
    BP.pk, BP.sk, BP.setHcheck, BP.setidents, 
    BP.bb0, BP.bb1, BP.sethappy, BP.setchecked, 
    BP.setH, BP.secmap, BP.secmapD, BP.pubmap}

  /\ (BP.pk{1}.`1 = get_epk BP.sk{1}.`2)

  /\ (forall id pc c, (id, pc, c) \in BP.bb0{1} => pc = oget BP.pubmap{1}.[id])
  /\ (forall id pc c, (id, pc, c) \in BP.bb1{1} => pc = oget BP.pubmap{1}.[id])

  /\ (fdom BP.vmap{1} = fdom BP.vmap{2})

  /\ (forall id, (oget (ohead (odflt [] BP.vmap{1}.[id]))).`3 = 
                 (oget (ohead (odflt [] BP.vmap{2}.[id]))).`3)

  /\ (forall (id:ident) (c:cipher) pc, (id, pc, c) \in BP.bb0{1} => 
          Some (oget (onth (odflt [] BP.vmap{1}.[id]) 
               (find (fun (x : cipher * cipher * vote * vote) => x.`1 = c) 
               (odflt [] BP.vmap{1}.[id])))).`4
           = dec_cipher_vo BP.sk{2}.`2 id c HRO.ERO.m{2})

  /\ (forall i, (nth witness BP.bb0{2} i).`1 = (nth witness BP.bb1{2} i).`1)

  /\ (forall i, (nth witness BP.bb0{2} i).`2 = (nth witness BP.bb1{2} i).`2)
  /\ (forall i, (nth witness (rem_ids BP.bb0{1}) i).`1 = 
                (nth witness (rem_ids BP.bb1{1}) i).`1)

  /\ (size BP.bb0{2} = size BP.bb1{2})

  /\ (forall (id:ident) (c:cipher) pc, (id, pc, c) \in BP.bb1{2} =>
           Some (oget (onth (odflt [] BP.vmap{1}.[id]) 
                (find (fun (x:cipher*cipher*vote*vote) => 
                 x.`1 = (nth witness BP.bb0{2} (index (id, pc, c) BP.bb1{2})).`3)
                 (odflt [] BP.vmap{1}.[id])))).`4
           = Some (oget (onth (odflt [] BP.vmap{2}.[id]) 
             (find (fun (x:cipher*cipher*vote*vote) => x.`1 = c)
             (odflt [] BP.vmap{2}.[id])))).`4) 

  /\ (forall (id:ident) (c:cipher) pc, 
           (id, pc, c) \in BP.bb0{1} \/ (id, pc, c) \in BP.bb1{1}
           => is_some BP.vmap{1}.[id] /\ is_some BP.vmap{2}.[id])

  /\ (BP.setidents{1} = BP.setH{1} `|` BP.setD{1})

  /\ (forall id, id \in BP.setidents{1} => is_some BP.pubmap{1}.[id])


  /\ (forall id, is_some BP.pubmap{1}.[id] => (oget BP.pubmap{1}.[id]).`1 = id)

  /\ (forall b, b \in rem_ids BP.bb0{1} <=> (b.`1.`1, b.`1, b.`2) \in BP.bb0{1} )
  /\ (forall b, b \in rem_ids BP.bb1{1} <=> (b.`1.`1, b.`1, b.`2) \in BP.bb1{1} ) 

  /\ (forall b, b \in BP.bb1{2} => b.`2.`1 = b.`1)

  /\ (forall b, b \in BP.bb1{2} => 
                index b BP.bb1{2} = index (b.`2, b.`3) (rem_ids BP.bb1{2}))

  /\ (forall i, 0 <= i < size BP.bb0{2}  =>
       (nth witness (rem_ids BP.bb0{2}) i).`2 = (nth witness BP.bb0{2} i).`3)
).


proc; first if => //. 
inline*.  

swap{1} [13..20] -5. swap{2} [13..20] -5. 

seq 21 21 : (
  ={id, v0, v1, v3, id2, pd, ev, v4, pd0, id3, b0, ev0, s0po} 
    /\ v3{1} = v0{1} /\ v4{1} = v1{1} /\ b0{1} = ev{1} /\

  ={glob S, glob C, glob CP, glob Ev, glob Ve, HRO.ERO.m, BP.pk, BP.pubmap,
       BP.sk, BP.setHcheck, BP.bb0, BP.bb1, BP.sethappy, BP.setchecked,
       BP.setH, BP.secmap, BP.secmapD, BP.setidents} /\

   BP.pk{1}.`1 = get_epk BP.sk{1}.`2 /\
  
    (forall id pc c, (id, pc, c) \in BP.bb0{1} => pc = oget BP.pubmap{1}.[id]) /\
    (forall id pc c, (id, pc, c) \in BP.bb1{1} => pc = oget BP.pubmap{1}.[id]) /\

   fdom BP.vmap{1} = fdom BP.vmap{2} /\

   (forall (id4 : ident), (oget (ohead (odflt [] BP.vmap{1}.[id4]))).`3 =  
     (oget (ohead (odflt [] BP.vmap{2}.[id4]))).`3) /\

   (forall (id4 : ident) (c : cipher) pc, (id4, pc, c) \in BP.bb0{1} =>
      Some (oget (onth (odflt [] BP.vmap{1}.[id4]) 
           (find (fun (x : cipher * cipher * vote * vote) => x.`1 = c)
                 (odflt [] BP.vmap{1}.[id4])))).`4 =  
           dec_cipher_vo BP.sk{2}.`2 id4 c HRO.ERO.m{2}) /\

   (forall i, (nth witness BP.bb0{2} i).`1 = (nth witness BP.bb1{2} i).`1) /\

   (forall (i : int), (nth witness BP.bb0{2} i).`2 = (nth witness BP.bb1{2} i).`2) /\
   (forall i, (nth witness (rem_ids BP.bb0{1}) i).`1 = 
              (nth witness (rem_ids BP.bb1{1}) i).`1) /\

   size BP.bb0{2} = size BP.bb1{2} /\

   (forall (id4 : ident) (c : cipher) pc, (id4, pc, c) \in BP.bb1{2} =>
     Some (oget (onth (odflt [] BP.vmap{1}.[id4]) 
          (find (fun (x : cipher * cipher * vote * vote) =>
        x.`1 = (nth witness BP.bb0{2} (index (id4, pc, c) BP.bb1{2})).`3)
    (odflt [] BP.vmap{1}.[id4])))).`4 = Some (oget (onth (odflt [] BP.vmap{2}.[id4])
             (find (fun (x : cipher * cipher * vote * vote) => x.`1 = c)
                (odflt [] BP.vmap{2}.[id4])))).`4) /\ 

  (id{1} \in BP.setH{1}) /\

  (forall (id:ident) (c:cipher) pc, 
           (id, pc, c) \in BP.bb0{1} \/ (id, pc, c) \in BP.bb1{1}
           => is_some BP.vmap{1}.[id] /\ is_some BP.vmap{2}.[id]) /\
 
  (Some v0{2} = dec_cipher_vo BP.sk{2}.`2 id{2} ev{2} HRO.ERO.m{2}) /\

  (Some v1{2} = dec_cipher_vo BP.sk{2}.`2 id{2} ev0{2} HRO.ERO.m{2})

   /\ BP.setidents{1} = BP.setH{1} `|` BP.setD{1}

   /\ (forall id, id \in BP.setidents{1} => is_some BP.pubmap{1}.[id])


   /\ (forall id, is_some BP.pubmap{1}.[id] => (oget BP.pubmap{1}.[id]).`1 = id)

   /\ (forall b, b \in rem_ids BP.bb0{1} <=> (b.`1.`1, b.`1, b.`2) \in BP.bb0{1} )
   /\ (forall b, b \in rem_ids BP.bb1{1} <=> (b.`1.`1, b.`1, b.`2) \in BP.bb1{1} )

   /\ (forall b, b \in BP.bb1{2} => b.`2.`1 = b.`1)

   /\ (forall b, b \in BP.bb1{2} => 
                index b BP.bb1{2} = index (b.`2, b.`3) (rem_ids BP.bb1{2}))

   /\ (forall i, 0 <= i < size BP.bb0{2}  =>
       (nth witness (rem_ids BP.bb0{2}) i).`2 = (nth witness BP.bb0{2} i).`3)
).

sp. 
exists* BP.sk{1}, pd{1}, v3{1}, v4{1}, id2{1}, id3{1}; elim* => sk pd v0 v1 id2 id3. 
pose kp := pd.`1 = get_epk sk.`2. 
have em_kp : kp \/ !kp by exact/orbN.  
elim em_kp;progress. 
call(Eenc_dec_vo sk.`2 pd.`1 id3 v1). rewrite H => //.  
wp. 
call(Eenc_dec_vo sk.`2 pd.`1 id2 v0). rewrite H => //.  
auto;progress.   

conseq (_: _ ==> !(pd.`1 = get_epk sk.`2));progress. 
call(_: ={glob HRO.ERO}); first sim. auto;progress. 
wp;call(_: ={glob HRO.ERO}). sim. auto; progress. 
auto;progress. smt(). smt(). 
 
(* Property 3: fdom vmap{1} = fdom vmap{2}  *)
by rewrite fdom_set fdom_set H2.  

(* Property 4: voters states are equal *)
case(id4 = id{2}) => ideq. 
rewrite get_set_eqE. by rewrite ideq. 
rewrite get_set_eqE. by rewrite ideq. trivial.
rewrite get_set_neqE. by rewrite ideq. 
rewrite get_set_neqE. by rewrite ideq.
by rewrite H3. 

(* Property 5: v0 corresponds to b0 on the left side *)
case (id{2} = id4) => id_eq. 
case (ev{2} = c) => c_eq.  
rewrite id_eq c_eq. 
rewrite get_set_sameE; first  smt().  
have in_bb0 : (id4, pc1, c) \in BP.bb0{2} by smt(). 

rewrite get_set_eqE; first smt(). 
rewrite -(H4 id4 c pc1); first smt(). 
apply H4 in in_bb0. rewrite id_eq in_bb0. simplify. 

have -> : (if ev{2} = c then 0 else
            (find (fun (x : cipher * cipher * vote * vote) => x.`1 = c)
              (odflt [] BP.vmap{1}.[id4]) + 1)) = 
            find (fun (x : cipher * cipher * vote * vote) => x.`1 = c)
              (odflt [] BP.vmap{1}.[id4]) + 1 by rewrite c_eq. 

have H36 : !(find (fun (x:cipher*cipher*vote*vote) => x.`1 = c) 
            (odflt [] BP.vmap{1}.[id4]) + 1 = 0).  
have H22 : 0 <= find (fun (x:cipher*cipher*vote*vote) => x.`1 = c) 
                     (odflt [] BP.vmap{1}.[id4]) by rewrite find_ge0. 
rewrite addz1_neq0 => />.  
rewrite H36; first simplify. 
rewrite -in_bb0.  
have ? : is_some BP.vmap{1}.[id4] by smt(). 
have -> : odflt [] BP.vmap{1}.[id4] = odflt [] BP.vmap{1}.[id4] by smt(). 
trivial. 

have in_bb0 : (id4, pc1, c) \in BP.bb0{2} by smt(). 
rewrite get_set_neqE; first by smt(). 
rewrite (H4 id4 c pc1); first rewrite in_bb0. trivial. 

(* Property 6: bb0 and bb1 agree on identities *)
case (i=0); first trivial. 
move => i_neq_0. apply H5.  

(* Property 7: bb0 and bb1 agree on public credentials *)
case (i=0); first trivial. 
move => i_neq_0. apply H6.  
have -> : (rem_ids ((id{2}, oget BP.pubmap{2}.[id{2}], ev{2}) :: BP.bb0{2})) 
          = (oget BP.pubmap{2}.[id{2}], ev{2}) :: (rem_ids BP.bb0{2}) 
            by smt(in_rem_ids).  
have -> : (rem_ids ((id{2}, oget BP.pubmap{2}.[id{2}], ev0{2}) :: BP.bb1{2})) 
          = (oget BP.pubmap{2}.[id{2}], ev0{2}) :: (rem_ids BP.bb1{2}) 
            by smt(in_rem_ids). smt().  
by rewrite H8. 

(* Property 9: recovery and vmap on left side is equvalent to vmap on the right *)

(* First assume that id4 = id{2} *)
case(id4 = id{2}) => id_eq. 
rewrite id_eq.      
rewrite get_set_sameE  get_set_sameE.  

(* Case on whether the right ballots are equal *)
have [/#|c_rR_eq]:= eqVneq c (ev0{2}).

(* Now the ballots are not equal *)
have in_bb1 : (id4, pc1, c) \in BP.bb1{2} by smt(). 

have -> : odflt [] BP.vmap{1}.[id{2}] = odflt [] BP.vmap{1}.[id{2}] by smt(). 
have -> : odflt [] BP.vmap{2}.[id{2}] = odflt [] BP.vmap{2}.[id{2}] by smt().
have -> : find (fun (x : cipher * cipher * vote * vote) => x.`1 = c)
         ((ev0{2}, ev0{2}, s0po{2}, v0{2}) :: odflt [] BP.vmap{2}.[id{2}])
       = (find (fun (x : cipher * cipher * vote * vote) => x.`1 = c) 
                    (odflt [] BP.vmap{2}.[id{2}]) + 1) by smt().  
rewrite (H1 id4 pc1 c); first smt(). 
have -> : (index (id{2}, oget BP.pubmap{2}.[id4], c) 
          ((id{2}, oget BP.pubmap{2}.[id{2}], ev0{2}) :: BP.bb1{2}))
         = (index (id{2}, pc1, c) BP.bb1{2} + 1) by smt(). 
have !->: forall (x : ident * (ident * upkey * commitment) * cipher) y, 
            index x y + 1 <> 0 by smt(index_ge0).
have->: forall c, 
        (if false then (id, oget BP.pubmap.[id], ev){2} else c) = c by done.
have onth_cat : forall (a:cipher*cipher*vote*vote) b i, 
                0 <= i => onth (a :: b) (i+1) = onth b i by smt().
have odflt_some: forall (x : cipher * cipher * vote * vote) y, 
          odflt [] (Some (x :: odflt [] y)) = x :: odflt [] y by done.
rewrite !odflt_some.
rewrite onth_cat 1:find_ge0.
rewrite -(H9 id{2} c pc1); first smt(). 
have:= eqVneq (ev{2}) ((nth witness BP.bb0{2} (index (id{2}, pc1, c) BP.bb1{2})).`3) 
        => - [] ev2_nth_bb0.
 
have find_ge0 : find (fun (x : cipher * cipher * vote * vote) => x.`1 = c)
         (odflt [] BP.vmap{2}.[id{2}]) +
       1 <> 0. 
have find_g0 : 0 <= find (fun (x:cipher*cipher*vote*vote) => x.`1 = c) 
                    (odflt [] BP.vmap{2}.[id{2}]) by rewrite find_ge0.
rewrite addz1_neq0 => />. 
rewrite ev2_nth_bb0.  simplify.  
rewrite -ev2_nth_bb0.
have pc_nth : pc1 = (nth witness BP.bb0{2} 
                    (index (id4, pc1, c) BP.bb1{2})).`2 by smt(@List).  
have id_nth : id4 = (nth witness BP.bb0{2} 
                    (index (id4, pc1, c) BP.bb1{2})).`1 by smt(@List). 
have in_bb0 : (id4, pc1, ev{2}) \in BP.bb0{2} by smt(@List). 
rewrite -id_eq.
have:= H4 id4 ev{2} pc1 _.
+ by have:= H21; rewrite c_rR_eq.
by rewrite id_eq -H12.
rewrite /= ev2_nth_bb0 //=.
have H36 : forall a, 0 <= a => a + 1 <> 0. move => a a_geq0. rewrite addz1_neq0 => />.   
rewrite H36.  rewrite find_ge0.  simplify; first by trivial. 

(** Now the identities are not equal **)


rewrite get_set_neqE; first by exact/id_eq. 
rewrite get_set_neqE; first by exact/id_eq.    

have index_neq0 : index (id4, pc1, c) 
                  ((id{2}, oget BP.pubmap{2}.[id{2}], ev0{2}) :: BP.bb1{2}) 
                  <> 0 by smt(@List).  
rewrite index_neq0; first simplify. 

have in_bb1 : (id4, pc1, c) \in BP.bb1{2}; first by smt().  
have H36: nth witness BP.bb0{2} 
             (index (id4, pc1, c) 
             ((id{2}, oget BP.pubmap{2}.[id{2}], ev0{2}) :: BP.bb1{2}) - 1) = 
             nth witness BP.bb0{2} 
             (index (id4, pc1, c) BP.bb1{2}) by smt(@List). 
rewrite H36. apply H9. rewrite in_bb1. 

(** is_some vmap  **)
case(id4 = id{2}) => ideq. 
rewrite ideq. rewrite get_set_sameE. trivial. 
rewrite get_set_neqE; first by assumption. smt(). 
case(id4 = id{2}) => ideq. 
rewrite ideq. rewrite get_set_sameE. trivial. 
rewrite get_set_neqE; first by assumption. smt(). 
 
(* Rest of the properties *)
case (b5.`1.`1 = id{2}) => ideq. 
have H36 : b5.`1 = oget BP.pubmap{2}.[id{2}] by smt().   
rewrite H36. simplify. 
case (b5.`2 = ev{2}); first smt(). move => evneq. 
right. smt(). 
have H36 : b5.`1 <> oget BP.pubmap{2}.[id{2}]. 
have H37 : (oget BP.pubmap{2}.[id{2}]).`1 = id{2}. 
rewrite H15. rewrite H14. rewrite in_fsetU. 
left. apply H10. trivial. smt(). 
have ? : b5 \in ((oget BP.pubmap{2}.[id{2}], ev{2}) :: rem_ids BP.bb0{2})
         by smt(@List). 
have ? : b5 <> ((oget BP.pubmap{2}.[id{2}], ev{2})) by smt(). 
simplify => /#. smt().  

case (b5.`1.`1 = id{2}) => ideq. 
have H36 : b5.`1 = oget BP.pubmap{2}.[id{2}] by smt().   
rewrite H36. simplify. 
case (b5.`2 = ev0{2}); first by smt(). 
move => evneq. 
right. smt(). 
have H36 : b5.`1 <> oget BP.pubmap{2}.[id{2}]. 
have H37 : (oget BP.pubmap{2}.[id{2}]).`1 = id{2}. 
rewrite H15. rewrite H14. rewrite in_fsetU.  
left. apply H10. trivial. smt(). 
have ? : b5 \in ((oget BP.pubmap{2}.[id{2}], ev0{2}) :: rem_ids BP.bb1{2}) 
         by smt(@List). 
have ? : b5 <> ((oget BP.pubmap{2}.[id{2}], ev0{2})) by smt(). 
simplify => /#. smt(). 

elim H21 => H36. 
have ? : (oget BP.pubmap{2}.[id{2}]).`1 = id{2}. 
rewrite H15. rewrite H14. rewrite in_fsetU.  
left. apply H10. trivial. 
smt(). rewrite H18. rewrite H36.  trivial. 

case (b5.`1 = id{2}) => ideq. 
have ? : b5.`2 = oget BP.pubmap{2}.[id{2}] by smt(). 
case (b5.`3 = ev0{2}); first by smt(). 
move =>  cneq. 
 have H36 : b5 \in BP.bb1{2} by smt(). 
have H37 : (b5.`2, b5.`3) \in (rem_ids BP.bb1{2}) by smt(). 
have ? : index b5 BP.bb1{2} = 
         index (b5.`2, b5.`3) (rem_ids BP.bb1{2}) by smt(). 
have ? : b5 <> (id{2}, oget BP.pubmap{2}.[id{2}], ev0{2}) by smt(). 
have ? : (b5.`2, b5.`3) <> (oget BP.pubmap{2}.[id{2}], ev0{2}) by smt(). 
have -> : index b5 ((id{2}, oget BP.pubmap{2}.[id{2}], ev0{2}) :: BP.bb1{2}) = 
          index b5 BP.bb1{2} + 1 by smt(@List). 
rewrite H19. rewrite H36. 
have -> : index (b5.`2, b5.`3)
          (rem_ids ((id{2}, oget BP.pubmap{2}.[id{2}], ev0{2}) :: BP.bb1{2})) = 
          index (b5.`2, b5.`3) (rem_ids BP.bb1{2}) + 1.  
have -> : rem_ids ((id{2}, oget BP.pubmap{2}.[id{2}], ev0{2}) :: BP.bb1{2}) = 
          (oget BP.pubmap{2}.[id{2}], ev0{2}) :: (rem_ids BP.bb1{2}) by smt(@List). 
smt(). trivial. 
have ? : b5.`2 <> oget BP.pubmap{2}.[id{2}]. 
have ? : (oget BP.pubmap{2}.[id{2}]).`1 = id{2}.  
rewrite H15. rewrite H14. rewrite in_fsetU. 
left. apply H10. trivial.  
have ? : b5.`2.`1 = b5.`1. smt().  smt().  

have -> : index b5 ((id{2}, oget BP.pubmap{2}.[id{2}], ev0{2}) :: BP.bb1{2}) = 
            index b5 BP.bb1{2} + 1 by smt(@List). 
have -> : index (b5.`2, b5.`3) 
          (rem_ids ((id{2}, oget BP.pubmap{2}.[id{2}], ev0{2}) :: BP.bb1{2})) = 
          index (b5.`2, b5.`3) (rem_ids BP.bb1{2}) + 1. 
have -> :  rem_ids ((id{2}, oget BP.pubmap{2}.[id{2}], ev0{2}) :: BP.bb1{2}) = 
            (oget BP.pubmap{2}.[id{2}], ev0{2}) :: (rem_ids BP.bb1{2}) by smt(@List).  
smt(@List). smt(). smt(). 

proc;inline*;auto. 
proc;inline*;auto.  
by conseq So_ll2;auto;progress. 
auto;progress.  smt(). 
 
(* The validity check is fairly straight forward *)
seq 1 1 : (
 ={glob A, glob S, glob C, glob CP, glob Ev, glob Ev, glob Ve, glob HRO.ERO,
      BP.pk, BP.sk, BP.setHcheck, BP.bb0, BP.bb1, BP.bb, BP.sethappy, valid,
      BP.setchecked, BP.setH, BP.secmap, BP.secmapD, BP.pubmap, BP.setidents} /\
  BP.pk{1}.`1 = get_epk BP.sk{1}.`2 /\

  (forall id pc c, (id, pc, c) \in BP.bb0{1} => pc = oget BP.pubmap{1}.[id]) /\
    (forall id pc c, (id, pc, c) \in BP.bb1{1} => pc = oget BP.pubmap{1}.[id]) /\
  fdom BP.vmap{1} = fdom BP.vmap{2} /\

  (forall (id0 : ident), (oget (ohead (odflt [] BP.vmap{1}.[id0]))).`3 = 
    (oget (ohead (odflt [] BP.vmap{2}.[id0]))).`3) /\

  (forall (id0 : ident) (c : cipher), (id0, oget BP.pubmap{2}.[id0], c) \in BP.bb0{1} =>
     Some (oget (onth (odflt [] BP.vmap{1}.[id0]) 
                (find (fun (x : cipher * cipher * vote * vote) => x.`1 = c)
                (odflt [] BP.vmap{1}.[id0])))).`4 =
                dec_cipher_vo BP.sk{2}.`2 id0 c HRO.ERO.m{2}) /\

  (forall (i0 : int), (nth witness BP.bb0{2} i0).`1 = 
                      (nth witness BP.bb1{2} i0).`1) /\

  (forall (i0 : int), (nth witness BP.bb0{2} i0).`2 = 
                      (nth witness BP.bb1{2} i0).`2) /\

  (forall (i0 : int), (nth witness (rem_ids BP.bb0{1}) i0).`1 = 
                      (nth witness (rem_ids BP.bb1{1}) i0).`1) /\

  size BP.bb0{2} = size BP.bb1{2} /\
  
  (forall (id0 : ident) (c : cipher), (id0, oget BP.pubmap{2}.[id0], c) \in BP.bb1{2} =>
    Some (oget (onth (odflt [] BP.vmap{1}.[id0])
         (find (fun (x : cipher * cipher * vote * vote) =>
          x.`1 = (nth witness BP.bb0{2}
                 (index (id0, oget BP.pubmap{2}.[id0], c) BP.bb1{2})).`3)
                 (odflt [] BP.vmap{1}.[id0])))).`4 =
          Some (oget (onth (odflt [] BP.vmap{2}.[id0])
          (find (fun (x : cipher * cipher * vote * vote) => x.`1 = c)
         (odflt [] BP.vmap{2}.[id0])))).`4)

  /\ (forall b, b \in rem_ids BP.bb0{1} <=> (b.`1.`1, b.`1, b.`2) \in BP.bb0{1} )
  /\ (forall b, b \in rem_ids BP.bb1{1} <=> (b.`1.`1, b.`1, b.`2) \in BP.bb1{1} )

  /\ (forall b, b \in BP.bb1{2} => b.`2.`1 = b.`1)

  /\ (forall b, b \in BP.bb1{2} => 
                index b BP.bb1{2} = index (b.`2, b.`3) (rem_ids BP.bb1{2}))

  /\ (forall i, 0 <= i < size BP.bb0{1} =>
       (nth witness (rem_ids BP.bb0{2}) i).`2 = (nth witness BP.bb0{2} i).`3)

  /\ (valid{2} => forall pc c, (pc, c) \in BP.bb{2} => (oget BP.pubmap{2}.[pc.`1]) = pc)
).

inline*.  
wp;while(={i0, bb, e1, e2, e3, glob C, glob HRO.ERO, pd, BP.pubmap}
  /\ (e3{2} =>  forall j pc c, j <= i0{2} => (pc, c) \in (take j bb{2}) 
            => oget BP.pubmap{2}.[pc.`1] = pc)
).  

seq 8 8 : (
(={i0, bb, e1, e2, e3, glob C, glob HRO.ERO, pd, BP.pubmap}) /\

   (e3{2} => forall (j0 : int) (pc : ident * upkey * commitment) (c : cipher),
     j0 <= i0{2} =>
     (pc, c) \in take j0 bb{2} => oget BP.pubmap{2}.[pc.`1] = pc) /\

   ( ((id0{2}, upk0{2}, ct0{2}), ev0{2}) = nth witness bb{2} i0{2}  ) /\

  i0{1} < size bb{1} /\ 
  i0{2} < size bb{2} 
  /\ (e3{2} = (oget BP.pubmap{2}.[id0{2}] = (id0{2}, upk0{2}, ct0{2}))) 
). 

wp. 

call(_: ={glob HRO.ERO}). sim. wp. skip. progress. 
rewrite (H H3 j0 pc c). rewrite H9. rewrite H10. trivial. 
smt().  
auto;progress.  

case (j0 = i0{2} + 1) => H10; last first.  
rewrite (H H3 j0 pc c). smt(). exact H5. trivial.
case ( (pc, c) \in (take i0{2} bb{2})); first by smt(). 
move => not_in_take. 
have ? : (pc, c) = nth witness bb{2} i0{2}. 
have H11 : (pc, c) \in take (i0{2} + 1) bb{2} by smt().  
have H12 : take (i0{2}+1) bb{2} = 
           rcons (take i0{2} bb{2}) (nth witness bb{2} i0{2}). 
rewrite (take_nth witness i0{2} bb{2}). smt().  trivial. 
smt(@List). 
smt(@SmtMap @List). 

auto;progress. smt(). rewrite (H4 id00 c (oget BP.pubmap{2}.[id00])).
 exact/H18.  trivial.  
rewrite H9.  exact H18. trivial. 
rewrite (H17 H20 i0_R pc c).  trivial. smt(@List). trivial. 

(*** We now case on whether or not the board by the adversary is valid ***)
case (valid{2}). 

(* We now look at the recovery algorithm  *)

seq 3 2 : (
  ={glob A, glob S, glob C, glob CP, glob Ev, glob Ve, glob HRO.ERO, 
    BP.pubmap, BP.secmap, BP.setidents, 
    BP.sk, BP.setHcheck, rL, valid, BP.bb0, BP.bb1, BP.bb, 
    BP.sethappy, BP.setchecked, j, BP.pk}
  /\ (j{1} = 0)
  /\ (rL{1} = [])
  /\ (size BP.bb0{1} = size BP.bb1{1}) 
  /\ (fdom BP.vmap{1} = fdom BP.vmap{2})
  /\ (size BP.bb'{1} = size BP.bb{2})
  /\ (forall id, (oget (ohead (odflt [] BP.vmap{1}.[id]))).`3 = 
                 (oget (ohead (odflt [] BP.vmap{2}.[id]))).`3)

  /\ (forall (id:ident) (c:cipher), (id, oget BP.pubmap{1}.[id], c) \in BP.bb0{1} =>
          Some (oget (onth (odflt [] BP.vmap{1}.[id]) 
               (find (fun (x : cipher*cipher*vote*vote) => x.`1 = c)
               (odflt [] BP.vmap{1}.[id])))).`4
           = dec_cipher_vo BP.sk{1}.`2 id c HRO.ERO.m{1}) /\

    (forall id pc c, (id, pc, c) \in BP.bb0{1} => pc = oget BP.pubmap{1}.[id]) /\
    (forall id pc c, (id, pc, c) \in BP.bb1{1} => pc = oget BP.pubmap{1}.[id]) /\

  (forall i, !(nth witness BP.bb{2} i \in rem_ids BP.bb1{1}) => 
             nth witness BP.bb'{1} i = nth witness BP.bb{2} i)

  /\ (forall i, (nth witness BP.bb'{1} i).`1 = (nth witness BP.bb{2} i).`1)
  /\ (forall i, (nth witness BP.bb0{1} i).`1 = (nth witness BP.bb1{1} i).`1)
  /\ (forall i, (nth witness BP.bb0{1} i).`2 = (nth witness BP.bb1{1} i).`2)

  /\ (forall (id:ident) (c:cipher), (id, oget BP.pubmap{2}.[id], c) \in BP.bb1{2} =>
        Some (oget (onth (odflt [] BP.vmap{1}.[id]) (find (fun (x : cipher*cipher*vote*vote) 
         => x.`1 = (nth witness BP.bb0{2} 
                   (index (id, oget BP.pubmap{2}.[id], c) BP.bb1{2})).`3) 
                   (odflt [] BP.vmap{1}.[id])))).`4
          = Some (oget (onth (odflt [] BP.vmap{2}.[id]) 
                 (find (fun (x : cipher*cipher*vote*vote) => x.`1 = c)
                 (odflt [] BP.vmap{2}.[id])))).`4)
  
  /\ (forall i, 0 <= i < size BP.bb'{1} => (nth witness BP.bb{2} i) \in rem_ids BP.bb1{1} =>
          (nth witness BP.bb'{1} i \in rem_ids BP.bb0{1}))

  /\ (forall i, 0 <= i < size BP.bb'{1} => (nth witness BP.bb{2} i) \in rem_ids BP.bb1{1} =>
          (nth witness BP.bb'{1} i) = 
          nth witness (rem_ids BP.bb0{1}) 
                      (index (nth witness BP.bb{2} i) (rem_ids BP.bb1{2})))

  /\ (forall b, b \in rem_ids BP.bb0{1} <=> (b.`1.`1, b.`1, b.`2) \in BP.bb0{1} )
  /\ (forall b, b \in rem_ids BP.bb1{1} <=> (b.`1.`1, b.`1, b.`2) \in BP.bb1{1} )

  /\ (forall b, b \in BP.bb1{2} => b.`2.`1 = b.`1)

  /\ (forall b, b \in BP.bb1{2} => 
                index b BP.bb1{2} = index (b.`2, b.`3) (rem_ids BP.bb1{2}))

  /\ (forall i, 0 <= i < size BP.bb0{2} =>
       (nth witness (rem_ids BP.bb0{2}) i).`2 = (nth witness BP.bb0{2} i).`3)

     /\ (valid{2} => forall pc c, (pc, c) \in BP.bb{2} => (oget BP.pubmap{2}.[pc.`1]) = pc)
     /\ valid{2}

); inline*. 

(* Prepare for while loop *)
seq 5 0 : (
  ={glob A, glob S, glob C, glob CP, glob Ev, glob Ve, glob HRO.ERO, 
    BP.pubmap, BP.secmap, BP.setidents, 
    BP.sk, BP.setHcheck, valid, BP.bb0, BP.bb1,
    BP.bb, BP.sethappy, BP.setchecked, BP.pk}
    /\ (fdom BP.vmap{1} = fdom BP.vmap{2}) 
    /\ bb'{1} = [] /\ bb0{1} = rem_ids BP.bb0{1} /\ bb1{1} = rem_ids BP.bb1{1} 
    /\ bb{1} = BP.bb{1} /\ i0{1} = 0
  
    /\ (size BP.bb0{1} = size BP.bb1{1})
    /\ (fdom BP.vmap{1} = fdom BP.vmap{2})

    /\ (forall id pc c, (id, pc, c) \in BP.bb0{1} 
          => pc = oget BP.pubmap{1}.[id]) 
    /\ (forall id pc c, (id, pc, c) \in BP.bb1{1} 
          => pc = oget BP.pubmap{1}.[id]) 

    /\ (forall id, (oget (ohead (odflt [] BP.vmap{1}.[id]))).`3 = 
                   (oget (ohead (odflt [] BP.vmap{2}.[id]))).`3)

    /\ (forall (id:ident) (c:cipher), (id, oget BP.pubmap{1}.[id], c) \in BP.bb0{1} =>
          Some (oget (onth (odflt [] BP.vmap{1}.[id]) 
               (find (fun (x : cipher*cipher*vote*vote) => x.`1 = c)
               (odflt [] BP.vmap{1}.[id])))).`4 
           = dec_cipher_vo BP.sk{1}.`2 id c HRO.ERO.m{1}) 

    /\  (forall i, i < size bb'{1} => !(nth witness BP.bb{2} i \in rem_ids BP.bb1{1}) => 
             nth witness bb'{1} i = nth witness BP.bb{2} i)

    /\ (forall i, (nth witness BP.bb0{1} i).`1 = (nth witness BP.bb1{1} i).`1)
    /\ (forall i, (nth witness BP.bb0{1} i).`2 = (nth witness BP.bb1{1} i).`2)
    /\ (forall i, (nth witness (rem_ids BP.bb0{1}) i).`1 = 
                  (nth witness (rem_ids BP.bb1{1}) i).`1)

    /\ (forall (id:ident) (c:cipher), (id, oget BP.pubmap{2}.[id], c) \in BP.bb1{2} =>
        Some (oget (onth (odflt [] BP.vmap{1}.[id]) 
                   (find (fun (x : cipher*cipher*vote*vote) 
                    => x.`1 = (nth witness BP.bb0{2} 
                              (index (id, oget BP.pubmap{2}.[id], c) BP.bb1{2})).`3) 
                              (odflt [] BP.vmap{1}.[id])))).`4
       = Some (oget (onth (odflt [] BP.vmap{2}.[id]) 
              (find (fun (x : cipher*cipher*vote*vote) => x.`1 = c)
              (odflt [] BP.vmap{2}.[id])))).`4) 
  
    /\ (forall i, 0 <= i < size bb'{1} 
        => (nth witness BP.bb{2} i) \in rem_ids BP.bb1{1} =>
           (nth witness bb'{1} i \in rem_ids BP.bb0{1}))

    /\ (forall i, 0 <= i < size bb'{1} => 
                  (nth witness BP.bb{2} i) \in rem_ids BP.bb1{1} =>
          (nth witness bb'{1} i) = 
          nth witness (rem_ids BP.bb0{1}) 
                      (index (nth witness BP.bb{2} i) (rem_ids BP.bb1{2})))

    /\ (forall b, b \in rem_ids BP.bb0{1} <=> (b.`1.`1, b.`1, b.`2) \in BP.bb0{1} )
    /\ (forall b, b \in rem_ids BP.bb1{1} <=> (b.`1.`1, b.`1, b.`2) \in BP.bb1{1} )

    /\ (forall b, b \in BP.bb1{2} => b.`2.`1 = b.`1)

    /\ (forall b, b \in BP.bb1{2} => 
                index b BP.bb1{2} = index (b.`2, b.`3) (rem_ids BP.bb1{2}))

    /\ (forall i, 0 <= i < size BP.bb0{2} =>
       (nth witness (rem_ids BP.bb0{2}) i).`2 = 
       (nth witness BP.bb0{2} i).`3)

      /\ (valid{2} => forall pc c, (pc, c) \in BP.bb{2} 
                   => (oget BP.pubmap{2}.[pc.`1]) = pc)

      /\ valid{2}
).

wp;skip;progress. 
smt(@List). smt(@List). smt(@List).  

seq 1 0 : (
  ={glob A, glob S, glob C, glob CP, glob Ev, glob Ve, glob HRO.ERO, 
    BP.pubmap, BP.secmap, BP.setidents, 
    BP.sk, BP.setHcheck, valid, BP.bb0, BP.bb1, 
    BP.bb, BP.sethappy, BP.setchecked, BP.pk}

    /\ (fdom BP.vmap{1} = fdom BP.vmap{2}) 
    /\ (size bb'{1} = size BP.bb{1})
    /\ (size BP.bb0{1} = size BP.bb1{1})

    /\ (forall id pc c, (id, pc, c) \in BP.bb0{1} 
          => pc = oget BP.pubmap{1}.[id]) 
    /\  (forall id pc c, (id, pc, c) \in BP.bb1{1} 
          => pc = oget BP.pubmap{1}.[id]) 

    /\ (forall id, (oget (ohead (odflt [] BP.vmap{1}.[id]))).`3 = 
                    (oget (ohead (odflt [] BP.vmap{2}.[id]))).`3)

    /\ (forall (id:ident) (c:cipher), 
               (id, oget BP.pubmap{1}.[id], c) \in BP.bb0{1} =>
               Some (oget (onth (odflt [] BP.vmap{1}.[id]) 
                     (find (fun (x : cipher*cipher*vote*vote) => x.`1 = c)
                      (odflt [] BP.vmap{1}.[id])))).`4
                = dec_cipher_vo BP.sk{1}.`2 id c HRO.ERO.m{1}) 

    /\ (forall i, i < size bb'{1} => !(nth witness BP.bb{2} i \in rem_ids BP.bb1{1}) => 
             nth witness bb'{1} i = nth witness BP.bb{2} i)

    /\ (forall i, (nth witness bb'{1} i).`1 = (nth witness BP.bb{2} i).`1)

    /\ (forall i, (nth witness BP.bb0{1} i).`1 = (nth witness BP.bb1{1} i).`1)
    /\ (forall i, (nth witness BP.bb0{1} i).`2 = (nth witness BP.bb1{1} i).`2)
    /\ (forall i, (nth witness (rem_ids BP.bb0{1}) i).`1 = 
                  (nth witness (rem_ids BP.bb1{1}) i).`1)
         
    /\ (forall (id:ident) (c:cipher), 
               (id, oget BP.pubmap{2}.[id], c) \in BP.bb1{2} =>
               Some (oget (onth (odflt [] BP.vmap{1}.[id]) 
                    (find (fun (x : cipher*cipher*vote*vote) 
                      => x.`1 = (nth witness BP.bb0{2} 
                         (index (id, oget BP.pubmap{2}.[id], c) BP.bb1{2})).`3) 
                         (odflt [] BP.vmap{1}.[id])))).`4
             = Some (oget (onth (odflt [] BP.vmap{2}.[id]) 
                    (find (fun (x : cipher*cipher*vote*vote) => x.`1 = c)
                    (odflt [] BP.vmap{2}.[id])))).`4)

    /\ (forall i, 0 <= i < size bb'{1} 
              => (nth witness BP.bb{2} i) \in rem_ids BP.bb1{1} 
              => (nth witness bb'{1} i \in rem_ids BP.bb0{1}))

    /\ (forall i, 0 <= i < size bb'{1} 
              => (nth witness BP.bb{2} i) \in rem_ids BP.bb1{2} 
              => (nth witness bb'{1} i) = 
                 nth witness (rem_ids BP.bb0{1}) 
                             (index (nth witness BP.bb{2} i) (rem_ids BP.bb1{2})))
         

    /\ (forall b, b \in rem_ids BP.bb0{1} <=> (b.`1.`1, b.`1, b.`2) \in BP.bb0{1} )
    /\ (forall b, b \in rem_ids BP.bb1{1} <=> (b.`1.`1, b.`1, b.`2) \in BP.bb1{1} )

    /\ (forall b, b \in BP.bb1{2} => b.`2.`1 = b.`1)

    /\ (forall b, b \in BP.bb1{2} => 
                index b BP.bb1{2} = index (b.`2, b.`3) (rem_ids BP.bb1{2}))

    /\ (forall i, 0 <= i < size BP.bb0{2} =>
       (nth witness (rem_ids BP.bb0{2}) i).`2 = (nth witness BP.bb0{2} i).`3)

    /\ (valid{2} => forall pc c, (pc, c) \in BP.bb{2} 
           => (oget BP.pubmap{2}.[pc.`1]) = pc)
       
    /\ valid{2}
).


while{1} (
  ={BP.bb, BP.bb0, BP.bb1} /\ 0 <= i0{1} <= size bb{1} /\ size bb'{1} = i0{1}
  /\ (size BP.bb0{1} = size BP.bb1{1})
  /\ (bb0{1} = rem_ids BP.bb0{1})
  /\ (bb1{1} = rem_ids BP.bb1{1})
  /\ (bb{1}  = BP.bb{1} )


  /\ (forall i, i < size bb'{1} 
       => !nth witness BP.bb{2} i \in rem_ids BP.bb1{1} 
       => nth witness bb'{1} i = nth witness BP.bb{2} i) 

  /\ (forall i, (nth witness BP.bb0{1} i).`1 = (nth witness BP.bb1{1} i).`1)
  /\ (forall i, (nth witness BP.bb0{1} i).`2 = (nth witness BP.bb1{1} i).`2)
  /\ (forall i, (nth witness (rem_ids BP.bb0{1}) i).`1 = 
                (nth witness (rem_ids BP.bb1{1}) i).`1)

  /\ (forall i, i < size bb'{1} => (nth witness bb'{1} i).`1 = 
                                   (nth witness BP.bb{2} i).`1)

  /\ (forall i, 0 <= i < size bb'{1} 
       => (nth witness BP.bb{2} i) \in rem_ids BP.bb1{1} 
       => (nth witness bb'{1} i \in rem_ids BP.bb0{1}))

  /\ (forall i, 0 <= i < size bb'{1} 
       => (nth witness BP.bb{2} i) \in rem_ids BP.bb1{1} 
       => (nth witness bb'{1} i) = nth witness (rem_ids BP.bb0{1}) 
          (index (nth witness BP.bb{2} i) (rem_ids BP.bb1{2})))
) 
(size bb{1} - i0{1});progress.
  
sp 1. if => //;wp. 
skip;progress; first smt(size_ge0). smt(). 
by rewrite cats1 size_rcons. 
rewrite nth_cat. simplify.    
case (i1 < size bb'{hr}) => i1_size. rewrite H3. done. exact H13. done. 
case (i1 = size bb'{hr}) => i1_eq_size. have -> : i1 - size bb'{hr} = 0 by smt(). rewrite /=. smt(@List). smt(@List). 
rewrite nth_cat.  simplify. 
smt(@List).  
rewrite nth_cat. 
case (i1 < size bb'{hr}); first smt(@List). 
move => H17. 
have H18 : (i1 - size bb'{hr} = 0) by smt(@List). 
rewrite H18. simplify. smt(@List). 
rewrite nth_cat. 
case (i1 < size bb'{hr}); first smt(@List). 
move => H17. have H18 : (i1 - size bb'{hr} = 0) by smt(@List). 
rewrite H18. simplify. smt(@List). smt(). 
auto;progress. smt(size_ge0). smt(). 
by rewrite cats1 size_rcons. 
rewrite nth_cat; 1: smt(@List).  
rewrite nth_cat; 1: smt(@List). 
smt(@List). smt(@List). smt(). 
auto;progress. rewrite size_ge0. smt(@List). smt(). smt(). smt(@List). 
auto;progress. smt(@List). 
 
seq 3 3 : (
  ={glob A, glob S, glob C, glob CP, glob Ev, glob HRO.ERO, glob Ve, 
    BP.sk, BP.setHcheck,  BP.pk, BP.setidents, 
    rL, BP.r, valid, BP.bb0, BP.bb1, BP.bb, BP.sethappy, 
    BP.setchecked, BP.pubmap, BP.secmap}
  
  /\ (fdom BP.vmap{1} = fdom BP.vmap{2})

  /\ (forall id, (oget (ohead (odflt [] BP.vmap{1}.[id]))).`3 = 
                 (oget (ohead (odflt [] BP.vmap{2}.[id]))).`3)

  /\ (valid{2} => forall pc c, (pc, c) \in BP.bb{2} 
               => (oget BP.pubmap{2}.[pc.`1]) = pc)

  /\ valid{2}
);first last. 

if => //; first smt(). 
rnd;skip;progress. 

rcondf{1} 1;progress. rcondf{2} 1;progress. 
 
seq 13 13 : (((={glob A, glob S, glob C, glob CP, glob Ev, glob HRO.ERO, 
                BP.bbstar, valid', BP.pk, BP.setidents, 
                glob Ve, BP.sk, BP.setHcheck, BP.pi', rL, BP.r, valid, 
                BP.bb0, BP.pubmap, BP.secmap,
                BP.bb1, BP.bb, BP.sethappy, BP.setchecked, da} /\
    fdom BP.vmap{1} = fdom BP.vmap{2} /\
    forall (id0 : ident),
      (oget (ohead (odflt [] BP.vmap{1}.[id0]))).`3 =
      (oget (ohead (odflt [] BP.vmap{2}.[id0]))).`3) /\
   ! ! (BP.setHcheck{1} \subset fdom BP.vmap{1})) /\
  ! !valid{1}
).

inline*;wp;call(_: ={glob S}); first by conseq So_ll2. 
wp;call(_: ={glob HRO.ERO, glob S, BP.bb0, BP.bb1});
             [proc;inline*;auto | sim | sim | auto;progress]. 
call(_: ={glob HRO.ERO, glob S}); [1..2: by sim].
call(_:true).  
auto;progress. 

if => //; first rnd;progress. 

seq 1 1 : (
  (((={glob A, glob S, glob C, glob CP, glob Ev, glob HRO.ERO, 
       BP.d, BP.pubmap, BP.secmap, BP.setidents, 
         BP.bbstar, valid', BP.pk, glob Ve, BP.sk, 
         BP.setHcheck, BP.pi', rL,
         BP.r, valid, BP.bb0, BP.bb1, BP.bb, BP.sethappy, 
         BP.setchecked, da} /\
     fdom BP.vmap{1} = fdom BP.vmap{2} /\
     forall (id0 : ident),
       (oget (ohead (odflt [] BP.vmap{1}.[id0]))).`3 =
       (oget (ohead (odflt [] BP.vmap{2}.[id0]))).`3) /\
    ! ! (BP.setHcheck{1} \subset fdom BP.vmap{1})) /\
   ! !valid{1}) /\
  ! !valid'{1}
).
call(_: ={glob HRO.ERO, glob S, glob CP, BP.setchecked, BP.sethappy, 
          BP.setHcheck, BP.bbstar, BP.bb, BP.pubmap, BP.secmap, BP.setidents}
  /\ forall (id0 : ident), (oget (ohead (odflt [] BP.vmap{1}.[id0]))).`3 = 
                           (oget (ohead (odflt [] BP.vmap{2}.[id0]))).`3
). 
proc;inline*.

 if =>//.

seq 15 15 : (
  ={glob HRO.ERO, glob S, glob CP, BP.setchecked, BP.sethappy, 
    BP.setHcheck, BP.bbstar, BP.bb, BP.pubmap, BP.secmap, ok, BP.setidents,  
    tr, sc, pc, rp, bb, id0, id} 
  /\ forall (id0 : ident), (oget (ohead (odflt [] BP.vmap{1}.[id0]))).`3 = 
                           (oget (ohead (odflt [] BP.vmap{2}.[id0]))).`3
).

wp. call(_:true);wp;skip;progress;smt(). 
if => //; first wp;skip;progress. 
proc;auto. 
by conseq So_ll2. 
auto;progress. 
if => //. sp 1 1. 
if => //; first rnd.  
auto;progress. 
if => //; first rnd;progress. 

(** We are now ready for the tally **)
wp;rnd. 
while(
  ={j, glob HRO.ERO, glob Ev, rL, BP.sk, BP.pk, BP.bb0, BP.bb1, BP.pubmap} 
  /\ 0 <= j{1}
  /\ (size BP.bb'{1} = size BP.bb{2}) /\ size BP.bb0{2} = size BP.bb1{2}
  
  /\ (forall id pc c, (id, pc, c) \in BP.bb0{1} => pc = oget BP.pubmap{1}.[id])
  /\ (forall id pc c, (id, pc, c) \in BP.bb1{1} => pc = oget BP.pubmap{1}.[id])
  
  /\ (forall (id:ident) (c:cipher), 
        (id, oget BP.pubmap{1}.[id], c) \in BP.bb0{1} =>
        Some (oget (onth (odflt [] BP.vmap{1}.[id]) 
             (find (fun (x : cipher*cipher*vote*vote) => x.`1 = c)
             (odflt [] BP.vmap{1}.[id])))).`4
         = dec_cipher_vo BP.sk{1}.`2 id c HRO.ERO.m{1}) 

  /\ (forall i, ! nth witness BP.bb{2} i \in rem_ids BP.bb1{1} => 
         nth witness BP.bb'{1} i = nth witness BP.bb{2} i) 

  /\ (forall i, !((nth witness BP.bb{2} i).`1.`1, 
                  (nth witness BP.bb{2} i).`1, 
                  (nth witness BP.bb{2} i).`2) \in BP.bb1{1} =>
         nth witness BP.bb'{1} i = nth witness BP.bb{2} i) 

  /\ (forall i, (nth witness BP.bb'{1} i).`1 = (nth witness BP.bb{2} i).`1)

  /\ (forall (id0 : ident) (c : cipher), 
             (id0, oget BP.pubmap{2}.[id0], c) \in BP.bb1{2} =>
              Some (oget (onth (odflt [] BP.vmap{1}.[id0]) 
                   (find (fun (x : cipher * cipher * vote * vote) =>
                    x.`1 = (nth witness BP.bb0{2} 
                           (index (id0, oget BP.pubmap{2}.[id0], c) BP.bb1{2})).`3)
                           (odflt [] BP.vmap{1}.[id0])))).`4 =
              Some (oget (onth (odflt [] BP.vmap{2}.[id0]) 
                         (find (fun (x : cipher * cipher * vote * vote) => x.`1 = c)
                (odflt [] BP.vmap{2}.[id0])))).`4)

  /\ (forall i, 0 <= i && i < size BP.bb'{1} =>
        nth witness BP.bb{2} i \in rem_ids BP.bb1{1} =>
        nth witness BP.bb'{1} i \in rem_ids BP.bb0{1})

  /\ (forall i, 0 <= i < size BP.bb'{1} 
          => nth witness BP.bb{2} i \in rem_ids BP.bb1{2} 
          => (nth witness BP.bb'{1} i) = 
        nth witness (rem_ids BP.bb0{1}) 
                    (index (nth witness BP.bb{2} i) (rem_ids BP.bb1{2})))

  /\ (forall b, b \in rem_ids BP.bb0{1} <=> (b.`1.`1, b.`1, b.`2) \in BP.bb0{1} )
  /\ (forall b, b \in rem_ids BP.bb1{1} <=> (b.`1.`1, b.`1, b.`2) \in BP.bb1{1} )

  /\ (forall b, b \in BP.bb1{2} => b.`2.`1 = b.`1)

  /\ (forall b, b \in BP.bb1{2} => 
       index b BP.bb1{2} = index (b.`2, b.`3) (rem_ids BP.bb1{2}))

  /\ (forall i, 0 <= i < size BP.bb0{2}  =>
       (nth witness (rem_ids BP.bb0{2}) i).`2 = 
       (nth witness BP.bb0{2} i).`3)

  /\ (valid{2} => forall pc c, (pc, c) \in BP.bb{2} 
       => (oget BP.pubmap{2}.[pc.`1]) = pc)
 
  /\ valid{2}
).
 
wp;sp.  
if{1}; last first. if{2}; last first. 
call(_: ={glob HRO.ERO}); first by sim. 
auto;progress => /#.    

exists* (glob Ev){1}, BP.sk{1}, id{1}, ev{1}; elim* => gev sk id ev. 
call{1}(Edec_Odec_vo gev sk.`2 id ev). auto;progress. 
 
rewrite H7. rewrite -H8; first smt(). 
rewrite H10. smt(). smt(@List). smt(@List).  
smt(). smt(). smt(). smt().  

if{2} => //;last first. 
exists* (glob Ev){2}, BP.sk{2}, id{2}, ev{2}; elim* => gev sk id ev. 
call{2}(Edec_Odec_vo gev sk.`2 id ev). auto;progress. 
   
have H32 : 0 <= j{2} && j{2} < size BP.bb'{1} by smt(). 
rewrite H6. smt(@List).  
have H33 : (oget BP.pubmap{2}.[(nth witness BP.bb'{1} j{2}).`1.`1], 
           (nth witness BP.bb'{1} j{2}).`2) \in rem_ids BP.bb0{2}.  
have H34 : nth witness BP.bb'{1} j{2} = 
          ((nth witness BP.bb'{1} j{2}).`1, (nth witness BP.bb'{1} j{2}).`2) by smt(). 
have H35 : rem_id ((nth witness BP.bb'{1} j{2}).`1.`1, (nth witness BP.bb'{1} j{2}).`1,
      (nth witness BP.bb'{1} j{2}).`2) = ( (nth witness BP.bb'{1} j{2}).`1,
      (nth witness BP.bb'{1} j{2}).`2) by smt().  
smt(@List). 

rewrite -H4 => /#.   

auto;progress => /#. smt(). smt(). 
auto;progress. smt(). 
auto;progress.  

have ? : ( (nth witness BP.bb{2} j{2}).`1.`1, 
           (nth witness BP.bb{2} j{2}).`1, 
           (nth witness BP.bb{2} j{2}).`2) \in BP.bb1{2} by smt(@List). 
have H32 : nth witness BP.bb'{1} j{2} = 
           nth witness (rem_ids BP.bb0{2}) 
                       (index (nth witness BP.bb{2} j{2}) 
                       (rem_ids BP.bb1{2})). smt(). 
have <- : (nth witness BP.bb'{1} j{2}).`1.`1 = 
          (nth witness BP.bb{2} j{2}).`1.`1 by smt(). 
rewrite -H8. rewrite H7 H21.  
 rewrite H7. rewrite H10. smt(). smt(). 
pose id := (nth witness BP.bb{2} j{2}).`1.`1. 
have -> : oget BP.pubmap{2}.[id] = (nth witness BP.bb{2} j{2}).`1 by smt(). 

have H33 : forall id c, (id, oget BP.pubmap{2}.[id], c) \in BP.bb1{2} => 
                index (id, oget BP.pubmap{2}.[id], c) BP.bb1{2} = 
                index (oget BP.pubmap{2}.[id], c) (rem_ids BP.bb1{2}) by smt(). 
have -> :  ((nth witness BP.bb{2} j{2}).`1.`1,
                    (nth witness BP.bb{2} j{2}).`1,
                    (nth witness BP.bb{2} j{2}).`2).`2 = 
                    (nth witness BP.bb{2} j{2}).`1 by smt(). 
have -> : ((nth witness BP.bb{2} j{2}).`1.`1,
                    (nth witness BP.bb{2} j{2}).`1,
                    (nth witness BP.bb{2} j{2}).`2).`3 = 
                    (nth witness BP.bb{2} j{2}).`2 by smt().     
rewrite H15. smt(@List). 
rewrite H14. smt().  
 
have -> : ((id, (nth witness BP.bb{2} j{2}).`1, 
                (nth witness BP.bb{2} j{2}).`2).`2 = 
          (nth witness BP.bb{2} j{2}).`1) by auto. 
have -> : ((id, (nth witness BP.bb{2} j{2}).`1, 
                (nth witness BP.bb{2} j{2}).`2).`3 = 
          (nth witness BP.bb{2} j{2}).`2) by auto. 

have -> : ((nth witness BP.bb{2} j{2}).`1,
           (nth witness BP.bb{2} j{2}).`2) = 
          nth witness BP.bb{2} j{2} by smt(). trivial => /#. 
smt(). smt(). smt(). smt().  
auto;progress => /#. 

(** The case where the board is not valid **)
seq 6 5 : (={BP.setHcheck, glob HRO.ERO, glob S, glob A, valid} 
           /\ fdom BP.vmap{1} = fdom BP.vmap{2} /\ !valid{2});last first. 
if => //; first by smt(). 
rnd;skip;progress. 
rcondt{1} 1;progress. rcondt{2} 1;progress. 
rnd;progress. 

conseq (_: _ ==>  (={BP.setHcheck, glob HRO.ERO, glob S, glob A, valid} 
             /\ fdom BP.vmap{1} = fdom BP.vmap{2} /\ !valid{2})). 
wp;rnd{1};rnd{2}.  
conseq (_: _ ==>  (={BP.setHcheck, glob HRO.ERO, glob S, glob A, valid} 
             /\ fdom BP.vmap{1} = fdom BP.vmap{2} /\ !valid{2})). progress.  
apply duni_ap_ll. apply duni_ap_ll.  


(*** Recovery alorithm ***)
seq 3 2 : (
  ={glob A, glob S, glob C, glob CP, glob Ev, glob Ve, glob HRO.ERO, 
    BP.pubmap, BP.secmap, BP.setidents, 
    BP.sk, BP.setHcheck, rL, valid, BP.bb0, BP.bb1, 
    BP.bb, BP.sethappy, BP.setchecked, j, BP.pk}
  /\ (j{1} = 0)
  /\ (rL{1} = [])
  /\ (size BP.bb0{1} = size BP.bb1{1}) 
  /\ (fdom BP.vmap{1} = fdom BP.vmap{2})
  /\ (size BP.bb'{1} = size BP.bb{2})
  /\ (forall id, (oget (ohead (odflt [] BP.vmap{1}.[id]))).`3 = 
                 (oget (ohead (odflt [] BP.vmap{2}.[id]))).`3)

  /\ (forall (id:ident) (c:cipher), 
             (id, oget BP.pubmap{1}.[id], c) \in BP.bb0{1} =>
             Some (oget (onth (odflt [] BP.vmap{1}.[id]) 
                   (find (fun (x : cipher*cipher*vote*vote) => x.`1 = c)
                   (odflt [] BP.vmap{1}.[id])))).`4
             = dec_cipher_vo BP.sk{1}.`2 id c HRO.ERO.m{1}) /\

    (forall id pc c, (id, pc, c) \in BP.bb0{1}
      => pc = oget BP.pubmap{1}.[id]) /\
    (forall id pc c, (id, pc, c) \in BP.bb1{1} 
      => pc = oget BP.pubmap{1}.[id]) /\

  (forall i, !(nth witness BP.bb{2} i \in rem_ids BP.bb1{1}) => 
             nth witness BP.bb'{1} i = nth witness BP.bb{2} i)

  /\ (forall i, (nth witness BP.bb'{1} i).`1 = (nth witness BP.bb{2} i).`1)
  /\ (forall i, (nth witness BP.bb0{1} i).`1 = (nth witness BP.bb1{1} i).`1)
  /\ (forall i, (nth witness BP.bb0{1} i).`2 = (nth witness BP.bb1{1} i).`2)

  /\ (forall (id:ident) (c:cipher), 
       (id, oget BP.pubmap{2}.[id], c) \in BP.bb1{2} =>
        Some (oget (onth (odflt [] BP.vmap{1}.[id]) 
             (find (fun (x : cipher*cipher*vote*vote) 
              => x.`1 = (nth witness BP.bb0{2} 
                        (index (id, oget BP.pubmap{2}.[id], c) BP.bb1{2})).`3) 
                        (odflt [] BP.vmap{1}.[id])))).`4
              = Some (oget (onth (odflt [] BP.vmap{2}.[id]) 
                     (find (fun (x : cipher*cipher*vote*vote) => x.`1 = c)
                     (odflt [] BP.vmap{2}.[id])))).`4)
  
  /\ (forall i, 0 <= i < size BP.bb'{1} 
       => (nth witness BP.bb{2} i) \in rem_ids BP.bb1{1} 
       => (nth witness BP.bb'{1} i \in rem_ids BP.bb0{1}))

  /\ (forall i, 0 <= i < size BP.bb'{1} 
       => (nth witness BP.bb{2} i) \in rem_ids BP.bb1{1} 
       => (nth witness BP.bb'{1} i) = 
           nth witness (rem_ids BP.bb0{1}) 
           (index (nth witness BP.bb{2} i) (rem_ids BP.bb1{2})))

  /\ (forall b, b \in rem_ids BP.bb0{1} <=> (b.`1.`1, b.`1, b.`2) \in BP.bb0{1} )
  /\ (forall b, b \in rem_ids BP.bb1{1} <=> (b.`1.`1, b.`1, b.`2) \in BP.bb1{1} )

  /\ (forall b, b \in BP.bb1{2} => b.`2.`1 = b.`1)

  /\ (forall b, b \in BP.bb1{2} => 
                index b BP.bb1{2} = index (b.`2, b.`3) (rem_ids BP.bb1{2}))

   /\ (forall i, 0 <= i < size BP.bb0{2} =>
       (nth witness (rem_ids BP.bb0{2}) i).`2 = 
       (nth witness BP.bb0{2} i).`3)
   
   /\ !valid{2}

); inline*. 

(* Prepare for while loop *)
seq 5 0 : (
  ={glob A, glob S, glob C, glob CP, glob Ev, glob Ve, glob HRO.ERO, 
    BP.pubmap, BP.secmap, BP.setidents, 
    BP.sk, BP.setHcheck, valid, BP.bb0, BP.bb1, 
    BP.bb, BP.sethappy, BP.setchecked, BP.pk}
    
    /\ (fdom BP.vmap{1} = fdom BP.vmap{2}) 
    /\ bb'{1} = [] /\ bb0{1} = rem_ids BP.bb0{1} /\ bb1{1} = rem_ids BP.bb1{1} 
    /\ bb{1} = BP.bb{1} /\ i0{1} = 0
  
    /\ (size BP.bb0{1} = size BP.bb1{1})
    /\ (fdom BP.vmap{1} = fdom BP.vmap{2})

    /\ (forall id pc c, (id, pc, c) \in BP.bb0{1} 
          => pc = oget BP.pubmap{1}.[id]) 
    /\  (forall id pc c, (id, pc, c) \in BP.bb1{1} 
          => pc = oget BP.pubmap{1}.[id]) 

    /\ (forall id, (oget (ohead (odflt [] BP.vmap{1}.[id]))).`3 = 
                   (oget (ohead (odflt [] BP.vmap{2}.[id]))).`3)

    /\ (forall (id:ident) (c:cipher), 
               (id, oget BP.pubmap{1}.[id], c) \in BP.bb0{1} =>
               Some (oget (onth (odflt [] BP.vmap{1}.[id]) 
                    (find (fun (x : cipher*cipher*vote*vote) => x.`1 = c)
                    (odflt [] BP.vmap{1}.[id])))).`4 
              = dec_cipher_vo BP.sk{1}.`2 id c HRO.ERO.m{1}) 

    /\  (forall i, i < size bb'{1} 
           => !(nth witness BP.bb{2} i \in rem_ids BP.bb1{1}) 
           =>   nth witness bb'{1} i = nth witness BP.bb{2} i)

    /\ (forall i, (nth witness BP.bb0{1} i).`1 = 
                  (nth witness BP.bb1{1} i).`1)
    /\ (forall i, (nth witness BP.bb0{1} i).`2 = 
                  (nth witness BP.bb1{1} i).`2)
    /\ (forall i, (nth witness (rem_ids BP.bb0{1}) i).`1 = 
                  (nth witness (rem_ids BP.bb1{1}) i).`1)

    /\ (forall (id:ident) (c:cipher), 
               (id, oget BP.pubmap{2}.[id], c) \in BP.bb1{2} =>
                Some (oget (onth (odflt [] BP.vmap{1}.[id]) 
                     (find (fun (x : cipher*cipher*vote*vote) 
                     => x.`1 = (nth witness BP.bb0{2} 
                               (index (id, oget BP.pubmap{2}.[id], c) BP.bb1{2})).`3) 
                               (odflt [] BP.vmap{1}.[id])))).`4
               = Some (oget (onth (odflt [] BP.vmap{2}.[id]) 
                      (find (fun (x : cipher*cipher*vote*vote) => x.`1 = c)
                      (odflt [] BP.vmap{2}.[id])))).`4) 
  
    /\ (forall i, 0 <= i < size bb'{1} 
            => (nth witness BP.bb{2} i) \in rem_ids BP.bb1{1} 
            => (nth witness bb'{1} i \in rem_ids BP.bb0{1}))

    /\ (forall i, 0 <= i < size bb'{1} 
            => (nth witness BP.bb{2} i) \in rem_ids BP.bb1{1} 
            => (nth witness bb'{1} i) = 
                nth witness (rem_ids BP.bb0{1}) 
                            (index (nth witness BP.bb{2} i) 
                            (rem_ids BP.bb1{2})))

    /\ (forall b, b \in rem_ids BP.bb0{1} <=> (b.`1.`1, b.`1, b.`2) \in BP.bb0{1} )
    /\ (forall b, b \in rem_ids BP.bb1{1} <=> (b.`1.`1, b.`1, b.`2) \in BP.bb1{1} )

    /\ (forall b, b \in BP.bb1{2} => b.`2.`1 = b.`1)

    /\ (forall b, b \in BP.bb1{2} => 
                index b BP.bb1{2} = index (b.`2, b.`3) (rem_ids BP.bb1{2}))

    /\ (forall i, 0 <= i < size BP.bb0{2} =>
       (nth witness (rem_ids BP.bb0{2}) i).`2 = (nth witness BP.bb0{2} i).`3)
    
    /\ !valid{2}
).

wp;skip;progress. smt(@List). smt(@List). smt(@List).  

seq 1 0 : (
  ={glob A, glob S, glob C, glob CP, glob Ev, glob Ve, glob HRO.ERO, 
    BP.pubmap, BP.secmap, BP.setidents, 
    BP.sk, BP.setHcheck, valid, BP.bb0, BP.bb1, 
    BP.bb, BP.sethappy, BP.setchecked, BP.pk}

    /\ (fdom BP.vmap{1} = fdom BP.vmap{2}) 
    /\ (size bb'{1} = size BP.bb{1})
    /\ (size BP.bb0{1} = size BP.bb1{1})

    /\ (forall id pc c, (id, pc, c) \in BP.bb0{1} 
          => pc = oget BP.pubmap{1}.[id]) 
    /\  (forall id pc c, (id, pc, c) \in BP.bb1{1} 
          => pc = oget BP.pubmap{1}.[id]) 

    /\ (forall id, (oget (ohead (odflt [] BP.vmap{1}.[id]))).`3 = 
                   (oget (ohead (odflt [] BP.vmap{2}.[id]))).`3)

    /\ (forall (id:ident) (c:cipher), 
               (id, oget BP.pubmap{1}.[id], c) \in BP.bb0{1} =>
               Some (oget (onth (odflt [] BP.vmap{1}.[id]) 
                          (find (fun (x : cipher*cipher*vote*vote) => x.`1 = c)
                          (odflt [] BP.vmap{1}.[id])))).`4
             = dec_cipher_vo BP.sk{1}.`2 id c HRO.ERO.m{1}) 

    /\ (forall i, i < size bb'{1} 
         => !(nth witness BP.bb{2} i \in rem_ids BP.bb1{1}) 
         =>   nth witness bb'{1} i = nth witness BP.bb{2} i)

    /\ (forall i, (nth witness bb'{1} i).`1 = 
                  (nth witness BP.bb{2} i).`1)

    /\ (forall i, (nth witness BP.bb0{1} i).`1 = 
                  (nth witness BP.bb1{1} i).`1)
    /\ (forall i, (nth witness BP.bb0{1} i).`2 = 
                  (nth witness BP.bb1{1} i).`2)
    /\ (forall i, (nth witness (rem_ids BP.bb0{1}) i).`1 = 
                  (nth witness (rem_ids BP.bb1{1}) i).`1)
         
    /\ (forall (id:ident) (c:cipher), 
               (id, oget BP.pubmap{2}.[id], c) \in BP.bb1{2} =>
               Some (oget (onth (odflt [] BP.vmap{1}.[id]) 
                    (find (fun (x : cipher*cipher*vote*vote) 
                => x.`1 = (nth witness BP.bb0{2} 
                          (index (id, oget BP.pubmap{2}.[id], c) BP.bb1{2})).`3) 
                          (odflt [] BP.vmap{1}.[id])))).`4
              = Some (oget (onth (odflt [] BP.vmap{2}.[id]) 
                     (find (fun (x : cipher*cipher*vote*vote) => x.`1 = c)
                     (odflt [] BP.vmap{2}.[id])))).`4)

    /\ (forall i, 0 <= i < size bb'{1} 
           => (nth witness BP.bb{2} i) \in rem_ids BP.bb1{1} 
           => (nth witness bb'{1} i \in rem_ids BP.bb0{1}))

    /\ (forall i, 0 <= i < size bb'{1} 
           => (nth witness BP.bb{2} i) \in rem_ids BP.bb1{2} 
           => (nth witness bb'{1} i) = 
               nth witness (rem_ids BP.bb0{1}) 
                           (index (nth witness BP.bb{2} i) 
                           (rem_ids BP.bb1{2})))
         

    /\ (forall b, b \in rem_ids BP.bb0{1} <=> (b.`1.`1, b.`1, b.`2) \in BP.bb0{1} )
    /\ (forall b, b \in rem_ids BP.bb1{1} <=> (b.`1.`1, b.`1, b.`2) \in BP.bb1{1} )

    /\ (forall b, b \in BP.bb1{2} => b.`2.`1 = b.`1)

    /\ (forall b, b \in BP.bb1{2} => 
                index b BP.bb1{2} = index (b.`2, b.`3) (rem_ids BP.bb1{2}))

    /\ (forall i, 0 <= i < size BP.bb0{2} =>
       (nth witness (rem_ids BP.bb0{2}) i).`2 = (nth witness BP.bb0{2} i).`3)

    /\ !valid{2}
).

while{1} (
  ={BP.bb, BP.bb0, BP.bb1} /\ 0 <= i0{1} <= size bb{1} /\ size bb'{1} = i0{1}
  /\ (size BP.bb0{1} = size BP.bb1{1})
  /\ (bb0{1} = rem_ids BP.bb0{1})
  /\ (bb1{1} = rem_ids BP.bb1{1})
  /\ (bb{1}  = BP.bb{1} )


  /\ (forall i, i < size bb'{1} => !nth witness BP.bb{2} i \in rem_ids BP.bb1{1} =>
       nth witness bb'{1} i = nth witness BP.bb{2} i) 

  /\ (forall i, (nth witness BP.bb0{1} i).`1 = (nth witness BP.bb1{1} i).`1)
  /\ (forall i, (nth witness BP.bb0{1} i).`2 = (nth witness BP.bb1{1} i).`2)
  /\ (forall i, (nth witness (rem_ids BP.bb0{1}) i).`1 = (nth witness (rem_ids BP.bb1{1}) i).`1)

  /\ (forall i, i < size bb'{1} => (nth witness bb'{1} i).`1 = (nth witness BP.bb{2} i).`1)

  /\ (forall i, 0 <= i < size bb'{1} => (nth witness BP.bb{2} i) \in rem_ids BP.bb1{1} =>
          (nth witness bb'{1} i \in rem_ids BP.bb0{1}))

  /\ (forall i, 0 <= i < size bb'{1} 
          => (nth witness BP.bb{2} i) \in rem_ids BP.bb1{1}
          => (nth witness bb'{1} i) = 
              nth witness (rem_ids BP.bb0{1}) 
                          (index (nth witness BP.bb{2} i) 
                          (rem_ids BP.bb1{2})))
) 
(size bb{1} - i0{1});progress.
sp 1. if => //;wp. 
skip;progress; first smt(size_ge0). smt(). 
by rewrite cats1 size_rcons. 
rewrite nth_cat. simplify.  
case (i1 < size bb'{hr}) => i1_size. rewrite H3. done. exact H13. done. 
case (i1 = size bb'{hr}) => i1_eq_size. have -> : i1 - size bb'{hr} = 0 by smt(). rewrite /=. smt(@List). smt(@List). 
rewrite nth_cat.  simplify. 
smt(@List).  
rewrite nth_cat. 
case (i1 < size bb'{hr}); first smt(@List). 
move => H17. 
have H18 : (i1 - size bb'{hr} = 0) by smt(@List). rewrite H18. simplify. smt(@List). 
rewrite nth_cat. 
case (i1 < size bb'{hr}); first smt(@List). 
move => H17. have H18 : (i1 - size bb'{hr} = 0) by smt(@List). 
rewrite H18. simplify. smt(@List). smt(). 
auto;progress. smt(size_ge0). smt(). 
by rewrite cats1 size_rcons. 
rewrite nth_cat; 1:smt(@List).
rewrite nth_cat; 1:smt(@List). 
rewrite nth_cat; 1:smt(@List). 
rewrite nth_cat; 1:smt(@List). smt(). 
auto;progress. rewrite size_ge0. smt(@List). smt(). smt(). smt(@List). 
auto;progress. smt(@List). 

while{1} (0 <= j{1} <= size BP.bb'{1}) (size BP.bb'{1} - j{1});progress. 
sp;wp.
if => //. auto;progress => /#.  
call(Ev_dec_ll HRO.ERO). 
proc;inline*. trivial. auto;progress => /#.  

while{2} (0 <= j{2} <= size BP.bb{2}) (size BP.bb{2} - j{2});progress. 
sp;wp. 
if => //. auto;progress => /#.  
call(Ev_dec_ll HRO.ERO). 
proc;inline*. trivial. auto;progress => /#.  

auto;progress.
rewrite size_ge0. 
smt(). 
rewrite size_ge0. 
smt(). 

qed. 

(*** We now remove one of the boards and only have one to prepare for the CCA game  ***)
local module G3R(Ev:PKEvo.Scheme, Ve:Verifier, C:ValidIndS, CP:CommitmentProtocol, 
                 A:DU_MB_BPRIV_adv, H:HOracle.Oracle, S:Simulator) = {

    var bb : (ident * (ident * upkey * commitment) * cipher) list

    module Smv = Selene(Ev,P,Ve,C,CP,H,S)

    module O = {
   
      proc h = H.o
      proc g = S.o

      proc vote_core(id, v, sl) = {
        var p, b, spr, spo;
        (p, b, spr, spo) <@ Smv.vote(BP.pk, id, oget BP.pubmap.[id], sl, v);
        return (p,b,spr,spo);
      }

      proc vote(id:ident, v0 v1 : vote) = {
      var p1, b1, s1pr, s1po;
  
      if (id \in BP.setH) {
        (p1, b1, s1pr, s1po) <@ vote_core(id, v1, oget BP.secmap.[id]);

        BP.vmap.[id] <- (b1, b1, v0, v0) :: (odflt [] BP.vmap.[id]);

        bb <- (id, oget BP.pubmap.[id], b1) :: bb;
        }
      }

      proc verify(id:ident) = {
        var ok, sv;
        if (id \in BP.setidents){
          BP.setchecked <- BP.setchecked `|` (fset1 id);
          sv <- odflt [] (BP.vmap.[id]);
           ok <@ Smv.verifyvote(id, (oget (ohead sv)).`2, (oget (ohead sv)).`3, 
                         BP.bb, BP.bbstar, oget BP.pubmap.[id], oget BP.secmap.[id]);
          if (ok) {
            BP.sethappy <- BP.sethappy `|` (fset1 id);
          }
        }
        return BP.sethappy;
      }

      proc board() = {
        return sPublish (rem_ids bb);
      } 

    }

    module A = A(O)

    proc main() : bool = {
      var i;
      var id, upk, ct, d, da, vt;
      var valid, valid';
      var rL, j, b, ev, v, tr', sv, k;

      BP.vmap       <- empty;
      BP.pubmap     <- empty;
      BP.secmap     <- empty;
      BP.secmapD    <- empty;
      G3R.bb        <- [];
      BP.setchecked <- fset0;
      BP.sethappy   <- fset0;
      
      H.init();
      S.init();
      
      (* setup *)
      (BP.pk, BP.sk) <@ Smv.setup();

      (* register *)
      i <- 0;
      while (i < card BP.setidents) {
        id  <- nth witness (elems BP.setidents) i;
         d  <- oget BP.sk.`1.[id];
        upk <- oget BP.pk.`3.`4.[id];
        ct  <- oget BP.pk.`3.`5.[id];
        BP.secmap.[id] <-  d;
        BP.pubmap.[id] <- (id, upk, ct);

        if (id \in BP.setD) {
          BP.secmapD.[id] <- oget BP.secmap.[id];
        }

        i <- i + 1;
      }

      (* adversary creates bulletin board *)
      BP.bb <@ A.create_bb(BP.pk, BP.secmapD, BP.pubmap, BP.setHcheck);

      (* check if BP.bb is valid *)
      valid <@ Smv.validboard(BP.bb, BP.pk);

      (* We now tally the  board created by the adversary *)
      rL <- [];
      j <- 0;

      while (j < size BP.bb) {
            
        b    <- nth witness BP.bb j;
        ev   <- b.`2;
        id   <- b.`1.`1;
        if ( (id, oget BP.pubmap.[id], ev) \in bb) {
          (* Get the vote from BP.vmap that mathes the ballot *)
          sv <- odflt [] BP.vmap.[id]; (* get list for voter id *)
          k  <- find (fun (x:cipher*cipher*vote*vote) => x.`1 = ev) sv; (* first index where b appears *)
          v  <- Some (oget (onth sv k)).`4; (* the vote at that index *)
        } else {
          v    <@ Ev(H).dec(BP.sk.`2, id, ev);
        }

        tr'  <@ ElGamal.dec(BP.sk.`3, oget BP.pk.`3.`3.[id]);

        rL   <- (oget v, oget tr') :: rL;

         j  <- j + 1;
      }
      
      vt   <$ (duniform (allperms rL));
      BP.r <- (unzip1 vt, unzip2 vt);

      if (!(BP.setHcheck \subset fdom BP.vmap)) {
        BP.d <$ {0,1};
      } else {
        if (!valid) {
          BP.d <$ {0,1};
        } else {
          BP.pi'    <@ S.prove(BP.pk, sPublish BP.bb, BP.r);
             da     <@ A.initial_guess();
          BP.bbstar <@ A.get_tally(BP.r, BP.pi');
          valid'    <@ Smv.verifytally((BP.pk, sPublish BP.bb, BP.bbstar.`1), BP.bbstar.`2);
          if (!valid') {
            BP.d <$ {0,1};
          } else {
            BP.d <@ A.final_guess();
            if (!(BP.setHcheck \subset BP.sethappy)) {
              BP.d <- da; 
            } 
            if (!(BP.setHcheck \subset BP.setchecked)) {
              BP.d <$ {0,1};
            }
          }
        }
      }
      return BP.d;
    }
}.

(* Prove that G2R and G3R are equivalent *)
local lemma G2R_G3R_equiv &m : 
    BP.setidents{m} = BP.setH{m} `|` BP.setD{m} =>
    Pr[G2R(Ev,Ve,C,CP,A,HRO.ERO,S).main() @ &m : res] = 
    Pr[G3R(Ev,Ve,C,CP,A,HRO.ERO,S).main() @ &m : res].
proof.  
move => ?. 
byequiv => //;proc. 

(* Everything up to creation of BP.bb *)
seq 14 13 : (
  ={glob CP, glob A, glob C, glob Ve, glob S, glob Ev, glob HRO.ERO, 
    BP.pk, BP.sk, BP.bb, BP.setidents, 
    BP.setHcheck, BP.secmapD, BP.setD, BP.setidents, 
    BP.setH, BP.vmap, BP.pubmap, BP.secmap, BP.setchecked, BP.sethappy}

  /\ (BP.pk{1}.`1 = get_epk BP.sk{1}.`2)

  /\ (G3R.bb{2} = BP.bb1{1})

  /\ (forall id pc c, (id, pc, c) \in G3R.bb{2} 
       => pc = oget BP.pubmap{2}.[id])
  /\ (forall id pc pc' c, (id, pc, c) \in G3R.bb{2} 
                       /\ (id, pc', c) \in G3R.bb{2} => pc = pc')
  
  /\ (forall id c, (id, oget BP.pubmap{2}.[id], c) \in G3R.bb{2} 
       => !(exists pc, pc <> oget BP.pubmap{2}.[id] /\ (id, pc, c) \in G3R.bb{2}))

).

call(_: 
  ={glob Ev, glob HRO.ERO, glob S, BP.setidents, BP.setH, 
    BP.pk, BP.sk, BP.secmap, BP.vmap, BP.pubmap}
  /\ (BP.bb1{1} = G3R.bb{2})
  /\ (BP.pk{1}.`1 = get_epk BP.sk{1}.`2)
  /\ (forall id pc c, (id, pc, c) \in G3R.bb{2} 
         => pc = oget BP.pubmap{2}.[id]) 
  /\ (forall id pc pc' c, (id, pc, c) \in G3R.bb{2} 
                       /\ (id, pc', c) \in G3R.bb{2} => pc = pc')
  /\ (forall id c, (id, oget BP.pubmap{2}.[id], c) \in G3R.bb{2} 
         => !(exists pc, pc <> oget BP.pubmap{2}.[id] /\ (id, pc, c) \in G3R.bb{2}))
).

proc. if => //;inline*;wp.
seq 9 0 : (
  ={id, v0, v1, glob Ev, glob HRO.ERO, BP.pk, BP.sk, glob S, BP.setidents, BP.secmap,
  BP.setH, BP.vmap, BP.pubmap}
  /\ id0{1} = id{1} /\ v{1} = v0{1} /\ pd{1} = BP.pk{1}  /\ v3{1} = v0{1}
  
  /\ BP.pk{1}.`1 = get_epk BP.sk{1}.`2

  /\ (BP.bb1{1} = G3R.bb{2})

  /\ (forall id pc c, (id, pc, c) \in G3R.bb{2} 
       => pc = oget BP.pubmap{2}.[id])

  /\ (forall id pc pc' c, (id, pc, c) \in G3R.bb{2} 
                       /\ (id, pc', c) \in G3R.bb{2} => pc = pc')

 /\ (forall id c, (id, oget BP.pubmap{2}.[id], c) \in G3R.bb{2} 
        => !(exists pc, pc <> oget BP.pubmap{2}.[id] /\ (id, pc, c) \in G3R.bb{2}))
).

exists* (glob Ev){1}; elim* => gev. 
call{1} (Ev_e_eq gev). auto;progress. 

seq 11 8 : (
  ={id, v0, v1, glob Ev, glob HRO.ERO, BP.pk, BP.sk, glob S, BP.setidents,
  BP.setH, BP.secmap, BP.vmap, BP.pubmap}

  /\ id0{1} = id{1} /\ v{1} = v0{1} /\ pd{1} = BP.pk{1} /\ BP.bb1{1} = G3R.bb{2}

  /\ v2{2} = v1{2} /\ v4{1} = v1{1} /\ id0{2} = id{2} /\ id{2} = id1{2}

  /\ BP.pk{1}.`1 = get_epk BP.sk{1}.`2

  /\ id3{1} = id{1} /\ s0po{1} = v0{1}

  /\ pd0{1} = pd{2} /\ pd{2} = BP.pk{2} 

  /\ (forall id pc c, (id, pc, c) \in G3R.bb{2} 
        => pc = oget BP.pubmap{2}.[id])

  /\ (forall id pc pc' c, (id, pc, c) \in G3R.bb{2} /\ (id, pc', c) \in G3R.bb{2} => pc = pc')

  /\ (forall id c, (id, oget BP.pubmap{2}.[id], c) \in G3R.bb{2} 
        => !(exists pc, pc <> oget BP.pubmap{2}.[id] /\ (id, pc, c) \in G3R.bb{2}))
).

auto;progress. 
exists* BP.sk{1}, pd0{1}, id3{1}, v4{1}; elim* => sk pd id v. 
pose kp := pd.`1 = get_epk sk.`2. 
have em_kp : kp \/ !kp by exact/orbN.
elim em_kp. move => h. 
call (Eenc_dec_vo sk.`2 pd.`1 id v); first by assumption. 
auto;progress => /#.   
 
move => h.  
conseq(_: _ ==> !(pd.`1 = get_epk sk.`2)). progress. 
call(_: ={glob HRO.ERO}); first by sim.   
auto;progress. 
proc;inline*;auto.
proc;inline*;auto. 
by conseq So_ll2.
while (={i, BP.setidents, glob CP, BP.secmap, BP.pubmap, BP.setD, BP.secmapD, BP.pk, BP.sk});
first by sim. 
wp;inline*.
wp;while(={i0, BP.setidents, tpk, tsk, pPk, pTr, pCo, pOp, trL, pi2}); first sim.  
wp;while(={i0, BP.setidents, trL, pTr, glob CP, pPk, tpk}); first sim. 
wp;rnd;while(={i0, BP.setidents, tpk, tpTr, trL}); first sim.   
wp;rnd;call Ev_kgen_get_epk. wp;call(_:true). 
while(={w, HRO.ERO.m}); first sim. 
auto;progress. 

(* We now do the ifs *)
(* The ifs should be more or less equivalent *)
seq 6 6 : (
  ={glob A, glob S, glob C, glob CP, glob Ev, glob HRO.ERO, glob Ve, 
    BP.sk, BP.setHcheck,  BP.pk, BP.setidents, rL, BP.r, valid, BP.bb, 
    BP.sethappy, BP.setchecked, BP.pubmap, BP.secmap, BP.vmap}
/\ BP.bb1{1} = G3R.bb{2}
);last by sim. 

(**** End of ifs ****)

(** We now tally and check if the board is valid **)
wp;rnd. 

while(={j, BP.bb, glob HRO.ERO, BP.pk, BP.sk, 
        glob Ev, rL, BP.vmap, BP.pubmap}

  /\ BP.bb1{1} = G3R.bb{2}

  /\ (forall id pc c, (id, pc, c) \in G3R.bb{2} 
         => pc = oget BP.pubmap{2}.[id])

  /\ (forall id pc pc' c, (id, pc, c) \in G3R.bb{2} 
                       /\ (id, pc', c) \in G3R.bb{2} => pc = pc')

  /\ (forall id c, (id, oget BP.pubmap{2}.[id], c) \in G3R.bb{2} 
       => !(exists pc, pc <> oget BP.pubmap{2}.[id] /\ (id, pc, c) \in G3R.bb{2}))
).

sp;wp;call(_:true); first auto. 
if{1} => //. if{2} => //. auto;progress. 

exists* (glob Ev){2}, BP.sk{2}, id{2}, ev{2}; elim* => gev sk id c. 
call{2} (Edec_Odec_vo gev sk.`2 id c). 
auto;progress.  

if{2} => //. 
exists* (glob Ev){1}, BP.sk{1}, id{1}, ev{1}; elim* => gev sk id c. 
call{1} (Edec_Odec_vo gev sk.`2 id c). 
auto;progress. 

call(_: ={glob HRO.ERO}). sim. auto;progress. 

 
inline*.  
wp;while(={i0, bb, e1, e2, e3, glob C, BP.pubmap, pd, glob HRO.ERO}). sim;progress. 
auto;progress.  
qed.  

(**** Proof that the left side IND1CCA experiment using BCCA is equivalent to G2L ****)

local lemma G2L_CCA_left_equiv &m : 
  BP.setidents{m} = BP.setH{m} `|` BP.setD{m} =>
    Pr[G2L(Ev, Ve, C, CP, A, HRO.ERO, S).main() @ &m : res] 
    = Pr[Ind1CCA(Ev,BCCA(Selene(Ev,P,Ve,C,CP),CP,A,S),HRO.ERO,Left).main() @ &m : res]. 
proof. 
move => id_union. 
byequiv => //. 
proc. 
inline*.  
swap{2} [8..13] -7. swap{2} 15 -3. swap{2} 15 -10. swap{2} [14..15] 6. 
  
(*** We start with everything before the creation of BP.bb and up to the valid check ***) 
seq 41 44 : (
  ={glob CP, glob A, glob C, glob Ve, glob S, glob Ev, 
    BP.setHcheck, BP.secmapD, BP.setD, BP.setidents, BP.pk, 
    BP.bb, valid, trL, BP.setidents, BP.setHcheck, BP.setH, 
    BP.secmapD, BP.setD, BP.sethappy, BP.setchecked,
    BP.vmap, BP.pubmap, BP.secmap, glob HRO.ERO}

    /\ (G2L.bb{1} = BCCA.bb{2})

    /\ (BP.sk{1}.`2 = BS.sk{2})
    /\ (BP.pk{2}.`1 = BS.pk{2})

    /\ (size BCCA.bb{2} = size BS.encL{2})

    /\ (!BS.decQueried{2})

    /\ (forall id pc c, (id, pc, c) \in BCCA.bb{2} => pc = oget BP.pubmap{2}.[id]) 

    /\ (forall (id:ident) (c:cipher) pc, (id, pc, c) \in BCCA.bb{2}
           => is_some BP.vmap{2}.[id])

    /\ (forall id pc c, (id, pc, c) \in BCCA.bb{2} => (c, id) \in BS.encL{2})

    /\ (BP.pk{1}.`1 = get_epk BP.sk{1}.`2)

    /\ (tsk{2} = BP.sk{1}.`3)

    /\ (forall id, id \in BP.setidents{1} => is_some BP.pubmap{1}.[id])

  /\ (forall id, is_some BP.pubmap{1}.[id] => (oget BP.pubmap{1}.[id]).`1 = id)

  /\ BP.setidents{1} = BP.setH{1} `|` BP.setD{1}

   /\ (forall id c, (c, id) \in BS.encL{2} => exists pc, (id, pc, c) \in BCCA.bb{2})

  /\ (forall id c, (id, oget BP.pubmap{2}.[id], c) \in BCCA.bb{2} <=> (c, id) \in BS.encL{2})

  /\ (forall id c, !(exists pc, (id, pc, c) \in BCCA.bb{2}) => !( (c,id) \in BS.encL{2}))

   /\ (forall (id:ident) (c:cipher) pc, (id, pc, c) \in BCCA.bb{2} =>
        Some (oget (onth (odflt [] BP.vmap{2}.[id]) 
             (find (fun (x : cipher*cipher*vote*vote) => x.`1 = c)
             (odflt [] BP.vmap{2}.[id])))).`4
         = dec_cipher_vo BS.sk{2} id c HRO.ERO.m{1}) 

  /\ (forall (id:ident) (c:cipher), (c, id) \in BS.encL{2} =>
        Some (oget (onth (odflt [] BP.vmap{2}.[id]) 
             (find (fun (x : cipher*cipher*vote*vote) => x.`1 = c)
             (odflt [] BP.vmap{2}.[id])))).`4
         = dec_cipher_vo BS.sk{2} id c HRO.ERO.m{1}) 
). 

wp. 
while ( ={e1, e2, e3, bb, glob C, glob HRO.ERO, BP.pubmap, pd} /\ i1{1} = i0{2}); first sim.  
wp. 
(*** A.a1 call ***)
call(_: 
  ={glob C, glob CP, glob Ev, glob HRO.ERO, glob S, 
    BP.pk, BP.setH, BP.vmap, BP.pubmap, BP.setidents}
 
  /\ (!BS.decQueried{2})

  /\ (G2L.bb{1} = BCCA.bb{2})

  /\ (BP.pk{1}.`1 = BS.pk{2})
  /\ (BP.sk{1}.`2 = BS.sk{2})

  /\ (size G2L.bb{1} = size BS.encL{2})

  /\ (forall id pc c, (id, pc, c) \in BCCA.bb{2} => pc = oget BP.pubmap{2}.[id]) 

  /\ (forall (id:ident) (c:cipher) pc, (id, pc, c) \in BCCA.bb{2}
           => is_some BP.vmap{2}.[id])


  /\ (forall id pc c, (id, pc, c) \in BCCA.bb{2} => (c, id) \in BS.encL{2}) 

  /\ (BP.pk{1}.`1 = get_epk BP.sk{1}.`2)

  /\ (BP.setidents{1} = BP.setH{1} `|` BP.setD{1})

  /\ (forall id, id \in BP.setidents{1} => is_some BP.pubmap{1}.[id])

  /\ (forall id, is_some BP.pubmap{1}.[id] => (oget BP.pubmap{1}.[id]).`1 = id)

  /\ (forall id pc c, (id, pc, c) \in BCCA.bb{2} => is_some BP.vmap{2}.[id])

  /\ (forall id c, (c, id) \in BS.encL{2} => is_some BP.vmap{2}.[id])

  /\ (forall id c, (c, id) \in BS.encL{2} => exists pc, (id, pc, c) \in BCCA.bb{2})

  /\ (forall id c, (id, oget BP.pubmap{2}.[id], c) \in BCCA.bb{2} <=> (c, id) \in BS.encL{2})

    /\ (forall id c, !(exists pc, (id, pc, c) \in BCCA.bb{2}) => !( (c,id) \in BS.encL{2}))

  /\ (forall (id:ident) (c:cipher) pc, (id, pc, c) \in BCCA.bb{2} =>
        Some (oget (onth (odflt [] BP.vmap{2}.[id]) 
             (find (fun (x : cipher*cipher*vote*vote) => x.`1 = c)
             (odflt [] BP.vmap{2}.[id])))).`4
         = dec_cipher_vo BS.sk{2} id c HRO.ERO.m{1}) 

  /\ (forall (id:ident) (c:cipher), (c, id) \in BS.encL{2} =>
        Some (oget (onth (odflt [] BP.vmap{2}.[id]) 
             (find (fun (x : cipher*cipher*vote*vote) => x.`1 = c)
             (odflt [] BP.vmap{2}.[id])))).`4
         = dec_cipher_vo BS.sk{2} id c HRO.ERO.m{1}) 
). 

proc. if => //. inline*. 
seq 9 6 : ( 
  ={id, v0, v1, glob C, glob CP, glob Ev, HRO.ERO.m, glob S,
    BP.pk, BP.setH, BP.vmap, BP.pubmap, BP.setidents} /\

  v2{1} = v0{1} /\ l{2} = id{2} /\

  ev{1} = c0{2} /\ pc{1} = oget BP.pubmap{1}.[id0{1}] /\ l{2} = id{2} /\ v2{1} = p{2}

  /\ !BS.decQueried{2} /\

   G2L.bb{1} = BCCA.bb{2} /\

   BP.pk{1}.`1 = BS.pk{2} /\
   BP.sk{1}.`2 = BS.sk{2} /\

   size G2L.bb{1} = size BS.encL{2} 

  /\ Some v0{2} = dec_cipher_vo BP.sk{1}.`2 id{2} c0{2} HRO.ERO.m{2}

  /\ (forall id pc c, (id, pc, c) \in BCCA.bb{2} => pc = oget BP.pubmap{2}.[id]) 

  /\ (forall (id:ident) (c:cipher) pc, (id, pc, c) \in BCCA.bb{2}
           => is_some BP.vmap{2}.[id])

  /\ (forall id pc c, (id, pc, c) \in BCCA.bb{2} => (c, id) \in BS.encL{2}) 

  /\ BP.pk{1}.`1 = get_epk BP.sk{1}.`2 /\

  (id{1} \in BP.setH{1})

  /\ (BP.setidents{1} = BP.setH{1} `|` BP.setD{1})

  /\ (forall id, id \in BP.setidents{1} => is_some BP.pubmap{1}.[id])

  /\ (forall id, is_some BP.pubmap{1}.[id] => (oget BP.pubmap{1}.[id]).`1 = id)

   /\ (forall id pc c, (id, pc, c) \in BCCA.bb{2} => is_some BP.vmap{2}.[id])

  /\ (forall id c, (c, id) \in BS.encL{2} => is_some BP.vmap{2}.[id])

  /\ (forall id c, (c, id) \in BS.encL{2} => exists pc, (id, pc, c) \in BCCA.bb{2})

 /\ (forall id c, (id, oget BP.pubmap{2}.[id], c) \in BCCA.bb{2} <=> (c, id) \in BS.encL{2})

    /\ (forall id c, !(exists pc, (id, pc, c) \in BCCA.bb{2}) => !( (c,id) \in BS.encL{2}))

   /\ (forall (id:ident) (c:cipher) pc, (id, pc, c) \in BCCA.bb{2} =>
        Some (oget (onth (odflt [] BP.vmap{2}.[id]) 
             (find (fun (x : cipher*cipher*vote*vote) => x.`1 = c)
             (odflt [] BP.vmap{2}.[id])))).`4
         = dec_cipher_vo BS.sk{2} id c HRO.ERO.m{1}) 

  /\ (forall (id:ident) (c:cipher), (c, id) \in BS.encL{2} =>
        Some (oget (onth (odflt [] BP.vmap{2}.[id]) 
             (find (fun (x : cipher*cipher*vote*vote) => x.`1 = c)
             (odflt [] BP.vmap{2}.[id])))).`4
         = dec_cipher_vo BS.sk{2} id c HRO.ERO.m{1}) 
). 

sp. 
exists* BP.sk{1}, BP.pk{1}, id1{1}, v2{1}. elim* => sk pk id v. 
pose kp := (pk.`1 = get_epk sk.`2). 
      have em_kp : kp \/ !kp by exact/orbN.   
      elim em_kp.
      move => h. 
      call (Eenc_dec_vo sk.`2 pk.`1 id v h);skip;progress.  
      move => h. 
      conseq (_: _ ==> !(BP.pk{1}.`1 = get_epk BP.sk{1}.`2)) => //.  
      call(_: ={glob HRO.ERO}); first by sim. 
      skip;progress. 
auto;progress. 
rewrite H0 size_cat addzC. 
by rewrite -size_cat cats1 size_rcons.  
smt().

smt(@SmtMap). 

 case (id2 = id{2}) => ideq.  
case (c1 = c0{2}) => ceq. rewrite mem_cat. right. by rewrite ideq ceq mem_seq1. 
have ?: (id2, pc0, c1) \in BCCA.bb{2} by smt(). 
smt(@List).  
have ?: (id2, pc0, c1) \in BCCA.bb{2} by smt(). 
smt(@List). 

case(id2 = id{2}) => ideq. rewrite get_set_eqE. rewrite ideq.  trivial. trivial. 
rewrite get_set_neqE. rewrite ideq. trivial. smt().  

case (id2 = id{2}) => ideq. 
rewrite ideq. 
rewrite get_set_eqE; first trivial. trivial.   
rewrite get_set_neqE; first trivial. smt(@List @SmtMap). 

exists (oget BP.pubmap{2}.[id2]). 
case (id2 = id{2}) => ideq.  
case (c1 = c0{2}) => ceq. 
smt(). 
have ? : (c1, id2) \in BS.encL{2} by smt(@List). 
smt(). 
have ? : (c1, id2) \in BS.encL{2} by smt(@List). 
smt(). 

smt(@List). smt(@List).

rewrite mem_cat.  
smt (@List @SmtMap). 

case(id{2} = id2) => ideq. 
case (c1 = c0{2}) => ceq. 
rewrite ideq. rewrite ceq. rewrite get_set_sameE.
smt().  
have ? : (id2, pc0, c1) \in BCCA.bb{2} by smt(). 
rewrite ideq. rewrite get_set_sameE. 
have -> : odflt [] BP.vmap{2}.[id2] = odflt [] BP.vmap{2}.[id2] by smt(). 
rewrite -(H14 id2 c1 pc0). smt(). smt(@List @SmtMap). 
have ? : (id2, pc0, c1) \in BCCA.bb{2} by smt(). 
rewrite get_set_neqE. smt(). 
rewrite -(H14 id2 c1 pc0). smt(). trivial.  

case (id{2} = id2) => ideq. 
case (c1 = c0{2}) => ceq. 
rewrite get_set_eqE; first by smt(). 
rewrite -ceq. 
smt(@SmtMap). 
have ? : (c1, id2) \in BS.encL{2} by smt(@List). 
rewrite ideq. rewrite get_set_sameE. 
have -> : odflt [] BP.vmap{2}.[id2] = odflt [] BP.vmap{2}.[id2] by smt(@SmtMap). 
rewrite -(H15 id2 c1). smt(). smt(@List @SmtMap). 
have ? : (c1, id2) \in BS.encL{2} by smt(@List). 
rewrite get_set_neqE. smt(). 
rewrite -(H15 id2 c1). smt(). trivial.  

proc;inline*;auto. 
proc;inline*;auto. 
by conseq So_ll2. 

(* Everything that happens before BP.bb is created *)

while(={i, BP.setidents, BP.secmap, BP.secmapD, BP.setD, BP.pubmap, glob CP, trL}
  /\ (BP.pk{1}.`3.`4 = pPk{2})
  /\ (BP.pk{1}.`3.`5 = pCo{2})
  /\ (BP.sk{1}.`1 = pOp{2})
  /\ (forall j id, j <= i{1} => id \in (take j (elems BP.setidents{1})) 
        => is_some BP.pubmap{1}.[id])
  /\ (forall id, is_some BP.pubmap{1}.[id] => (oget BP.pubmap{1}.[id]).`1 = id)
).
 
seq 6 6 : (
  (={i, BP.setidents, BP.pubmap, BP.secmap, BP.secmapD, BP.setD, id,
       glob CP, trL}

  /\ (BP.pk{1}.`3.`4 = pPk{2})

  /\ (BP.pk{1}.`3.`5 = pCo{2})

  /\ (BP.sk{1}.`1 = pOp{2})

  /\  (forall (j0 : int) (id0 : ident),
      j0 <= i{1} + 1 =>
      id0 \in take j0 (elems BP.setidents{1}) 
         => is_some BP.pubmap{1}.[id0]) 

  /\ forall (id0 : ident),
     is_some BP.pubmap{1}.[id0] => (oget BP.pubmap{1}.[id0]).`1 = id0) 

  /\ i{1} < card BP.setidents{1} /\ i{2} < card BP.setidents{2}
).

auto;progress.      
rewrite get_setE.   
case (id00 = nth witness (elems BP.setidents{2}) i{2}); first by trivial.  
move => id00_neq_nth.
case: (0 < j0)=> [gt0_j0|/lezNgt /take_le0<:ident> /#].
case (j0 = i{2} + 1) => h. 
+ have h1 : id00 \in take i{2} (elems BP.setidents{2}). 
  + have h2 : (take j0 (elems BP.setidents{2})) <> [] by smt(@List).
    by move: H4; rewrite h (take_nth witness) 1:/# mem_rcons /= id00_neq_nth.
  smt(@List).  
smt().
smt(@SmtMap). 
if => //;auto;progress. 
wp;while(={BP.setidents, tpk, pPk, pTr, tsk, pCo, pOp, trL, pi2} /\ i0{1} = i{2});first sim. 
wp;while(={glob CP, BP.setidents, tpk, trL, pTr, pPk} /\ i0{1} = i{2}); first sim. 
wp;rnd;while(={BP.setidents, tpk, tpTr} /\ i0{1} = i{2}); first sim. 
wp;rnd;wp;call Ev_kgen_get_epk. 
wp;call(_:true);while(={w, HRO.ERO.m});first sim. 
auto;progress. smt(@List). smt(@SmtMap). rewrite (H11 i_R2). trivial. smt(@List).


(*** If sentences are equivalent ***)
seq 5 11 : (
  ={glob HRO.ERO, glob A, glob S, glob Ve, valid, BP.setHcheck, BP.vmap, 
    BP.r, BP.bb, BP.setchecked, BP.sethappy, BP.pk, BP.secmap, BP.setidents, 
    BP.pubmap, glob CP}
  /\ (G2L.bb{1} = BCCA.bb{2})
  /\ (BP.sk{1}.`2 = BS.sk{2})
); last first. 
(*** If sentences complete ***)
wp. 
if => //; first rnd;progress. 
if => //; first rnd;progress. 

seq 13 13 : (
  ={glob HRO.ERO, glob A, glob S, glob Ve, valid, valid', BP.setHcheck, 
    BP.vmap, BP.bbstar, da, BP.pi, BP.setidents, 
    BP.r, BP.bb, BP.setchecked, BP.sethappy, BP.pk, BP.secmap, 
    BP.pubmap, glob CP}
  /\ (G2L.bb{1} = BCCA.bb{2}) /\ (BP.sk{1}.`2 = BS.sk{2})
  /\ (BP.setHcheck{1} \subset fdom BP.vmap{1})
  /\ valid{1}
).

wp;call(_: ={glob S}). by conseq So_ll2.  
wp. call(_: ={glob HRO.ERO, glob S} /\ G2L.bb{1} = BCCA.bb{2}); [1..3: by sim]. 
call(_: ={glob HRO.ERO, glob S}); [1..2: by sim]. 
call(_:true). auto;progress. 
if => //; first rnd;progress. 
seq 1 1 : (
   (={glob HRO.ERO, glob A, glob S, glob Ve, valid, valid', 
      BP.setHcheck, BP.d, da, BP.pi, BP.setidents, 
      BP.vmap, BP.r, BP.bb, BP.setchecked, BP.sethappy, BP.pk, BP.secmap, BP.bbstar,
      BP.pubmap, glob CP} /\
   G2L.bb{1} = BCCA.bb{2} /\
   BP.sk{1}.`2 = BS.sk{2} /\
   (BP.setHcheck{1} \subset fdom BP.vmap{1}) /\ valid{1}) /\
  ! !valid'{1}
).

call(_: ={glob HRO.ERO, glob S, BP.bbstar, BP.bb, BP.vmap, BP.secmap, BP.pubmap,
          glob CP, BP.setchecked, BP.sethappy, BP.setidents}); 1..3:sim.
auto;progress.  
if => //. sp 1 1. if => //; first rnd;progress. 
if => //;first rnd;progress. 

wp;rnd.

while(={j, BP.bb, rL, BP.vmap, glob HRO.ERO, BP.pk} /\ 0 <= j{2}
  /\ (BP.sk{1}.`2 = BS.sk{2})
  /\ (BP.pk{1}.`1 = BS.pk{2}) 
  /\ (G2L.bb{1} = BCCA.bb{2})
  /\ (BP.sk{1}.`3 = tsk{2})

  /\ (BP.setidents{1} = BP.setH{1} `|` BP.setD{1})

  /\ (forall id, id \in BP.setidents{1} => is_some BP.pubmap{1}.[id])

  /\ (forall id pc c, (id, pc, c) \in BCCA.bb{2} => pc = oget BP.pubmap{2}.[id]) 

  /\ (forall id, is_some BP.pubmap{1}.[id] => (oget BP.pubmap{1}.[id]).`1 = id)

  /\ (forall id c, (c, id) \in BS.encL{2} => exists pc, (id, pc, c) \in BCCA.bb{2})

  /\ (forall id pc c, (id, pc, c) \in BCCA.bb{2} => (c, id) \in BS.encL{2}) 

  /\ (forall id c, (id, oget BP.pubmap{2}.[id], c) \in BCCA.bb{2} <=> (c, id) \in BS.encL{2}) 

  /\ (forall id c, !(exists pc, (id, pc, c) \in BCCA.bb{2}) => !( (c,id) \in BS.encL{2}))

  /\ (forall (id:ident) (c:cipher) pc, (id, pc, c) \in BCCA.bb{2} =>
        Some (oget (onth (odflt [] BP.vmap{2}.[id]) 
             (find (fun (x : cipher*cipher*vote*vote) => x.`1 = c)
             (odflt [] BP.vmap{2}.[id])))).`4
         = dec_cipher_vo BS.sk{2} id c HRO.ERO.m{1}) 

  /\ (forall (id:ident) (c:cipher), (c, id) \in BS.encL{2} =>
        Some (oget (onth (odflt [] BP.vmap{2}.[id]) 
             (find (fun (x : cipher*cipher*vote*vote) => x.`1 = c)
             (odflt [] BP.vmap{2}.[id])))).`4
         = dec_cipher_vo BS.sk{2} id c HRO.ERO.m{1}) 

  /\ (mL{2} = map (fun (b:cipher*ident) =>  
              if !( b \in BS.encL{2})
              then dec_cipher_vo BS.sk{2} b.`2 b.`1 HRO.ERO.m{2}
              else None)
              (map (fun (x:(ident*upkey*commitment)*cipher) 
                  => (x.`2, x.`1.`1)) BP.bb{2} ))
).
sp 3 3. 
wp 1 1. 
  
if{1} => //. if{2} => //.  
auto;progress => /#.  
auto;progress => /#.  

exists* (glob Ev){1}, BP.sk{1}, id{1}, ev{1}; elim* => gev sk id c. 
call{1} (Edec_Odec_vo gev sk.`2 id c). 
auto;progress. 
pose id := (nth witness BP.bb{2} j{2}).`1.`1. 
pose c  := (nth witness BP.bb{2} j{2}).`2. 
rewrite -H8 => /#.  smt(). 
congr.  

rewrite (nth_map witness witness _ j{2} _); first smt(@List).   
have H13 : ( (nth witness BP.bb{2} j{2}).`2, 
             (nth witness BP.bb{2} j{2}).`1.`1 ) = 
             (nth witness (map (fun (x : (ident * upkey * commitment) * cipher) 
                 => (x.`2, x.`1.`1)) BP.bb{2}) j{2}) by smt(@List). 
 
have ? : forall id c, !((id, oget BP.pubmap{2}.[id], c) \in BCCA.bb{2}) 
           => !((c, id) \in BS.encL{2}) by smt(). 
have ? : forall id c, !( (c,id) \in BS.encL{2}) 
           => !( (id, oget BP.pubmap{2}.[id], c) \in BCCA.bb{2}) by smt(). 
rewrite -H13 => /#.  smt().   

sp;wp. 
rcondt{2} 1. progress. 
wp. 
 
while{2} (0 <= i1{2} <= size cL0{2}
  /\ mL0{2} = map (fun (b : (cipher * ident)) => 
              if !( (b.`1, b.`2) \in BS.encL{2})
              then dec_cipher_vo BS.sk{2} b.`2 b.`1 HRO.ERO.m{2}
              else None) (take i1{2} cL0{2}))
              (size cL0{2} - i1{2}).
progress. 
wp;sp. 
exists* (glob Ev), BS.sk{hr}, l, c3. elim* => gev sk l c3.  
call (Edec_Odec_vo gev sk l c3).
auto;progress. smt(). smt(). rewrite (take_nth witness i1{hr} cL0{hr});1: smt(). 
rewrite -cats1 map_cat. 
rewrite -H. 
have -> : map
  (fun (b1 : cipher * ident) =>
     if ! ((b1.`1, b1.`2) \in BS.encL{hr}) 
     then dec_cipher_vo BS.sk{hr} b1.`2 b1.`1 HRO.ERO.m{hr}
     else None) 
     [(c3{hr}, l{hr})] = [None] by smt(@List). 
done. 
 smt(). smt(). smt(). 

rewrite (take_nth witness i1{hr} cL0{hr}); 1: done.  
rewrite  -cats1 -H map_cat.
have -> :  map (fun (b1 : cipher * ident) =>
             if ! ((b1.`1, b1.`2) \in BS.encL{hr}) then
             dec_cipher_vo BS.sk{hr} b1.`2 b1.`1 HRO.ERO.m{hr}
             else None) [(c3{hr}, l{hr})] = 
             [dec_cipher_vo BS.sk{hr} l{hr} c3{hr} HRO.ERO.m{hr}] by smt().
done. smt().  
 
auto;progress. rewrite size_ge0. rewrite take0.  smt(). smt(). 
have -> : (take i1_R
     (map
        (fun (x : (ident * upkey * commitment) * cipher) => (x.`2, x.`1.`1))
        BP.bb{2})) =
     (map
        (fun (x : (ident * upkey * commitment) * cipher) => (x.`2, x.`1.`1))
        BP.bb{2}) by smt(@List).   

have ? : forall id c, !((id, oget BP.pubmap{2}.[id], c) \in BCCA.bb{2}) 
      => !((c, id) \in BS.encL{2}) by smt(). 
have ? : forall id c, !( (c,id) \in BS.encL{2}) 
      => !( (id, oget BP.pubmap{2}.[id], c) \in BCCA.bb{2}) by smt(). 
have ? : i1_R = size (map
        (fun (x : (ident * upkey * commitment) * cipher) => (x.`2, x.`1.`1))
        BP.bb{2}). smt(). apply eq_map. progress. smt().
qed. 



(****************************************************************************************************)
(********************************* Right side IND-1-CCA proof ***************************************)
(****************************************************************************************************)

local lemma G3R_CCA_right_equiv &m : 
  BP.setidents{m} = BP.setH{m} `|` BP.setD{m} =>
    Pr[G3R(Ev, Ve, C, CP, A, HRO.ERO, S).main() @ &m : res]
    = Pr[Ind1CCA(Ev,BCCA(Selene(Ev,P,Ve,C,CP),CP,A,S),HRO.ERO,Right).main() @ &m : res]. 
proof. 
move => id_union. 
byequiv => //. 
proc. 
inline*.  
swap{2} [8..13] -7. swap{2} 15 -3. swap{2} 15 -10. swap{2} [14..15] 6.  

(*** We start with everything before the creation of BP.bb and up to the valid check ***) 
seq 41 44 : (
  ={glob CP, glob A, glob C, glob Ve, glob S, glob Ev, 
    BP.setHcheck, BP.secmapD, BP.setD, BP.setidents, BP.pk, BP.bb, valid,
    BP.setidents, BP.setHcheck, BP.setH, BP.secmapD, BP.setD, BP.vmap, 
    BP.sethappy, BP.setchecked, BP.pubmap, BP.secmap, glob HRO.ERO}

    /\ (G3R.bb{1} = BCCA.bb{2})

    /\ (BP.sk{1}.`2 = BS.sk{2})
    /\ (BP.pk{2}.`1 = BS.pk{2})

    /\ (size BCCA.bb{2} = size BS.encL{2})

    /\ (!BS.decQueried{2})

    /\ (forall id pc c, (id, pc, c) \in BCCA.bb{2} => pc = oget BP.pubmap{2}.[id]) 

    /\ (forall (id:ident) (c:cipher) pc, (id, pc, c) \in BCCA.bb{2}
           => is_some BP.vmap{2}.[id])

    /\ (forall id pc c, (id, pc, c) \in BCCA.bb{2} => (c, id) \in BS.encL{2})

    /\ (BP.pk{1}.`1 = get_epk BP.sk{1}.`2)

    /\ (tsk{2} = BP.sk{1}.`3)

    /\ (forall id, id \in BP.setidents{1} => is_some BP.pubmap{1}.[id])

    /\ (forall id, is_some BP.pubmap{1}.[id] => (oget BP.pubmap{1}.[id]).`1 = id)

    /\ BP.setidents{1} = BP.setH{1} `|` BP.setD{1}

    /\ (forall id c, (c, id) \in BS.encL{2} => exists pc, (id, pc, c) \in BCCA.bb{2})

    /\ (forall id c, (id, oget BP.pubmap{2}.[id], c) \in BCCA.bb{2} <=> (c, id) \in BS.encL{2})

    /\ (forall id c, !(exists pc, (id, pc, c) \in BCCA.bb{2}) => !( (c,id) \in BS.encL{2}))
). 

wp. 
while ( ={e1, e2, e3, bb, glob C, glob HRO.ERO, BP.pubmap, pd} /\ i1{1} = i0{2}); first sim.    
wp. 
(*** A.a1 call ***)
call(_: 
  ={glob C, glob CP, glob Ev, glob HRO.ERO, glob S, 
    BP.vmap, BP.pk, BP.setH, BP.pubmap, BP.setidents}

  /\ (!BS.decQueried{2})

  /\ (G3R.bb{1} = BCCA.bb{2})

  /\ (BP.pk{1}.`1 = BS.pk{2})
  /\ (BP.sk{1}.`2 = BS.sk{2})

  /\ (size G3R.bb{1} = size BS.encL{2})

  /\ (forall id pc c, (id, pc, c) \in BCCA.bb{2} => pc = oget BP.pubmap{2}.[id]) 

  /\ (forall (id:ident) (c:cipher) pc, (id, pc, c) \in BCCA.bb{2}
           => is_some BP.vmap{2}.[id])


  /\ (forall id pc c, (id, pc, c) \in BCCA.bb{2} => (c, id) \in BS.encL{2}) 

  /\ (BP.pk{1}.`1 = get_epk BP.sk{1}.`2)

  /\ (BP.setidents{1} = BP.setH{1} `|` BP.setD{1})

  /\ (forall id, id \in BP.setidents{1} => is_some BP.pubmap{1}.[id])

  /\ (forall id, is_some BP.pubmap{1}.[id] => (oget BP.pubmap{1}.[id]).`1 = id)

  /\ (forall id pc c, (id, pc, c) \in BCCA.bb{2} => is_some BP.vmap{2}.[id])

  /\ (forall id c, (c, id) \in BS.encL{2} => is_some BP.vmap{2}.[id])

  /\ (forall id c, (c, id) \in BS.encL{2} => exists pc, (id, pc, c) \in BCCA.bb{2})

  /\ (forall id c, (id, oget BP.pubmap{2}.[id], c) \in BCCA.bb{2} <=> (c, id) \in BS.encL{2})

    /\ (forall id c, !(exists pc, (id, pc, c) \in BCCA.bb{2}) => !( (c,id) \in BS.encL{2}))
).

proc. if => //. inline*. 
seq 9 6 : ( 
  ={id, v0, v1, glob C, glob CP, glob Ev, HRO.ERO.m, glob S, 
    BP.pk, BP.setH, BP.pubmap, BP.setidents, BP.vmap} /\

  v2{1} = v1{1} /\ l{2} = id{2} /\
  ev{1} = c0{2} /\ pc{1} = oget BP.pubmap{1}.[id0{1}] /\ 
  l{2} = id{2} /\ v2{1} = p{2}

  /\ !BS.decQueried{2} /\

   G3R.bb{1} = BCCA.bb{2} /\

   BP.pk{1}.`1 = BS.pk{2} /\
   BP.sk{1}.`2 = BS.sk{2} /\

   size G3R.bb{1} = size BS.encL{2} 

  /\ Some v1{2} = dec_cipher_vo BP.sk{1}.`2 id{2} c0{2} HRO.ERO.m{2}

  /\ (forall id pc c, (id, pc, c) \in BCCA.bb{2} => pc = oget BP.pubmap{2}.[id]) 

  /\ (forall (id:ident) (c:cipher) pc, (id, pc, c) \in BCCA.bb{2}
           => is_some BP.vmap{2}.[id])

  /\ (forall id pc c, (id, pc, c) \in BCCA.bb{2} => (c, id) \in BS.encL{2}) 

  /\ BP.pk{1}.`1 = get_epk BP.sk{1}.`2 /\

  (id{1} \in BP.setH{1})

  /\ (BP.setidents{1} = BP.setH{1} `|` BP.setD{1})

  /\ (forall id, id \in BP.setidents{1} => is_some BP.pubmap{1}.[id])

  /\ (forall id, is_some BP.pubmap{1}.[id] => (oget BP.pubmap{1}.[id]).`1 = id)

   /\ (forall id pc c, (id, pc, c) \in BCCA.bb{2} => is_some BP.vmap{2}.[id])

  /\ (forall id c, (c, id) \in BS.encL{2} => is_some BP.vmap{2}.[id])

  /\ (forall id c, (c, id) \in BS.encL{2} => exists pc, (id, pc, c) \in BCCA.bb{2})

 /\ (forall id c, (id, oget BP.pubmap{2}.[id], c) \in BCCA.bb{2} <=> (c, id) \in BS.encL{2})

    /\ (forall id c, !(exists pc, (id, pc, c) \in BCCA.bb{2}) => !( (c,id) \in BS.encL{2}))
). 

sp. 
exists* BP.sk{1}, BP.pk{1}, id1{1}, v2{1}. elim* => sk pk id v. 
pose kp := (pk.`1 = get_epk sk.`2). 
      have em_kp : kp \/ !kp by exact/orbN.  
      elim em_kp.
      move => h. 
      call (Eenc_dec_vo sk.`2 pk.`1 id v h);skip;progress.  
      move => h. 
      conseq (_: _ ==> !(BP.pk{1}.`1 = get_epk BP.sk{1}.`2)) => //.  
      call(_: ={glob HRO.ERO}); first by sim. 
      skip;progress.
auto;progress. 
by rewrite cats1 size_rcons H0 addzC. 
smt(@SmtMap). 
case (id2 = id{2}) => ideq. 
rewrite ideq. 
rewrite get_set_eqE. trivial. trivial. 
rewrite get_set_neqE. rewrite ideq. trivial. smt(). 

case(id2 = id{2}) => ideq. 
case(c1 = c0{2}) => ceq. 
rewrite mem_cat. right. by rewrite mem_seq1 ideq ceq. 
have ? : (id2, pc0, c1) \in BCCA.bb{2} by smt(). 
rewrite mem_cat. left. smt(). 
have ? : (id2, pc0, c1) \in BCCA.bb{2} by smt(). 
rewrite mem_cat. left. smt(). 

case (id2 = id{2}) => ideq. 
rewrite ideq. 
rewrite get_set_eqE; first trivial. trivial.   
rewrite get_set_neqE; first trivial. smt(). 

case (id2 = id{2}) => ideq. 
rewrite ideq. 
rewrite get_set_eqE; first trivial. trivial.   
rewrite get_set_neqE; first trivial. smt(@List @SmtMap). 


exists (oget BP.pubmap{2}.[id2]). 
case (id2 = id{2}) => ideq.  
case (c1 = c0{2}) => ceq. rewrite ideq. trivial.  
have ? : (c1, id2) \in BS.encL{2} by smt(@List). 
smt(). 
have ? : (c1, id2) \in BS.encL{2} by smt(@List). 
smt(). 

case(id2 = id{2}) => ideq. 
case(c1 = c0{2}) => ceq.  
rewrite mem_cat. right.  by rewrite mem_seq1 ideq ceq.
have ? : (id2, oget BP.pubmap{2}.[id2], c1) \in BCCA.bb{2} by smt(). 
rewrite mem_cat. left. smt(). 
have ? : (id2, oget BP.pubmap{2}.[id2], c1) \in BCCA.bb{2} by smt(). 
rewrite mem_cat. left. smt(). 
smt(@List). 
rewrite mem_cat.
smt(@List @SmtMap). 

proc;inline*;auto. 
proc;inline*;auto. 
by conseq So_ll2. 

while(={i, BP.setidents, BP.secmap, BP.secmapD, BP.setD, BP.pubmap, glob CP}
  /\ (BP.pk{1}.`3.`4 = pPk{2})
  /\ (BP.pk{1}.`3.`5 = pCo{2})
  /\ (BP.sk{1}.`1 = pOp{2})
  /\ (forall j id, j <= i{1} => id \in (take j (elems BP.setidents{1})) 
      => is_some BP.pubmap{1}.[id])
  /\ (forall id, is_some BP.pubmap{1}.[id] 
      => (oget BP.pubmap{1}.[id]).`1 = id)
).

seq 6 6 : (
  (={i, BP.setidents, BP.pubmap, BP.secmap, BP.secmapD, BP.setD, id,
       glob CP}  
  /\ (BP.pk{1}.`3.`4 = pPk{2})
  /\ (BP.pk{1}.`3.`5 = pCo{2})
  /\ (BP.sk{1}.`1 = pOp{2})
  /\  (forall (j0 : int) (id0 : ident),
      j0 <= i{1} + 1 =>
      id0 \in take j0 (elems BP.setidents{1}) => is_some BP.pubmap{1}.[id0]) /\
   forall (id0 : ident),
     is_some BP.pubmap{1}.[id0] => (oget BP.pubmap{1}.[id0]).`1 = id0) /\
  i{1} < card BP.setidents{1} /\ i{2} < card BP.setidents{2}
).
auto;progress.  
rewrite get_setE.   
case (id00 = nth witness (elems BP.setidents{2}) i{2}); first by trivial.  
move => id00_neq_nth. 
case: (0 < j0)=> [lt0_j0|/#].
case (j0 = i{2} + 1) => h. 
+ have h1 : id00 \in take i{2} (elems BP.setidents{2}). 
  + have h2 : (take j0 (elems BP.setidents{2})) <> [] by smt(@SmtMap).
    by move: H4; rewrite h (take_nth witness) 1:/# mem_rcons /= id00_neq_nth.
  smt(@List).  
smt().
smt(@SmtMap). 
if => //;auto;progress. 
wp;while(={BP.setidents, tpk, pPk, pTr, tsk, pCo, pOp, trL, pi2} /\ i0{1} = i{2}); first sim. 
wp;while(={BP.setidents, tpk, trL, pTr, glob CP, pPk} /\ i0{1} = i{2}); first sim. 
wp;rnd;while(={BP.setidents, tpk, tpTr, trL} /\ i0{1} = i{2}); first sim. 
wp;rnd;wp;call Ev_kgen_get_epk. 
wp;call(_:true);while(={w, HRO.ERO.m});first sim. 
auto;progress. smt(@List). smt(@SmtMap). rewrite (H11 i_R2); first trivial. smt(@List).


(*** If sentences are equivalent ***)
seq 5 11 : (
  ={glob HRO.ERO, glob A, glob S, glob Ve, valid, BP.setHcheck, BP.r, 
    BP.bb, BP.setchecked, BP.sethappy, BP.pk, BP.secmap, BP.vmap, BP.setidents, 
    BP.pubmap, glob CP}
  /\ (G3R.bb{1} = BCCA.bb{2}) 
  /\ (BP.sk{1}.`2 = BS.sk{2})
);last  by sim. 

(*** If sentences complete ***)

wp;rnd.

while(={j, BP.bb, rL,  glob HRO.ERO, BP.pk, BP.vmap, BP.pubmap} /\ 0 <= j{2}
  /\ (BP.sk{1}.`2 = BS.sk{2})
  /\ (BP.pk{1}.`1 = BS.pk{2}) 
  /\ (BP.sk{1}.`3 = tsk{2})

  /\ (G3R.bb{1} = BCCA.bb{2})

    /\ (BP.setidents{1} = BP.setH{1} `|` BP.setD{1})

  /\ (forall id, id \in BP.setidents{1} => is_some BP.pubmap{1}.[id])

   /\ (forall id pc c, (id, pc, c) \in BCCA.bb{2} => pc = oget BP.pubmap{2}.[id]) 

  /\ (forall id, is_some BP.pubmap{1}.[id] => (oget BP.pubmap{1}.[id]).`1 = id)

   /\ (forall id c, (c, id) \in BS.encL{2} => exists pc, (id, pc, c) \in BCCA.bb{2})

    /\ (forall id pc c, (id, pc, c) \in BCCA.bb{2} => (c, id) \in BS.encL{2}) 

  /\ (forall id c, (id, oget BP.pubmap{2}.[id], c) \in BCCA.bb{2} <=> (c, id) \in BS.encL{2}) 

  /\ (forall id c, !(exists pc, (id, pc, c) \in BCCA.bb{2}) => !( (c,id) \in BS.encL{2}))

  /\ (mL{2} = map (fun (b:cipher*ident) =>  
              if !( b \in BS.encL{2})
              then dec_cipher_vo BS.sk{2} b.`2 b.`1 HRO.ERO.m{2}
              else None)
              (map (fun (x:(ident*upkey*commitment)*cipher) => (x.`2, x.`1.`1)) BP.bb{2} ))
).
sp 3 3. 
wp 1 1. 
  
if{1} => //. if{2} => //.   
auto;progress => /#.  
auto;progress => /#.
 
if{2} => //. 

exists* (glob Ev){1}, BP.sk{1}, id{1}, ev{1}; elim* => gev sk id c. 
call{1} (Edec_Odec_vo gev sk.`2 id c). 
auto;progress. 
pose id := (nth witness BP.bb{2} j{2}).`1.`1. 
pose c := (nth witness BP.bb{2} j{2}).`2.
smt(). smt(). 

exists* (glob Ev){1}, BP.sk{1}, id{1}, ev{1}; elim* => gev sk id c. 
call{1} (Edec_Odec_vo gev sk.`2 id c). 
auto;progress. 

rewrite (nth_map witness witness _ j{2} _); first smt(@List).   
have H13 : ( (nth witness BP.bb{2} j{2}).`2, 
             (nth witness BP.bb{2} j{2}).`1.`1 ) = 
             (nth witness (map (fun (x : (ident * upkey * commitment) * cipher) 
                => (x.`2, x.`1.`1)) BP.bb{2}) j{2}) by smt(@List). 
 
have ? : forall id c, !((id, oget BP.pubmap{2}.[id], c) \in BCCA.bb{2}) 
          => !((c, id) \in BS.encL{2}) by smt(). 
have ? : forall id c, !( (c,id) \in BS.encL{2}) 
          => !( (id, oget BP.pubmap{2}.[id], c) \in BCCA.bb{2}) by smt(). 
rewrite -H13 => /#. smt(). 

sp;wp. 
rcondt{2} 1. progress. 
wp. 
 
while{2} (0 <= i1{2} <= size cL0{2}
  /\ mL0{2} = map (fun (b : (cipher * ident)) => 
              if !( (b.`1, b.`2) \in BS.encL{2})
              then dec_cipher_vo BS.sk{2} b.`2 b.`1 HRO.ERO.m{2}
              else None) (take i1{2} cL0{2}))
              (size cL0{2} - i1{2}).
progress. 
wp;sp. 
exists* (glob Ev), BS.sk{hr}, l, c3. elim* => gev sk l c3.  
 call (Edec_Odec_vo gev sk l c3).
auto;progress. smt(). smt().    
rewrite (take_nth witness i1{hr} cL0{hr}); 1:done. 
rewrite -cats1 -H map_cat; 1:smt(@List).  
smt(). smt(). smt(). 
rewrite (take_nth witness i1{hr} cL0{hr}); 1:done. 
rewrite -cats1 -H map_cat; 1:smt(@List). 
smt(). 
auto;progress. rewrite size_ge0. 
rewrite take0. smt(). 
smt(). 
have -> : (take i1_R
     (map
        (fun (x : (ident * upkey * commitment) * cipher) => (x.`2, x.`1.`1))
        BP.bb{2})) =
     (map
        (fun (x : (ident * upkey * commitment) * cipher) => (x.`2, x.`1.`1))
        BP.bb{2}) by smt(@List).   

have ? : forall id c, !((id, oget BP.pubmap{2}.[id], c) \in BCCA.bb{2}) 
      => !((c, id) \in BS.encL{2}) by smt(). 
have ? : forall id c, !( (c,id) \in BS.encL{2}) 
      => !( (id, oget BP.pubmap{2}.[id], c) \in BCCA.bb{2}) by smt(). 
have ? : i1_R = size (map
        (fun (x : (ident * upkey * commitment) * cipher) 
         => (x.`2, x.`1.`1)) BP.bb{2}). smt(). apply eq_map.  smt().   
qed. 


(**** Some useful lemmas for the final lemma ****)
local lemma G2L_G3R_cca &m : 
    BP.setidents{m} = BP.setH{m} `|` BP.setD{m} =>
    `| Pr[G2L(Ev,Ve,C,CP,A,HRO.ERO,S).main() @ &m : res] - 
       Pr[G3R(Ev,Ve,C,CP,A,HRO.ERO,S).main() @ &m : res]| = 
    `| Pr[Ind1CCA(Ev,BCCA(Selene(Ev,P,Ve,C,CP),CP,A,S),HRO.ERO,Left).main() @ &m : res] -  
       Pr[Ind1CCA(Ev,BCCA(Selene(Ev,P,Ve,C,CP),CP,A,S),HRO.ERO,Right).main() @ &m : res]|.
proof. 
move => id_union. 
by rewrite (G2L_CCA_left_equiv &m id_union) (G3R_CCA_right_equiv &m id_union). 
qed. 

local lemma DU_MB_BPRIV_R_G3R_equiv &m : 
    BP.setidents{m} = BP.setH{m} `|` BP.setD{m} =>
    Pr[DU_MB_BPRIV_R(Selene(Ev,P,Ve,C,CP),A,HRO.ERO,G,S,Recover').main() @ &m : res] = 
    Pr[G3R(Ev,Ve,C,CP,A,HRO.ERO,S).main() @ &m : res]. 
proof. 
move => id_union. 
by rewrite -(G2R_G3R_equiv &m id_union) -(G1R_G2R_equiv &m id_union) 
           -(G0R_G1R_equiv &m id_union) -(G0R'_G0R_equiv &m id_union) 
            (DU_MB_BPRIV_R_G0R'_equiv &m id_union). 
qed. 

local lemma DU_MB_BPRIV_L_G1L_equiv &m :
    BP.setidents{m} = BP.setH{m} `|`BP.setD{m} =>
    Pr[DU_MB_BPRIV_L(Selene(Ev,P,Ve,C,CP),A,HRO.ERO,G).main() @ &m : res] = 
    Pr[G0L(Ev,P,Ve,C,CP,A,HRO.ERO,G).main() @ &m : res]. 
proof. 
move => id_union. 
by rewrite (DU_MB_BPRIV_L_G0L'_equiv &m id_union) (G0L'_G0L_equiv &m id_union). 
qed. 
 
lemma du_mb_bpriv &m : 
  BP.setidents{m} = BP.setH{m} `|` BP.setD{m} =>
  `| Pr[DU_MB_BPRIV_L(Selene(Ev,P,Ve,C,CP),A,HRO.ERO,G).main() @ &m : res]
     - Pr[DU_MB_BPRIV_R(Selene(Ev,P,Ve,C,CP),A,HRO.ERO,G,S,Recover').main() @ &m : res]| 
   <= 
      Pr[VFRS(Ev,BVFR(Selene(Ev,P,Ve,C,CP),A,CP),R,CP,HRO.ERO,G).main() @ &m : res]
    + Pr[VFRS(Ev,BVFR(Selene(Ev,P,Ve,C,CP),A,CP),R,CP,HRO.ERO,S).main() @ &m : res]
    + `| Pr[ZK_L(R(Ev,HRO.ERO),P,BZK(Ev,P,C,Ve,A,CP,HRO.ERO),G).main() @ &m : res] 
         - Pr[ZK_R(R(Ev,HRO.ERO),S,BZK(Ev,P,C,Ve,A,CP,HRO.ERO)  ).main() @ &m : res]| 
    + `| Pr[Ind1CCA(Ev,BCCA(Selene(Ev,P,Ve,C,CP),CP,A,S),HRO.ERO,Left).main() @ &m : res] 
         - Pr[Ind1CCA(Ev,BCCA(Selene(Ev,P,Ve,C,CP),CP,A,S),HRO.ERO,Right).main() @ &m : res]|. 
proof. 
move => id_union.  

(** Add and subtract G1L to the first absolute value **)
have -> : 
    `|Pr[DU_MB_BPRIV_L(Selene(Ev, P, Ve, C, CP), A, HRO.ERO, G).main() @ &m : res]
    - Pr[DU_MB_BPRIV_R(Selene(Ev, P, Ve, C, CP), A, HRO.ERO, G, S, Recover').main () @ &m : res]| 
  = `|Pr[DU_MB_BPRIV_L(Selene(Ev, P, Ve, C, CP), A, HRO.ERO, G).main() @ &m : res]
    - Pr[G1L(Ev,Ve,C,CP,A,HRO.ERO,S).main() @ &m : res]
    + Pr[G1L(Ev,Ve,C,CP,A,HRO.ERO,S).main() @ &m : res]
    - Pr[DU_MB_BPRIV_R(Selene(Ev, P, Ve, C, CP), A, HRO.ERO, G, S, Recover').main () @ &m : res]| 
  by smt().  
 
rewrite (DU_MB_BPRIV_L_G0L'_equiv &m); 1:done.
rewrite (G0L'_G0L_equiv &m); 1:done.  

have H0 : `|Pr[G0L(Ev, P, Ve, C, CP, A, HRO.ERO, G).main() @ &m : res] -
            Pr[G1L(Ev, Ve, C, CP, A, HRO.ERO, S).main() @ &m : res]| +
          `|Pr[G1L(Ev, Ve, C, CP, A, HRO.ERO, S).main() @ &m : res] -
            Pr[DU_MB_BPRIV_R(Selene(Ev, P, Ve, C, CP), A, HRO.ERO, G, S, Recover').main() @ &m : res]| <=
            Pr[VFRS(Ev, BVFR(Selene(Ev, P, Ve, C, CP), A, CP), R, CP, HRO.ERO, G).main() @ &m : res] +
            Pr[VFRS(Ev, BVFR(Selene(Ev, P, Ve, C, CP), A, CP), R, CP, HRO.ERO, S).main() @ &m : res] +
          `|Pr[ZK_L(R(Ev, HRO.ERO), P, BZK(Ev, P, C, Ve, A, CP, HRO.ERO), G).main() @ &m : res] -
            Pr[ZK_R(R(Ev, HRO.ERO), S, BZK(Ev, P, C, Ve, A, CP, HRO.ERO)).main() @ &m : res]| +
          `|Pr[Ind1CCA(Ev, BCCA(Selene(Ev, P, Ve, C, CP), CP, A, S), HRO.ERO, Left).main() @ &m : res] -
            Pr[Ind1CCA(Ev, BCCA(Selene(Ev, P, Ve, C, CP), CP, A, S), HRO.ERO, Right).main() @ &m : res]|. 

rewrite (DU_MB_BPRIV_R_G3R_equiv &m); 1:done. 

have -> : `|Pr[G1L(Ev, Ve, C, CP, A, HRO.ERO, S).main() @ &m : res] -
            Pr[G3R(Ev, Ve, C, CP, A, HRO.ERO, S).main() @ &m : res]| = 
          `|Pr[G2L(Ev, Ve, C, CP, A, HRO.ERO, S).main() @ &m : res] -
            Pr[G3R(Ev, Ve, C, CP, A, HRO.ERO, S).main() @ &m : res]|
  by rewrite (G1L_G2L_equiv &m). 

rewrite (G2L_G3R_cca &m); 1:done.
smt(G0L_G1L_zk_vfr).  
smt(). 
qed.  

end section DU_MB_BPRIV. 
