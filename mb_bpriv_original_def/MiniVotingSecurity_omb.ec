require import Int Bool Real SmtMap. 
require import List Distr Core FSet. 
require import Logic. 
require import LeftOrRight. 
require (*  *) MiniVotingDefinition_omb. 
require (*  *) ROM.

clone include MiniVotingDefinition_omb.  

(* eager random oracle *)
clone include ROM with
  type in_t       <- h_in,
  type out_t      <- h_out,
  op dout(x:h_in) <- dh_out. 

  clone FiniteEager as HRO.

(****** MB-BPRIV *******)
section MB_BPRIV. 

declare module G  <: GOracle.Oracle { -BP, -HRO.ERO, -BPS, -BS }.   
declare module E  <: Scheme { -BP, -HRO.ERO, -G, -BPS, -BS, -PKEvf.H.Count, -PKEvf.H.HybOrcl, -WrapAdv }.
declare module S  <: Simulator { -BP, -HRO.ERO, -G, -E, -BPS, -BS, -PKEvf.H.Count, -PKEvf.H.HybOrcl, -WrapAdv }. 
declare module Ve <: Verifier { -BP, -HRO.ERO, -G, -E, -S, -BPS, -BS }. 
declare module P  <: Prover { -BP, -HRO.ERO, -G, -E, -S, -Ve, -BPS, -BS }. 
declare module R  <: VotingRelation' { -BP, -HRO.ERO, -G, -E, -S, -Ve, -P, -BPS, -BS }. 
declare module C  <: ValidInd { -BP, -HRO.ERO, -G, -E, -S, -Ve, -P, -R, -BPS, -BS }. 
declare module A  <: OMB_BPRIV_adv { -BP, -HRO.ERO, -G, -E, -S, -Ve, -P, -R, -C, -BPS, -BS }. 

(**** Lossless assumptions ****)

(** Oracles **)
declare axiom Gi_ll : islossless G.init. 
declare axiom Go_ll : islossless G.o. 

(** MB-BPRIV adversary **) 
declare axiom A_a1_ll (O <: MB_BPRIV_oracles { -A }):
  islossless O.vote => islossless O.board => islossless O.h => islossless O.g => islossless A(O).a1. 
declare axiom A_a2_ll (O <: MB_BPRIV_oracles { -A }): 
  islossless O.board => islossless O.h => islossless O.g => islossless A(O).a2. 
declare axiom A_a3_ll (O <: MB_BPRIV_oracles { -A }): 
  islossless O.verify => islossless O.h => islossless O.g => islossless A(O).a3. 
declare axiom A_a4_ll (O <: MB_BPRIV_oracles { -A }): 
  islossless O.h => islossless O.g => islossless A(O).a4.
declare axiom A_a5_ll (O <: MB_BPRIV_oracles { -A }): 
  islossless O.board => islossless O.h => islossless O.g => islossless A(O).a5.

(** Proof system **)
declare axiom PS_p_ll (G <: GOracle.POracle { -P }) : islossless G.o => islossless P(G).prove. 
declare axiom PS_v_ll (G <: GOracle.POracle { -Ve }) : islossless G.o => islossless Ve(G).verify. 

(** Encryption **)
declare axiom E_kg_ll  (H <: HOracle.POracle { -E }) : islossless H.o => islossless E(H).kgen. 
declare axiom E_enc_ll (H <: HOracle.POracle { -E }) : islossless H.o => islossless E(H).enc. 
declare axiom E_dec_ll (H <: HOracle.POracle { -E }) : islossless H.o => islossless E(H).dec. 

(** Encryption with HRO.ERO **)
local lemma E_kg_ll'  : islossless HRO.ERO.o => islossless E(HRO.ERO).kgen
  by rewrite (E_kg_ll HRO.ERO HRO.ERO_o_ll).
local lemma E_enc_ll' : islossless HRO.ERO.o => islossless E(HRO.ERO).enc
  by rewrite (E_enc_ll HRO.ERO HRO.ERO_o_ll).
local lemma E_dec_ll' : islossless HRO.ERO.o => islossless E(HRO.ERO).dec
  by rewrite (E_dec_ll HRO.ERO HRO.ERO_o_ll).

(** ZK simulator **)
declare axiom Si_ll : islossless S.init. 
declare axiom So_ll : islossless S.o. 
declare axiom Sp_ll : islossless S.prove. 

(** VFR **)
declare axiom R_m_ll : islossless R(E,HRO.ERO).main. 

(** ValidInd operator **)
declare axiom C_vi_ll (H <: HOracle.POracle { -C }) : islossless H.o => islossless C(H).validInd. 

(****************************************************************************************************)
(*************************** Necessary axioms and small lemmas **************************************)
(****************************************************************************************************)

(*** Axiom on result distribution ***)
declare axiom Rho_weight (x: (ident * vote option) list):
  weight (Rho x) = 1%r. 

(*** Axiom linking key generation and extractPk operator ***)
declare axiom E_kgen_extractpk (H <: HOracle.POracle):
 equiv [E(H).kgen ~ E(H).kgen : ={glob H, glob E} ==> 
                                ={glob H, glob E, res} /\ res{1}.`1 = extractPk res{1}.`2]. 

(*** Voting relation does not change state of eager random oracle ***)
declare axiom relConstraint (gh : (glob HRO.ERO)):
    phoare[ R(E,HRO.ERO).main : 
            (glob HRO.ERO) = gh ==> (glob HRO.ERO) = gh] = 1%r. 

(* decryption operator with access to a map of values, instead of random oracle*)
op dec_cipher: skey -> label -> cipher -> (h_in, h_out) SmtMap.fmap -> vote option.


(* axiom for stating that the keys are generated correctly *)
declare axiom Ekgen_extractPk (H<: HOracle.POracle):
  equiv [E(H).kgen ~ E(H).kgen:  ={glob H, glob E} ==> 
         ={glob H, glob E,  res} /\ 
         res{1}.`1 = extractPk res{1}.`2  /\
         res{1}.`1 = extractPk res{1}.`2 ].

(* axiom for linking E.dec to dec_cipher operator *)   
declare axiom Edec_Odec (ge: (glob E)) (sk2: skey)(l2: ident) (c2: cipher):
  phoare [E(HRO.ERO).dec:  
         (glob E) =ge /\ arg = (sk2, l2, c2)
           ==> (glob E) =ge /\ res = dec_cipher sk2 l2 c2 HRO.ERO.m ] = 1%r.

(* axiom on the state of the encryption scheme E *)
declare axiom Ee_eq (ge: (glob E)):
  phoare [E(HRO.ERO).enc: 
         (glob E) = ge ==> (glob E) = ge] = 1%r.
    
(* axiom for transforming an encryption into decryption (one-sided) *)
declare axiom Eenc_decL (ge: (glob E)) (sk2: skey) (pk2: pkey)(l2: ident) (p2: vote): 
    (pk2 = extractPk sk2) =>
    phoare [E(HRO.ERO).enc : 
           (glob E) = ge /\ arg=(pk2, l2, p2) 
            ==> (glob E) = ge /\ Some p2 = dec_cipher sk2 l2 res HRO.ERO.m ]= 1%r.   

(* axiom for transforming an encryption into decryption (two-sided) *)
declare axiom Eenc_decL_hr (ge: (glob E)) (sk2: skey) (l2: label) (p2: vote): 
  hoare [E(HRO.ERO).enc : 
          (glob E) = ge /\ arg=(extractPk sk2, l2, p2) 
          ==> (glob E) = ge /\ Some p2 = dec_cipher sk2 l2 res HRO.ERO.m ].

equiv Eenc_dec (sk2: skey) (l2: label) (p2: vote): 
  E(HRO.ERO).enc ~ E(HRO.ERO).enc : 
     ={glob HRO.ERO, glob E, arg} /\ arg{1} = (extractPk sk2, l2, p2) 
     ==> 
     ={glob HRO.ERO, glob E,  res} /\
     Some p2 = dec_cipher sk2 l2 res{1} HRO.ERO.m{1}.
proof.
exists * (glob E){1}; elim * => ge.
conseq (: _ ==> ={glob HRO.ERO, glob E, res}) (Eenc_decL_hr ge sk2 l2 p2)=> //.
by sim.
qed.

(* decryption should not change the state of an eager random oracle *) 
local lemma Edec_Odec_eq (sk2: skey)(l2: ident) (c2: cipher):
  equiv [E(HRO.ERO).dec ~ E(HRO.ERO).dec :
          ={glob HRO.ERO, glob E, arg}/\ arg{1} = (sk2, l2, c2)
           ==>  ={glob HRO.ERO, glob E, res} /\ res{1} = dec_cipher sk2 l2 c2 HRO.ERO.m{1} ].
proof.
  proc*=>//=. 
  exists* (glob E){1}; elim* => ge.
  call{1} (Edec_Odec ge sk2 l2 c2 ).
  call{2} (Edec_Odec ge sk2 l2 c2 ). 
  by auto.
qed.

(* axiom on the state of the encryption scheme E *)
declare axiom Ee_hr (ge: (glob E)):
  hoare [E(HRO.ERO).enc: (glob E) = ge ==> (glob E) = ge].

(* the state of the simulated oracle is the same in two-sided call *)
local equiv So_ll2: S.o ~ S.o : ={arg, glob S} ==> ={res, glob S}.
proof. by proc true. qed.    

(* Operator to reverse the order of tuples *)
op flip (bb : (ident * cipher) list) = map (fun b : (ident * cipher) => (b.`2, b.`1)) bb. 

(* Operator removing the first element of a three tuple *)
op rem_fst3 (x : ('a * 'b * 'c)) = (x.`2, x.`3).

(* Operator removing first element of a four tuple *)
op rem_fst4 (x : ('a * 'b * 'c * 'd)) = (x.`2, x.`3, x.`4).


(****************************************************************************************************)
(******************** Constructed adversaries from mb-bpriv adversary *******************************)
(****************************************************************************************************)


(************ Construct a ZK adversary from MB-BPRIV adversary *************) 
module type VotingAdvZK (H:HOracle.Oracle, O:GOracle.POracle) = {
  proc a1() : (pkey * pubBB * result) * (skey * (ident * cipher) list) {H.init, H.o, O.o}
  proc a2(pi : prf option) : bool {H.o, O.o}
}.

(********  BZK with valid as global variable BP.valid from the BP module  ********)
(********  in VotingSecurity_omb.ec                                       ********)

module BZK(E:Scheme, P:Prover, C:ValidInd, Ve:Verifier, 
           A:OMB_BPRIV_adv, H:HOracle.Oracle, G:GOracle.POracle) = {

  module O  = MB_BPRIV_oracles(MV(E,P,Ve,C), H, G, Left)
  module MV = MV(E,P,Ve,C,H,G)
  module A  = A(O)

  proc a1() : (pkey * pubBB * result) * (skey * (ident * cipher) list) = {
    
    var i, id;
    var dbb, idl, b, v, j;

    BP.vmap    <- empty;
    BP.pubmap  <- empty;
    BP.secmap  <- empty;
    BP.secmapD <- empty;
    BP.bb0     <- [];
    BP.bb1     <- [];


    BP.setchecked <- fset0;
    BP.sethappy   <- fset0;

    H.init();
    
    (BP.pk, BP.sk) <@ E(H).kgen();
    
    i <- 0;
    while (i < card BP.setidents) {
      id <- nth witness (elems BP.setidents) i;
      BP.secmap.[id] <- id;
      BP.pubmap.[id] <- id;
      if (id \in BP.setD) {
        BP.secmapD.[id] <- oget BP.secmap.[id];
      }
    i <- i + 1;
    }

    BP.bb <@ A.a1(BP.pk, BP.secmapD, BP.pubmap);

    dbb <- [];
     j <- 0;
     while (j < size BP.bb) {
      (idl, b) <- nth witness BP.bb j;
         v     <@ E(H).dec(BP.sk, idl, b);
       dbb     <- dbb ++ [(idl, v)];
         j     <- j + 1;
      }
    BP.pk  <- extractPk BP.sk;   BP.r   <$ Rho dbb;         
    
    if (!(BP.setHcheck \subset fdom BP.vmap)) {
      BP.d <$ {0,1};
    } else {
         BP.valid <@ MV.validboard(BP.bb, BP.pk); 

      if (!BP.valid) {
        BP.d <@ A.a2();
      } else { 
        A.a3();
        if (!BP.setHcheck \subset BP.setchecked) {
            BP.d <$ {0,1};
        } else { 
          if (!BP.setHcheck \subset BP.sethappy) {
             BP.d <@ A.a4();
          }
        }
      }
    }
  return ((BP.pk, miniPublish BP.bb, BP.r), (BP.sk, BP.bb));
  }
 
  proc a2(pi:prf option) : bool = {
   if ( BP.setHcheck \subset fdom BP.vmap /\ BP.valid /\ BP.setHcheck \subset BP.setchecked
       /\ BP.setHcheck \subset BP.sethappy) {
       BP.d <@ A.a5(BP.r, oget pi);
   }
   return BP.d;
  }      
}.   

(************* Construct VFR adversary from mb-BPRIV adversary **************)
module BVFR(V:VotingSystem, A:OMB_BPRIV_adv, H:HOracle.POracle, G:GOracle.POracle) = {
  
  module L = MB_BPRIV_oracles(V,H,G,Left)

  proc main(pk:pkey) : (ident * cipher) list = {
    
    var i, id;
    
    BP.vmap    <- empty;
    BP.pubmap  <- empty;
    BP.secmap  <- empty;
    BP.secmapD <- empty;
    BP.bb0     <- [];
    BP.bb1     <- [];
    BP.pk      <- pk;

    i <- 0;
    while (i < card BP.setidents) {
      id <- nth witness (elems BP.setidents) i;
      BP.secmap.[id] <- id;
      BP.pubmap.[id] <- id;
      if (id \in BP.setD) {
        BP.secmapD.[id] <- oget BP.secmap.[id];
      }
    i <- i + 1;
    }
   BP.bb <@ A(L).a1(BP.pk, BP.secmapD, BP.pubmap);
   return BP.bb; 
  }
}.

(*************** Construct CCA adversary from mb-BPRIV adversary **********)

module BCCA(V:VotingSystem, A:OMB_BPRIV_adv, S:Simulator, IO:Ind1CCA_Oracles) = {

  module V = V(HRO.ERO, S)
  
  module O = {

    proc h = IO.o
    proc g = S.o
    
    proc vote(id:ident, v0 v1: vote) = {
      var b;
      
      if ((id \in BP.setH)) {
        b <@ IO.enc(id, v0, v1);
        BP.vmap.[id] <- (b, b,  v0) :: (odflt [] BP.vmap.[id]);
        BP.bb' <- (id, b) :: BP.bb';
      }
    }

    proc verify(id:ident) = {
      var ok, sv;
      
      BP.setchecked <- BP.setchecked `|` (fset1 id);

      sv <- odflt [] (BP.vmap.[id]);
      ok <@ V.verifyvote(id,  (oget (ohead sv)).`2 , BP.bb, id, id);

      if (ok) {
        BP.sethappy <- BP.sethappy `|` (fset1 id);
      }
    }

    proc board() : pubBB = {
      return miniPublish(BP.bb');
    }
  }

  module A = A(O)

  proc main(pk:pkey) : bool = {
    var i, id;
    var valid;
    var dbb, j, idl, b, v;
    var mL;
    
    BP.vmap       <- empty;
    BP.pubmap     <- empty;
    BP.secmap     <- empty;
    BP.secmapD    <- empty;
    BP.setchecked <- fset0;
    BP.sethappy   <- fset0;
    BP.bbstar <- None;

    BP.bb' <- [];

    S.init();

    BP.pk <- pk;

    (* register *)
    i <- 0;
    while (i < card BP.setidents) {
      id <- nth witness (elems BP.setidents) i;
      BP.secmap.[id] <- id;
      BP.pubmap.[id] <- id;
      if (id \in BP.setD) {
        BP.secmapD.[id] <- oget BP.secmap.[id];
      }
    i <- i + 1;
    }

    (* adversary creates bulletin board *)
    BP.bb <@ A.a1(BP.pk, BP.secmapD, BP.pubmap);

    (* check if adversary board is valid *)
    valid <@ V.validboard(BP.bb, BP.pk);

    (* tally *)
    mL <@ IO.dec(flip (BP.bb));
    dbb <- [];
      j <- 0;

    while (j < size BP.bb) {
      (idl, b) <- nth witness BP.bb j;
       if ( (idl, b) \in BP.bb') {
         (* Find the vote in vmap that belongs to voter id *)
         v <- Some (oget (onth (odflt [] BP.vmap.[idl]) 
              (find (fun (x : cipher * cipher *  vote) => x.`1 = b) 
              (odflt [] BP.vmap.[idl])))).`3;
         } else {
           v <- nth witness mL j;
         }
      dbb <- dbb ++ [(idl, v)];
       j  <- j + 1;
    }

    BP.r <$ Rho dbb;

    if (!(BP.setHcheck \subset fdom BP.vmap)) {
      BP.d <$ {0,1};
    } else {
      if (!valid) {
         BP.d <@ A.a2();
      } else {
          A.a3();
          if (!(BP.setHcheck \subset BP.setchecked)) {
            BP.d <$ {0,1};
          } else {
          if (!(BP.setHcheck \subset BP.sethappy)) {
            BP.d <@ A.a4();
          } 
          if (BP.setHcheck \subset BP.sethappy) {
              BP.pi  <@ S.prove(BP.pk, miniPublish BP.bb, BP.r);
              BP.d <@ A.a5(BP.r, BP.pi);
          }
        }
      }
    }
    return BP.d; 
  }
}. 

(***********************************************************************************************)
(********* Proof that MiniVoting satisfies MB-BPRIV structured as a sequence of games. *********)
(*********   We start by modyfing the left hand side.                                  *********)
(***********************************************************************************************)
    
(*** We start with a game G0L' that simply unpacks some of the procs in the security definitions ***)
local module G0L' (E:Scheme, P:Prover, Ve:Verifier, C:ValidInd, 
                   A:OMB_BPRIV_adv, H:HOracle.Oracle, G:GOracle.Oracle)  = {  

  module O  = MB_BPRIV_oracles(MV(E, P, Ve, C), H, G, Left)
  module A  = A(O)
  module MV = MV(E,P,Ve,C,H,G)
 
    proc main() : bool = {   
    var i, id, valid;
    var dbb,j,idl,b,v;
    
    BP.vmap       <- empty; 
    BP.pubmap     <- empty;
    BP.secmap     <- empty;
    BP.secmapD    <- empty;
    BP.bb0        <- [];
    BP.bb1        <- [];
    BP.setchecked <- fset0;
    BP.sethappy   <- fset0;
    BP.bbstar     <- None;

    H.init();
    G.init();

   (BP.pk, BP.sk) <@ MV.setup();

    (* registration *)
    i <- 0;
    while (i < card BP.setidents) {   
      id <- nth witness (elems BP.setidents) i;
      BP.secmap.[id] <- id;
      BP.pubmap.[id] <- id;
      if (id \in BP.setD) { 
        BP.secmapD.[id] <- oget BP.secmap.[id];
      }  
    i <- i + 1;
    }  

    (* adversary creates bulletin board *)
    BP.bb <@ A.a1(BP.pk, BP.secmapD, BP.pubmap);
    
    if (!(BP.setHcheck \subset fdom BP.vmap)) { 
      BP.d <$ {0,1};
    } else { 
       valid <@ MV.validboard(BP.bb, BP.pk);
       if (!valid) {  
         BP.d <@ A.a2();
        }  else { 
          A.a3();
          if (!BP.setHcheck \subset BP.setchecked) {
            BP.d <$ {0,1};
            } else {
              if (!(BP.setHcheck \subset BP.sethappy)){
                BP.d <@ A.a4();
               } 
               if (BP.setHcheck \subset BP.sethappy){  
                 dbb     <- [];
                  j      <- 0;
                  while (j < size BP.bb) {
                    (idl, b) <- nth witness BP.bb j;
                       v     <@ E(H).dec(BP.sk, idl, b);
                      dbb    <- dbb ++ [(idl, v)];
                        j    <- j + 1;
                  }
                  BP.r   <$ Rho dbb;
                  BP.pk  <- extractPk BP.sk;
                  BP.pi  <@ P(G).prove((BP.pk, miniPublish BP.bb, BP.r), (BP.sk, BP.bb));
                  BP.d   <@ A.a5(BP.r, BP.pi);                                                        
                }
              }
            } 
          } 
        return BP.d; 
      }   
  }.



(*** Lemma proving that G0L' is perfectly equivalent to the original definition ***)
local lemma MB_BPRIV_L_G0L'_equiv &m (H <: HOracle.Oracle{ -E, -BP, -G, -A, -C, -Ve, -P}) : 
    Pr[OMB_BPRIV_L(MV(E, P, Ve, C), A, H, G).main() @ &m : res] = 
    Pr[G0L'(E,P,Ve,C,A,H,G).main() @ &m : res].
proof.
 byequiv => //; proc; inline*; sim.   
qed.


(*** Game Description : G0L'' is just G0L' after moving out valid statement from nested if ***)
local module G0L'' (E:Scheme, P:Prover, Ve:Verifier, C:ValidInd, 
                    A:OMB_BPRIV_adv, H:HOracle.Oracle, G:GOracle.Oracle)  = {  

  module O  = MB_BPRIV_oracles(MV(E, P, Ve, C), H, G, Left)
  module A  = A(O)
  module MV = MV(E,P,Ve,C,H,G)
 
    proc main() : bool = {   
    var i, id, valid;
    var dbb,j,idl,b,v;
    
    BP.vmap       <- empty; 
    BP.pubmap     <- empty;
    BP.secmap     <- empty;
    BP.secmapD    <- empty;
    BP.bb0        <- [];
    BP.bb1        <- [];
    BP.setchecked <- fset0;
    BP.sethappy   <- fset0;
    BP.bbstar     <- None;

    H.init();
    G.init();

   (BP.pk, BP.sk) <@ MV.setup();

    (* registration *)
    i <- 0;
    while (i < card BP.setidents) {   
      id <- nth witness (elems BP.setidents) i;
      BP.secmap.[id] <- id;
      BP.pubmap.[id] <- id;
      if (id \in BP.setD) { 
        BP.secmapD.[id] <- oget BP.secmap.[id];
      }  
    i <- i + 1;
    }  

    (* adversary creates bulletin board *)
        BP.bb <@ A.a1(BP.pk, BP.secmapD, BP.pubmap);
           valid <@ MV.validboard(BP.bb, BP.pk);

    
    if (!(BP.setHcheck \subset fdom BP.vmap)) { 
      BP.d <$ {0,1};
    } else { 
       if (!valid) {  
         BP.d <@ A.a2();
        } else { 
          A.a3();
          if (!BP.setHcheck \subset BP.setchecked) {
            BP.d <$ {0,1};
          } else {
            if (!(BP.setHcheck \subset BP.sethappy)){
              BP.d <@ A.a4();
            } 
            if (BP.setHcheck \subset BP.sethappy){  
              dbb     <- [];
               j      <- 0;
              while (j < size BP.bb) {
                (idl, b) <- nth witness BP.bb j;
                   v     <@ E(H).dec(BP.sk, idl, b);
                  dbb    <- dbb ++ [(idl, v)];
                   j     <- j + 1;
              }
              BP.r   <$ Rho dbb;
              BP.pk  <- extractPk BP.sk;
              BP.pi  <@ P(G).prove((BP.pk, miniPublish BP.bb, BP.r), (BP.sk, BP.bb));
              BP.d <@ A.a5(BP.r, BP.pi);                                                        
            }
          }
        } 
      } 
    return BP.d; 
  }   
}.

(* Prove that G0L' and G0L'' are equivalent *)
local lemma G0L'_G0L''_equiv &m:
  Pr[G0L'(E,P,Ve,C,A,HRO.ERO,G).main() @ &m : res] 
  = Pr[G0L''(E,P,Ve,C,A,HRO.ERO,G).main() @ &m : res]. 
proof.
  byequiv => //. proc; simplify. 
  seq 15 15 : (
    ={glob HRO.ERO, glob A , glob C, glob P, glob E, glob G, 
      BP.pk, BP.sk, BP.pubmap,BP.bb,  BP.secmap, BP.d,
      BP.vmap,BP.setchecked, BP.setHcheck, BP.sethappy, BP.bb0, 
      BP.bb1, BP.secmapD, BP.setidents, BP.setD}
 );first by sim. 

  inline*.
  if{1}=>//=.
  + rcondt{2} 8; progress.
    + wp; while (true).
      + by seq 2: (true) =>//=. 
      by wp.
    rnd; wp =>//=.
    while{2} (0 <= i0{2} <= size bb{2}) (size bb{2} - i0{2}). 
    + progress.
      seq 2: ((0 <= i0 && i0 < size bb) /\ size bb - i0 = z) =>//=.
      + by auto.  
      + wp; if=>//=.
        + call{1} (C_vi_ll HRO.ERO HRO.ERO_o_ll).
          by auto=>/>; smt(). 
        by auto; smt(). 
      + by hoare; wp. 
    auto=>/>; progress. 
    + by rewrite size_ge0. 
    + by smt().
 
  rcondf{2} 8; progress.
  + wp; while (true).
    + by seq 2 : true.
    by wp. 
  by sim. 

qed. 
 
(*** Game Description : G0L is just G0L'' after putting tally in before if statements ***)
local module G0L (E:Scheme, P:Prover, Ve:Verifier, C:ValidInd, 
                  A:OMB_BPRIV_adv, H:HOracle.Oracle, G:GOracle.Oracle)  = {  

  module O  = MB_BPRIV_oracles(MV(E, P, Ve, C), H, G, Left)
  module A  = A(O)
  module MV = MV(E,P,Ve,C,H,G)
 
    proc main() : bool = {   
    var i, id, valid;
    var dbb,j,idl,b,v;
    
    BP.vmap       <- empty; 
    BP.pubmap     <- empty;
    BP.secmap     <- empty;
    BP.secmapD    <- empty;
    BP.bb0        <- [];
    BP.bb1        <- [];
    BP.setchecked <- fset0;
    BP.sethappy   <- fset0;
    BP.bbstar     <- None;

    H.init();
    G.init();

   (BP.pk, BP.sk) <@ MV.setup();

    (* registration *)
    i <- 0;
    while (i < card BP.setidents) {   
      id <- nth witness (elems BP.setidents) i;
      BP.secmap.[id] <- id;
      BP.pubmap.[id] <- id;
      if (id \in BP.setD) { 
        BP.secmapD.[id] <- oget BP.secmap.[id];
      }  
      i <- i + 1;
    }  

     (* adversary creates bulletin board *)
     BP.bb <@ A.a1(BP.pk, BP.secmapD, BP.pubmap);
     valid <@ MV.validboard(BP.bb, BP.pk);

     (* tally *)
     dbb     <- [];
      j      <- 0;
     while (j < size BP.bb) {
       (idl, b) <- nth witness BP.bb j;
          v     <@ E(H).dec(BP.sk, idl, b);
         dbb    <- dbb ++ [(idl, v)];
          j     <- j + 1;
      }
      BP.r   <$ Rho dbb;
      BP.pk  <- extractPk BP.sk;

     if (!(BP.setHcheck \subset fdom BP.vmap)) { 
       BP.d <$ {0,1};
       } else { 
         if (!valid) {  
           BP.d <@ A.a2();
           } else { 
             A.a3();
             if (!(BP.setHcheck \subset BP.setchecked)) {
               BP.d <$ {0,1};
               } else {
                 if (!(BP.setHcheck \subset BP.sethappy)){
                 BP.d <@ A.a4();
               } 
               if (BP.setHcheck \subset BP.sethappy){
                 BP.pi  <@ P(G).prove((BP.pk, miniPublish BP.bb, BP.r), (BP.sk, BP.bb));
                 BP.d <@ A.a5(BP.r, BP.pi);                                             
               }
             }
           } 
         } 
       return BP.d; 
     }   
   }.



(* Prove that G0L'' and G0L are equivalent *)
local lemma G0L''_G0L_equiv &m : 
  Pr[G0L''(E,P,Ve,C,A,HRO.ERO,G).main() @ &m : res] 
  = Pr[G0L(E,P,Ve,C,A,HRO.ERO,G).main() @ &m : res]. 
proof.

  byequiv => //. 
  proc; simplify.
        
  seq 16 16 : (={valid, glob HRO.ERO, glob A , glob C, glob P, glob E, glob G, 
                 BP.pk, BP.sk, BP.pubmap,BP.bb,  BP.secmap, BP.vmap,BP.setchecked, 
                 BP.setHcheck, BP.sethappy, BP.bb0, BP.bb1, BP.secmapD, BP.setidents, 
                 BP.setD, BP.d});
  first by sim.
  
  inline*.
  if{1}=>/>. 
  + rcondt{2} 6; progress.
    + wp; rnd; while (true).
      + wp; call(: true); first by conseq HRO.ERO_o_ll.
        by wp.
      by wp.
    rnd; wp; rnd{2} =>/>.
    while{2} (0 <= j{2} <= size BP.bb{2}) (size BP.bb{2} - j{2}).
    + progress.
      wp; call{1} (E_dec_ll HRO.ERO HRO.ERO_o_ll); wp.
      by auto=>/>; smt(). 
    auto=>/>; progress; smt(size_ge0 Rho_weight).
  rcondf{2} 6; progress.
  + wp; rnd; while (true).
    + wp; call(: true); first by conseq HRO.ERO_o_ll.
      by wp.
    by wp.
  
  if{1}.
  + rcondt{2} 6; progress.
    + wp; rnd; while(true).
      + wp; call(: true); first by conseq HRO.ERO_o_ll.
        by wp.
      by wp.  
    call(: true). (* FIXME: check definition.maybe a BP.d <${0,1} would be better *)
    wp; rnd{2}.
    while{2} (0 <= j{2} <= size BP.bb{2}) (size BP.bb{2} - j{2}).
    + progress.
      wp; call{1} (E_dec_ll HRO.ERO HRO.ERO_o_ll); wp.
      by auto=>/>; smt(). 
    by auto=>/>; progress; smt(size_ge0 Rho_weight).   
  rcondf{2} 6; progress.
  + wp; rnd; while(true).
    + wp; call(: true); first by conseq HRO.ERO_o_ll.
      by wp.
    by wp.  

  swap{2} 6 -5.
  seq 1 1: ( ={ valid, HRO.ERO.m, glob A, glob C, glob P, glob E, glob G, BP.pk, BP.sk,
                BP.pubmap, BP.bb, BP.secmap, BP.vmap, BP.setchecked, BP.setHcheck,
                BP.sethappy, BP.bb0, BP.bb1, BP.secmapD, BP.setidents, BP.setD, BP.d} 
             /\ BP.setHcheck{1} \subset fdom BP.vmap{1}
             /\ valid{1}). 
    call(: ={glob HRO.ERO, glob G, BP.bb, BP.vmap, BP.secmap, BP.pubmap, BP.setchecked, 
             BP.sethappy});
      [1..3: sim]. 
    by auto.

  if{1} =>/>.
  + rcondt{2} 6; progress. 
    + wp; rnd; while(true).
      + wp; call(: true); first by conseq HRO.ERO_o_ll.
        by wp.
      by wp.
    rnd; wp; rnd{2}.
    while{2} (0 <= j{2} <= size BP.bb{2}) (size BP.bb{2} - j{2}).
    + progress.
      wp; call{1} (E_dec_ll HRO.ERO HRO.ERO_o_ll); wp.
      by auto=>/>; smt(). 
    by auto=>/>; progress; smt(size_ge0 Rho_weight).   
  rcondf{2} 6; progress.
  + wp; rnd; while(true).
    + wp; call(: true); first by conseq HRO.ERO_o_ll.
      by wp.
    by wp.

  if{1}=>/>.
  + rcondt{2} 6; progress. 
    + wp; rnd; while(true).
      + wp; call(: true); first by conseq HRO.ERO_o_ll.
        by wp.
      by wp.
    rcondf{1} 2; progress.
    + by call(: true). 
    rcondf{2} 7; progress.
    + call(: true); wp; rnd; while(true).
      + wp; call(: true); first by conseq HRO.ERO_o_ll.
        by wp.
      by wp.
    call (: true). (* FIXME: it should have RO access, maybe *)
    wp; rnd{2}; while{2} (0 <= j{2} <= size BP.bb{2}) (size BP.bb{2} - j{2}).
    + progress.
      wp; call{1} (E_dec_ll HRO.ERO HRO.ERO_o_ll); wp.
      by auto=>/>; smt(). 
    by auto=>/>; progress; smt(size_ge0 Rho_weight).   
  rcondt{1} 1; progress.
  rcondt{2} 7; progress.
  + seq 5: (BP.setHcheck \subset BP.sethappy).
    + wp; rnd; while(true).
      + wp; call(: true); first by conseq HRO.ERO_o_ll.
        by wp.
      by auto. 
    if=>//=. 
    by call(: true).
  rcondf{2} 6; progress.
  + wp; rnd; while(true).
    + wp; call(: true); first by conseq HRO.ERO_o_ll.
      by wp.
    by auto. 
  by sim. 
qed.

(*** In G1L, we simulate the proof of correct tally, still in the left world  ***)
local module G1L (E:Scheme, Ve:Verifier, C:ValidInd, A:OMB_BPRIV_adv, H:HOracle.Oracle, S:Simulator)  = {

  module O  = MB_BPRIV_oracles(MV(E, P, Ve, C), H, S, Left)
  module A  = A(O)
  module MV = MV(E,P,Ve,C,H,S)
 
    proc main() : bool = {   
    var i, id, valid;
    var dbb,j,idl,b,v;

    
    BP.vmap       <- empty; 
    BP.pubmap     <- empty;
    BP.secmap     <- empty;
    BP.secmapD    <- empty;
    BP.bb0        <- [];
    BP.bb1        <- [];
    BP.setchecked <- fset0;
    BP.sethappy   <- fset0;
    BP.bbstar     <- None;

    H.init();
    S.init();

   (BP.pk, BP.sk) <@ MV.setup();

    (* registration *)
    i <- 0;
    while (i < card BP.setidents) {   
      id <- nth witness (elems BP.setidents) i;
      BP.secmap.[id] <- id;
      BP.pubmap.[id] <- id;
      if (id \in BP.setD) { 
        BP.secmapD.[id] <- oget BP.secmap.[id];
      }  
    i <- i + 1;
    }  

    (* adversary creates first bulletin board *)
     BP.bb <@ A.a1(BP.pk, BP.secmapD, BP.pubmap);
     valid <@ MV.validboard(BP.bb, BP.pk);

      dbb     <- [];
       j      <- 0;
     while (j < size BP.bb) {
       (idl, b) <- nth witness BP.bb j;
          v     <@ E(H).dec(BP.sk, idl, b);
         dbb    <- dbb ++ [(idl, v)];
          j     <- j + 1;
     }
     BP.r   <$ Rho dbb;
     BP.pk  <- extractPk BP.sk;

    if (!(BP.setHcheck \subset fdom BP.vmap)) { 
      BP.d <$ {0,1};
    } else { 
       if (!valid) {  
         BP.d <@ A.a2();
        }  else { 
          A.a3();
          if (!BP.setHcheck \subset BP.setchecked) {
            BP.d <$ {0,1};
          } else {
          if (!(BP.setHcheck \subset BP.sethappy)){
            BP.d <@ A.a4();
          } 
          if (BP.setHcheck \subset BP.sethappy){         
            BP.pi  <@ S.prove(BP.pk, miniPublish BP.bb, BP.r);
            BP.d   <@ A.a5(BP.r, BP.pi);    
          }
        }
      } 
    } 
  return BP.d; 
  }   
}.

(*** Losslessness for BZK, useful in the ZK part a bit further down  ***)

local lemma BZK_a1_ll (H <: HOracle.Oracle { -A, -BP }) (G <: GOracle.POracle { -A, -BP }) : 
 islossless H.init =>  islossless H.o => 
 islossless G.o => islossless BZK(E, P, C, Ve, A, H, G).a1. 
proof. 
move => Hi_ll Ho_ll Go_ll. 
proc.  

(* first look at everything up to the if statements *)
seq 18 : (true).

rnd;wp;while (0 <= j <= size BP.bb);progress. 
wp;auto;call(_:true).   
auto.   
wp;skip; smt(). 
wp;call(_:true);  [ auto | auto | auto | auto | auto ]. 

while (0 <= i <= card BP.setidents). 
auto;progress;smt().  
wp;call(_: true). 
  call(_:true);wp;skip.
  progress. smt(@FSet). rewrite size_ge0. 
auto. swap 15  -14.  swap 15 -14.  
sp;while(0 <= j <= size BP.bb)(size BP.bb - j). progress. auto. sp. call(E_dec_ll H).
auto;progress;smt().
call(A_a1_ll (<: BZK(E,P,C,Ve,A,H,G).O )). proc;inline*. 
if => //. auto. 
  
  (* vote oracle *)
  call(E_enc_ll H Ho_ll). 
  auto. 
  call(E_enc_ll H Ho_ll). 
  auto. 

  (* board oracle *)
  proc;inline*;auto. 

  (* before A.a1 call *)
  while (0 <= i <= card BP.setidents) (card BP.setidents - i);progress. 

auto;progress;smt().  
wp;call(E_kg_ll H Ho_ll). 
call(_:true);wp;skip. 
  by progress; [ smt(@FSet) | smt() | rewrite size_ge0 | smt() | exact Rho_weight].

  (* if statements *)

  (* setHcheck \subset fdom vmap? *)
  if => //. rnd;skip;progress. smt(@DBool). inline*. 

  seq 7 : (BP.setHcheck \subset fdom BP.vmap).
  wp. while (0 <= i0 <= size bb). wp;sp. 
  if => //. call(_:true). auto. auto;progress;smt().  
  auto;progress;smt(). 
  auto;progress.
  wp. while(0 <= i0 <= size bb) (size bb - i0). progress. 
  sp;wp. if => //. call(C_vi_ll H Ho_ll). auto;progress;smt(). 
  auto;progress;smt(). 
  auto;progress. rewrite size_ge0. smt(). 

  (* board valid? *)
  if => //. call(A_a2_ll (<: BZK(E,P,C,Ve,A,H,G).O)). 
  
  (* O.board *)
  proc;inline*;auto.
  auto;progress. 
  seq 1 : true. 
  auto. 
  call (A_a3_ll (<: BZK(E,P,C,Ve,A,H,G).O)). 

  (* verify oracle *)
  proc;inline*;auto. 
  auto;progress. 

  (* setHcheck \subset setchecked? *)
  if => //. rnd;skip;progress. smt(@DBool).

  (* setHcheck \subset sethappy? *)
  if => //.
  call(A_a4_ll (<: BZK(E,P,C,Ve,A,H,G).O)). auto;progress. 

  hoare. auto. progress. 
  hoare. wp;sp. 
  while(0 <= i0 <= size bb). 
  wp;sp. 
  if => //. call(_:true); first by auto. 
  auto;progress;smt(). 
  auto;progress;smt(). 
  auto;progress.
  trivial. 

  by hoare. 
  trivial. 
  qed. 


lemma BZK_a2_ll (H <: HOracle.Oracle { -A, -BP }) (G <: GOracle.POracle { -A, -BP }) : 
  islossless H.o =>
  islossless G.o => 
  islossless BZK(E,P,C,Ve,A,H,G).a2. 
proof.
  move =>  Ho_ll Go_ll. 
  proc; inline*.
  if => //. 
  call(A_a5_ll (<: BZK(E,P,C,Ve,A,H,G).O)).
  proc;inline*;auto. 
  by auto. 
qed.
    
(************************************************************************)

lemma BZK_a2_ll' (H <: HOracle.Oracle { -A, -BP }) 
                 (G <: GOracle.POracle { -A, -H, -BP })
                 (P <: Prover { -E, -C, -Ve, -A, -ZK_L, -BPS, -BP, -H, -G }) :
  islossless H.o => 
  islossless G.o => 
  islossless P(G).prove =>
  islossless BZK(E,P,C,Ve,A,H,G).a2. 
proof. 
  move => Ho_ll Go_ll Pp_ll. 
  proc. 
  if => //. 
  call(A_a5_ll (<: BZK(E,P,C,Ve,A,H,G).O)).
  proc;inline*;auto. 
  by auto. 
qed. 

(****************************************************************************************************)
(***** Here starts the ZK part ending with a lemma proving that the advantage in distinguishing *****)
(***** between G0L and G1L is bounded by |ZK_L - ZK_R| + 2*VFR advantage.                       *****)
(****************************************************************************************************)

(*** Left game for ZK without checking relation ***)

local module ZKFL(E:Scheme, R:VotingRelation', P:Prover, A:VotingAdvZK, 
                  H:HOracle.Oracle, O:GOracle.Oracle) = {
  proc main() : bool = {
    var p;
    O.init();
    (BPS.s, BPS.w) <@ A(H,O).a1();
       BPS.rel     <@ R(E,H).main(BPS.s, BPS.w);
      p            <@ P(O).prove(BPS.s, BPS.w);
    BPS.p          <- Some p;
    BPS.b          <@ A(H,O).a2(BPS.p);
    return BPS.b;
  }
}.

(******************** Right game for ZK without checking relation *******************)
local module ZKFR(E:Scheme, R:VotingRelation', S:Simulator, A:VotingAdvZK, H:HOracle.Oracle) = {
  proc main() : bool = {
    var p;
    S.init();
    (BPS.s, BPS.w) <@ A(H,S).a1();
       BPS.rel     <@ R(E,H).main(BPS.s, BPS.w);
      p            <@ S.prove(BPS.s);
    BPS.p          <- Some p;
    BPS.b          <@ A(H,S).a2(BPS.p);
    return BPS.b;
  }
}.


(******************** Relate ZKFL to non local module ZK_L ***********************)

local lemma ZKFL_ZKL &m :
    `|Pr[ZKFL(E,R,P,BZK(E,P,C,Ve,A),HRO.ERO,G).main() @ &m : res] - 
      Pr[ZK_L(R(E,HRO.ERO),P,BZK(E,P,C,Ve,A,HRO.ERO),G).main() @ &m : res]| <=
      Pr[ZK_L(R(E,HRO.ERO),P,BZK(E,P,C,Ve,A,HRO.ERO),G).main() @ &m : !BPS.rel]. 
proof.
byequiv (_ : ={glob A, glob C, glob R, glob P, glob Ve, glob E, glob G, 
               BP.setHcheck, BP.secmapD, BP.pubmap, BP.secmap,
               BP.setD, BP.setidents, BP.d, BP.setH, BP.bb1, BP.bb0, BP.r, BP.sethappy,  glob HRO.ERO,
               BP.setchecked, BP.vmap, BP.pk, BP.bb, BP.valid} ==> 
             ={BPS.rel} /\ (BPS.rel{2} => ={res})) : (!BPS.rel) => //;last by smt(). 
proc.  
seq 3 3 : (={glob P, glob R, glob HRO.ERO, glob G, glob A, glob E, glob C, glob Ve, 
             BPS.s, BPS.w, BPS.rel, BP.secmapD, BP.setD, BP.setidents, BP.setH, BP.bb1, 
             BP.bb0, BP.setHcheck, BP.r, BP.d, BP.pubmap, BP.secmap,
             BP.sethappy, BP.setchecked, BP.vmap, BP.pk, BP.bb, BPS.rel, BPS.s, BPS.w, BP.valid}). 
call(_: ={glob HRO.ERO});first by sim.
call(_: ={glob HRO.ERO, glob G, glob A, glob C, BP.d,  glob E, BP.secmapD, 
          BP.setD, BP.setidents, BP.pk, BP.bb, BP.pubmap, BP.secmap, BP.setHcheck,
          BP.setH, BP.bb1, BP.bb0, BP.r, BP.sethappy, BP.setchecked, BP.vmap, BP.valid}); first by  sim. 
call(_: ={glob HRO.ERO}). skip. progress. 
if{2}; first by sim. 
call{1} (BZK_a2_ll' HRO.ERO G P HRO.ERO_o_ll Go_ll); first apply (PS_p_ll G Go_ll). 
call{2} (BZK_a2_ll' HRO.ERO G P HRO.ERO_o_ll Go_ll); first apply (PS_p_ll G Go_ll). 
by wp; call{1} (PS_p_ll G Go_ll).
qed. 


(******************* Relate ZKFR to non local module ZK_R *************************)

local lemma ZKFR_ZKR &m :
    `|Pr[ZKFR(E,R,S,BZK(E,P,C,Ve,A),HRO.ERO).main() @ &m : res] - 
      Pr[ZK_R(R(E,HRO.ERO),S,BZK(E,P,C,Ve,A,HRO.ERO)).main() @ &m : res]| <=
      Pr[ZK_R(R(E,HRO.ERO),S,BZK(E,P,C,Ve,A,HRO.ERO)).main() @ &m : !BPS.rel]. 
proof.  
byequiv (: ={ BP.pi, glob A, glob C, glob R, glob P, glob Ve, glob E, glob S, BP.setHcheck, 
                BP.secmapD, BP.pubmap, BP.secmap, BP.setD, BP.setidents, BP.d, BP.setH, BP.bb1, 
                BP.bb0, BP.r, BP.sethappy, glob HRO.ERO, BP.setchecked, BP.vmap, BP.pk, BP.bb, BP.valid} 
             ==> 
               ={BPS.rel} /\ (BPS.rel{2} => ={res})) : (!BPS.rel) => //;last by smt(). 
  proc. 
  seq 3 3 : (={ glob P, glob R, glob HRO.ERO, glob S, glob A, glob E, glob C, glob Ve, BPS.s,
                BPS.w, BPS.rel, BP.secmapD, BP.setD, BP.setidents, BP.setH, BP.bb1, BP.bb0, 
                BP.setHcheck, BP.r, BP.d, BP.pubmap, BP.secmap, BP.sethappy, BP.setchecked, 
                BP.vmap, BP.pk, BP.bb, BPS.rel, BPS.s, BPS.w, BP.valid}). 
  call(_: ={glob HRO.ERO});first by sim.  
  call(_: ={glob HRO.ERO, glob S, glob A, glob E, BP.secmapD, BP.setD, 
            BP.setidents, BP.pk, BP.bb, BP.pubmap, BP.valid,
            BP.secmap, BP.setH, BP.bb1, BP.bb0, BP.r, BP.sethappy,BP.setHcheck,
            glob C,BP.setchecked, BP.vmap, BP.d}); first by sim.
  call(_: ={glob HRO.ERO}). skip. progress. 
  if{2}; first by sim.  
  call{1} (BZK_a2_ll HRO.ERO S HRO.ERO_o_ll So_ll).  
  call{2} (BZK_a2_ll HRO.ERO S HRO.ERO_o_ll So_ll).
  wp; call{1} Sp_ll.  
  by auto.
qed.  

(*** Lemma bounding the probability that the relation does not hold in ZK_L by ***)
(*** the probability of returning true in the VFR game.                        ***)

local lemma ZKL_rel &m (G <: GOracle.Oracle { -A, -BPS, -BP, -BS, -Ve, -E, -HRO.ERO, -R, -C })
                       (P <: Prover { -E, -C, -Ve, -A, -R, -BPS, -BP, -BS, -HRO.ERO, -G}) :
    islossless G.o => islossless P(G).prove =>
    Pr[ZK_L(R(E,HRO.ERO), P, BZK(E,P,C,Ve,A,HRO.ERO), G).main() @ &m : !BPS.rel] <=
    Pr[VFR(E, BVFR(MV(E,P,Ve,C), A), R(E), HRO.ERO, G).main() @ &m : res].  
proof. 
move => (* Ho_ll *) Go_ll Pp_ll. 
byequiv (_: ={glob A, glob E, glob P, glob Ve, glob C,  glob HRO.ERO, glob G, glob R, BP.setHcheck,
              BP.setidents, BP.setD, BP.secmapD, BP.setH} ==> _) => //. 
proc.  
call{1} (BZK_a2_ll' HRO.ERO G P HRO.ERO_o_ll Go_ll Pp_ll). 
inline*.
 seq 24 24 : (BPS.rel{1} = rel{2}).   
  call(_: ={glob HRO.ERO}); first by sim.
swap{2} 1 16. swap{1} [10..12] -9. swap{2} [3..6] -2. swap{2} [5..6] 3. swap{1} 13 -8. 
seq 21 23 : (={glob P, glob R,glob HRO.ERO, glob A, glob E, glob C, glob Ve,
               BP.secmapD, BP.setD, BP.setidents, BP.setH, BP.bb1, BP.bb0, BP.setHcheck, 
               BP.pubmap, BP.secmap, BP.setHcheck,
               BP.vmap, BP.bb}/\ BP.pk{1} = BS.pk{2} /\ miniPublish BP.bb{1} = miniPublish bb{2} 
             /\ BP.r{1} = r{2} /\ BP.sk{1} = BS.sk{2} /\ BP.bb{1} = bb{2}
             /\ BP.pk{1} = extractPk BP.sk{1}
).
wp;rnd;wp. 
while (j{1} = i{2} /\ BP.sk{1} = BS.sk{2} /\ dbb{1} = ubb{2} /\ BP.bb{1} = bb{2} 
       /\ ={glob HRO.ERO, glob E}).
+ sim. 
  progress; smt(). 
wp.  
call(_: ={glob HRO.ERO, glob G, BP.secmap, BP.pubmap, BP.setH, 
          BP.pk, glob E, BP.bb0, BP.bb1, BP.vmap}); [1..4: by sim]. 
while(i{1} = i0{2} /\ ={BP.setidents, BP.secmap, BP.pubmap, BP.setD, BP.secmapD});first by sim. 
auto. call(Ekgen_extractPk HRO.ERO). call(_:true). while(={w, HRO.ERO.m}).  
auto;progress. auto;progress. 
smt(). 
wp.  

if{1} => //. rnd{1};auto;progress. 
sp. 
seq 2 0 : (
   bb{1} = BP.bb{1} /\
  pk{1} = BP.pk{1} /\
  (={glob P, glob R, HRO.ERO.m, glob A, glob E, glob Ve, BP.secmapD,
       BP.setD, BP.setidents, BP.setH, BP.bb1, BP.bb0, BP.setHcheck,
       BP.pubmap, BP.secmap, BP.setHcheck, BP.vmap, BP.bb} /\
   BP.pk{1} = BS.pk{2} /\
   miniPublish BP.bb{1} = miniPublish bb{2} /\
   BP.r{1} = r{2} /\
   BP.sk{1} = BS.sk{2} /\ BP.bb{1} = bb{2} /\ BP.pk{1} = extractPk BP.sk{1}) /\
  ! ! (BP.setHcheck{1} \subset fdom BP.vmap{1})
).
wp. while{1} (0 <= i0{1} <= size bb{1}) (size bb{1} - i0{1}). progress.  
wp;sp. if => //. call(C_vi_ll HRO.ERO HRO.ERO_o_ll). auto;progress;smt(). 
auto;progress;smt(). 
auto;progress. rewrite size_ge0. smt().  

if{1} => //. call{1} (A_a2_ll (<: BZK(E,P,C,Ve,A,HRO.ERO,G).O)). proc;inline*;auto.
by proc. 
auto;progress.  

seq 1 0 : (
(bb{1} = BP.bb{1} /\
   pk{1} = BP.pk{1} /\
   (={glob P, glob R, HRO.ERO.m,  glob E, glob Ve, BP.secmapD,
        BP.setD, BP.setidents, BP.setH, BP.bb1, BP.bb0, BP.setHcheck,
        BP.pubmap, BP.secmap, BP.setHcheck, BP.vmap, BP.bb} /\
    BP.pk{1} = BS.pk{2} /\
    miniPublish BP.bb{1} = miniPublish bb{2} /\
    BP.r{1} = r{2} /\
    BP.sk{1} = BS.sk{2} /\ BP.bb{1} = bb{2} /\ BP.pk{1} = extractPk BP.sk{1}) /\
   ! ! (BP.setHcheck{1} \subset fdom BP.vmap{1})) /\
  ! !BP.valid{1}
).
call{1} (A_a3_ll (<: BZK(E,P,C,Ve,A,HRO.ERO,G).O)). proc;inline*;auto. by proc. 
auto;progress. 

if{1} => //. auto. 
if{1} => //. 
call{1} (A_a4_ll (<: BZK(E,P,C,Ve,A,HRO.ERO,G).O)). by proc. 
auto;progress. 

(******* ******)
if{1}. wp. call{1} (Pp_ll).
  trivial. auto.
qed.


(*** Lemma bounding the probability that the relation does not hold in ZK_R by ***)
(*** the probability of returning true in the VFR game.                        ***)

local lemma ZKR_rel &m (S <: Simulator { -E, -C, -P, -Ve, -A, -R, -BPS, -BP, -BS, -HRO.ERO, -G }) :
    islossless S.o => islossless S.prove =>
    Pr[ZK_R(R(E,HRO.ERO), S, BZK(E,P,C,Ve,A,HRO.ERO) ).main() @ &m : !BPS.rel] <=
    Pr[VFR(E, BVFR(MV(E,P,Ve,C), A), R(E), HRO.ERO, S).main() @ &m : res].  
proof. 
move =>  So_ll Sp_ll. 
byequiv (_: ={glob A, glob E, glob S, glob Ve, glob C,  glob HRO.ERO, glob R, BP.setHcheck,
              BP.setidents, BP.setD, BP.secmapD, BP.setH} ==> _) => //. 
proc.  
call{1} (BZK_a2_ll HRO.ERO S HRO.ERO_o_ll So_ll ). 
inline*.
 seq 24 24 : (BPS.rel{1} = rel{2}).   
  call(_: ={glob HRO.ERO}); first by sim.
  swap{2} 1 16. swap{1} [10..12] -9. swap{2} [3..6] -2. swap{2} [5..6] 3. swap{1} 13 -8. 
seq 21 23 : (={glob S, glob R,glob HRO.ERO, glob A, glob E, glob C, glob Ve,
               BP.secmapD, BP.setD, BP.setidents, BP.setH, BP.bb1, BP.bb0, BP.setHcheck, 
               BP.pubmap, BP.secmap, BP.setHcheck,
               BP.vmap, BP.bb}/\ BP.pk{1} = BS.pk{2} /\ miniPublish BP.bb{1} = miniPublish bb{2} 
             /\ BP.r{1} = r{2} /\ BP.sk{1} = BS.sk{2} /\ BP.bb{1} = bb{2}
             /\ BP.pk{1} = extractPk BP.sk{1}
).
wp;rnd;wp. 

while(j{1} = i{2} /\ BP.sk{1} = BS.sk{2} /\ dbb{1} = ubb{2} /\ BP.bb{1} = bb{2} 
             /\ ={glob HRO.ERO, glob E}); first by sim; progress; smt(). 
wp.  
call(_: ={glob HRO.ERO, glob S, BP.secmap, BP.pubmap, BP.setH, BP.pk, 
          glob E, BP.bb0, BP.bb1, BP.vmap});[1..4: by sim]. 
while(i{1} = i0{2} /\ ={BP.setidents, BP.secmap, BP.pubmap, BP.setD, BP.secmapD});first by sim. 
auto. call(Ekgen_extractPk HRO.ERO). call(_:true). while(={w, HRO.ERO.m}).  
auto;progress. auto;progress. 
smt(). 
wp.  
if{1} => //. rnd{1};auto;progress. 
sp. 
seq 2 0 : (
   bb{1} = BP.bb{1} /\
  pk{1} = BP.pk{1} /\
  (={glob S, glob R, HRO.ERO.m, glob A, glob E, glob Ve, BP.secmapD,
       BP.setD, BP.setidents, BP.setH, BP.bb1, BP.bb0, BP.setHcheck,
       BP.pubmap, BP.secmap, BP.setHcheck, BP.vmap, BP.bb} /\
   BP.pk{1} = BS.pk{2} /\
   miniPublish BP.bb{1} = miniPublish bb{2} /\
   BP.r{1} = r{2} /\
   BP.sk{1} = BS.sk{2} /\ BP.bb{1} = bb{2} /\ BP.pk{1} = extractPk BP.sk{1}) /\
  ! ! (BP.setHcheck{1} \subset fdom BP.vmap{1})
).

 wp. while{1} (0 <= i0{1} <= size bb{1}) (size bb{1} - i0{1}). progress.  
wp;sp. if => //. call(C_vi_ll HRO.ERO HRO.ERO_o_ll). auto;progress;smt(). 
auto;progress;smt(). 
auto;progress. 
rewrite size_ge0. smt().  

if{1} => //. call{1} (A_a2_ll (<: BZK(E,P,C,Ve,A,HRO.ERO,S).O)). 
proc;inline*;auto.
by proc. 
auto;progress.  

seq 1 0 : (
(bb{1} = BP.bb{1} /\
   pk{1} = BP.pk{1} /\
   (={glob R, HRO.ERO.m,  glob E, glob Ve, BP.secmapD,
        BP.setD, BP.setidents, BP.setH, BP.bb1, BP.bb0, BP.setHcheck,
        BP.pubmap, BP.secmap, BP.setHcheck, BP.vmap, BP.bb} /\
    BP.pk{1} = BS.pk{2} /\
    miniPublish BP.bb{1} = miniPublish bb{2} /\
    BP.r{1} = r{2} /\
    BP.sk{1} = BS.sk{2} /\ BP.bb{1} = bb{2} /\ BP.pk{1} = extractPk BP.sk{1}) /\
   ! ! (BP.setHcheck{1} \subset fdom BP.vmap{1})) /\
  ! !BP.valid{1}
).
call{1} (A_a3_ll (<: BZK(E,P,C,Ve,A,HRO.ERO,S).O)). proc;inline*;auto. by proc. 
auto;progress. 

if{1} => //. auto. 
if{1} => //. 
call{1} (A_a4_ll (<: BZK(E,P,C,Ve,A,HRO.ERO,S).O)). by proc. 
auto;progress. 

(******* ******)
if{1}. wp. call{1} (Sp_ll).
  trivial. auto.
qed.


(************************* Lemma bounding ZKFL - ZK_L by VFR advantage ******************************)

local lemma ZKFL_ZKL_VFR &m :
  `|Pr[ZKFL(E, R, P, BZK(E,P,C,Ve,A), HRO.ERO, G).main() @ &m : res] - 
    Pr[ZK_L(R(E,HRO.ERO), P, BZK(E,P,C,Ve,A, HRO.ERO), G).main() @ &m : res]| <=
    Pr[VFR(E, BVFR(MV(E,P,Ve,C), A), R(E), HRO.ERO, G).main() @ &m : res]. 
proof. 
have := ZKFL_ZKL &m. move => H0.
have H1 : Pr[ZK_L(R(E,HRO.ERO), P, BZK(E,P,C,Ve,A,HRO.ERO), G).main() @ &m : !BPS.rel] <=
    Pr[VFR(E, BVFR(MV(E,P,Ve,C), A), R(E), HRO.ERO, G).main() @ &m : res].  
rewrite (ZKL_rel &m G P Go_ll). apply (PS_p_ll G Go_ll). smt(). 
qed. 

(************************* Lemma bounding ZKFR - ZK_R by VFR advantage ******************************)

local lemma ZKFR_ZKR_VFR &m : 
    `|Pr[ZKFR(E,R,S,BZK(E,P,C,Ve,A),HRO.ERO).main() @ &m : res] - 
      Pr[ZK_R(R(E,HRO.ERO), S, BZK(E,P,C,Ve,A,HRO.ERO)).main() @ &m : res]| <=
      Pr[VFR(E,BVFR(MV(E,P,Ve,C),A), R(E), HRO.ERO, S).main() @ &m : res]. 
proof. 
have := ZKFR_ZKR &m. move => H0.
have H1 : Pr[ZK_R(R(E,HRO.ERO), S, BZK(E,P,C,Ve,A,HRO.ERO)).main() @ &m : !BPS.rel] <=
    Pr[VFR(E, BVFR(MV(E,P,Ve,C), A), R(E), HRO.ERO, S).main() @ &m : res].  
rewrite (ZKR_rel &m S So_ll). apply (Sp_ll). smt(). 
qed.     


(**** Prove that G0L is equvalent to ZKFL with BZK as input ****)

local lemma G0_L_ZKFL_equiv &m :
  Pr[G0L(E, P, Ve, C, A, HRO.ERO, G).main() @ &m : res] =
  Pr[ZKFL(E, R, P, BZK(E,P,C,Ve,A), HRO.ERO, G).main() @ &m : res]. 

  proof.
 
    byequiv (_: ={BP.pi, glob A, glob E, glob P, glob Ve, glob C, glob HRO.ERO, glob G, glob R,
    BP.setidents, BP.setD, BP.secmapD, BP.setH, BP.bb0, BP.bb1, BP.setHcheck} ==> _) => //.

    proc;inline*.  

    swap{2} 1 12;wp. 
  
    seq 18 16 : (={glob HRO.ERO, glob A, glob C, glob P, glob Ve, glob E, glob G, BP.secmapD,
               BP.setHcheck, BP.secmapD, BP.setD, BP.setidents, BP.setH, BP.bb1, BP.bb0, BP.bb,
              BP.sethappy, BP.vmap, BP.pk, BP.sk, BP.setchecked, BP.secmap, BP.pubmap}
    /\ BP.pk{2} = extractPk BP.sk{2}).

    call(_: ={glob HRO.ERO, glob G, glob E, BP.pk, BP.secmapD, BP.pubmap, 
              BP.setH, BP.secmap, BP.bb1, BP.bb0, BP.vmap}); [1..4:by sim].
  
  while (={i, BP.setidents, BP.setD, BP.secmap, BP.pubmap, BP.secmapD, BP.vmap});auto.
    swap{1} 13 1. 
  call(_ : true).  call(E_kgen_extractpk HRO.ERO).  
  while (={w, HRO.ERO.m }); auto; progress;  smt(). 
  swap{1} [8..11] -7.  swap{1} 12 -5. swap{1} 5 2. 
 
seq 6 5 : (
    ={glob HRO.ERO, glob A, glob C, glob P, glob Ve, glob E, glob G,
      BP.secmapD, BP.setHcheck, BP.setD, BP.setidents, BP.setH,
      BP.bb0, BP.bb1, BP.bb, BP.sethappy, BP.vmap, BP.pk, BP.sk, BP.setchecked, BP.secmap, BP.pubmap, BP.r}
    /\ (BP.pk{2} = extractPk BP.sk{2})
    /\ pk0{1} = BP.pk{1}
).

swap{2} 5 -1. wp;rnd. 
while(={j, dbb, BP.sk, glob HRO.ERO, glob E, BP.bb}); first by sim. 
auto;progress. 

(*************   Starting Cases                                    ***********)
(*************   case(!(BP.setHcheck{2} \subset fdom BP.vmap{2}))  ***********)

case(!(BP.setHcheck{2} \subset fdom BP.vmap{2})).
rcondt{2} 1;progress. 
rcondt{1} 7;progress. auto.
   while(true); auto.
    swap{1} 7 -6. 
    case((BP.setHcheck{2} \subset fdom BP.vmap{2}) /\ BP.valid{2} /\ 
        (BP.setHcheck{2} \subset BP.setchecked{2}) /\ (BP.setHcheck{2} \subset BP.sethappy{2})).
    +rcondt{2} 7.
    auto. call(_: true). auto.  call(_:true);auto.

call{2} (A_a5_ll (<: BZK(E,P,C,Ve,A,HRO.ERO,G).O)).
proc. auto. call(_: true). auto. auto. proc. auto. auto. apply(Go_ll).
wp. while{1} (0 <= i0{1} <= size bb{1}) (size bb{1} - i0{1}). 
progress. wp;sp. 
if => //. 
call (C_vi_ll HRO.ERO HRO.ERO_o_ll). auto;progress;smt(). auto;progress;smt(). 
    call{2}(PS_p_ll G). apply(Go_ll).
 call{2}(R_m_ll).
    auto.
+rcondf{2} 7;auto.
 
   call(_ : true). auto. call(_: true). auto. auto.
while{1} (0 <= i0{1} <= size bb{1}) (size bb{1} - i0{1});progress. 
wp;sp.
if => //. call(C_vi_ll HRO.ERO HRO.ERO_o_ll). auto;progress;smt().  auto;progress;smt(). 
    call{2}(PS_p_ll G). apply(Go_ll).
 call{2}(R_m_ll).
wp. rnd. skip;progress.  rewrite size_ge0. smt(). 
 
 
(*************   case((BP.setHcheck{2} \subset fdom BP.vmap{2})).      ***********)

+ rcondf{2} 1;  auto.
+ rcondf{1} 7 ; auto.  while(true); auto.
  
seq 6 7 : (
   (={HRO.ERO.m, glob A, glob C, glob P, glob Ve, glob E, glob G, BP.secmapD,
       BP.setHcheck, BP.setD, BP.setidents, BP.setH, BP.bb0, BP.bb1, BP.bb,
       BP.sethappy, BP.vmap, BP.pk, BP.sk, BP.setchecked, BP.secmap,
       BP.pubmap, BP.r} /\
   BP.pk{2} = extractPk BP.sk{2} /\ pk0{1} = BP.pk{1}) /\ bb{1} = BP.bb{2} /\
  (BP.setHcheck{2} \subset fdom BP.vmap{2})
  /\ valid{1} = BP.valid{2}
).
wp. while(={i0, bb, e1, e2, HRO.ERO.m, glob C} /\ pk0{1} = pk{2}); first by sim. 
auto;progress. 
 
if => //.  
case((BP.setHcheck{2} \subset fdom BP.vmap{2}) /\ BP.valid{2} /\ 
      (BP.setHcheck{2} \subset BP.setchecked{2}) /\ (BP.setHcheck{2} \subset BP.sethappy{2})). 
rcondt{2} 7;progress. 
wp. call(_:true);auto. call(_:true);auto. call(_:true);auto. 
call{2} (A_a5_ll (<: BZK(E,P,C,Ve,A,HRO.ERO,G).O)). proc;inline*;auto. proc;auto. apply Go_ll. 
wp;call{2} (PS_p_ll G Go_ll). call{2} R_m_ll. wp. 
call(_:true). auto;progress.

rcondf{2} 7;progress. 
wp;call(_:true);auto. call(_:true);auto. call(_:true);auto. 
wp;call{2} (PS_p_ll G Go_ll). call{2} R_m_ll. wp. 
call(_:true).  auto;progress. 

seq 1 1 : (
   ((bb{1} = BP.bb{1} /\
    ={HRO.ERO.m,glob P, glob A,  glob Ve,  glob E, glob G, BP.secmapD, BP.setHcheck, BP.setD,
        BP.setidents, BP.setH, BP.bb0, BP.bb1, BP.bb, BP.sethappy, BP.vmap,
        BP.pk, BP.sk, BP.setchecked, BP.secmap, BP.pubmap, BP.r} /\ valid{1} = BP.valid{2}
    /\ BP.pk{2} = extractPk BP.sk{2} /\ pk0{1} = BP.pk{1}) /\ valid{1} /\
   (BP.setHcheck{2} \subset fdom BP.vmap{2}) /\ bb{1} = BP.bb{2}
 )).
call(_: ={BP.bb, BP.vmap, BP.pubmap, BP.secmap, BP.bb0, BP.bb1, glob HRO.ERO, glob G, BP.sethappy, BP.setchecked});[1..3: by sim]. 
auto;progress. 
 
if => //. 
case((BP.setHcheck{2} \subset fdom BP.vmap{2}) /\ BP.valid{2} /\ 
     (BP.setHcheck{2} \subset BP.setchecked{2}) /\ (BP.setHcheck{2} \subset BP.sethappy{2})). 
rcondt{2} 7;progress. 
wp;call(_: true);auto. call(_:true);auto. 
call{2} (A_a5_ll (<: BZK(E,P,C,Ve,A,HRO.ERO,G).O)). proc;inline*;auto. proc;auto. apply Go_ll. 
wp. 
call{2} (PS_p_ll G Go_ll). call{2} (R_m_ll). 
by wp;rnd. 

rcondf{2} 7;progress. 
wp;call(_:true);auto. call(_:true);auto. 
    wp. call{2} (PS_p_ll G Go_ll). call{2} R_m_ll.
by wp;rnd. 

    case (!(BP.setHcheck{2} \subset BP.sethappy{2})).
    rcondt{2} 1;auto.
    rcondt{1} 1;auto.

    case((BP.setHcheck{2} \subset fdom BP.vmap{2}) /\ BP.valid{2} /\ 
         (BP.setHcheck{2} \subset BP.setchecked{2}) /\ (BP.setHcheck{2} \subset BP.sethappy{2})).

    rcondt{2} 7. auto. call( _ : true ). auto. call(_: true). auto. auto. call(_: true). auto.
    rcondf{1} 2. auto. call(_: true). auto.

call{2} (A_a5_ll (<: BZK(E,P,C,Ve,A,HRO.ERO,G).O)).
    proc;inline*;auto. proc;auto. apply Go_ll.

wp. 
call{2} (PS_p_ll G Go_ll). call{2} (R_m_ll). 
auto.  call(_ : true). auto.

rcondf{2} 7. auto.
call (_ : true); auto. call(_ : true); auto.
call(_:true).  auto.



rcondf{1} 2. auto.
    call(_: true).  auto. wp.
 call{2} (PS_p_ll G Go_ll). call{2} R_m_ll. 
auto.
    sim.
simplify. 
rcondf{1} 1;progress. 
rcondf{2} 1;progress.
rcondt{1} 1;progress.  
rcondt{2} 6;progress. 
auto. call( _ : true ). auto. call(_: true). auto. auto. 

call(_: ={glob HRO.ERO, glob G, BP.bb0, BP.bb1}). sim.  sim. sim. 
wp.
call(_: ={glob G}). sim.  call{2} R_m_ll. 
by auto. 
qed. 

(**** Prove that G1L is equvalent to ZKFR with BZK as input ****)

local lemma G1_L_ZKFR_equiv &m :
  Pr[G1L(E, Ve, C, A, HRO.ERO, S).main() @ &m : res] 
  = Pr[ZKFR(E, R, S, BZK(E,P,C,Ve,A), HRO.ERO).main() @ &m : res]. 

  proof.
 
    byequiv (_: ={glob A, glob E, glob Ve, glob C, glob HRO.ERO, glob S, glob R,
    BP.setidents, BP.setD, BP.secmapD, BP.setH, BP.bb0, BP.bb1, BP.setHcheck} ==> _) => //.
  proc;inline*.  

  swap{2} 1 12;wp. 
  
  seq 18 16 : (={glob HRO.ERO, glob A, glob C, glob Ve, glob E, glob S, BP.secmapD,
               BP.setHcheck, BP.secmapD, BP.setD, BP.setidents, BP.setH, BP.bb1, BP.bb0, BP.bb,
              BP.sethappy, BP.vmap, BP.pk, BP.sk, BP.setchecked, BP.secmap, BP.pubmap}
    /\ BP.pk{2} = extractPk BP.sk{2}).

call(_: ={glob HRO.ERO, glob S, glob E, BP.pk, BP.secmapD, BP.pubmap, BP.setH, BP.secmap, BP.bb1, BP.bb0,
    BP.vmap}); [1..4:by sim].
  
  while (={i, BP.setidents, BP.setD, BP.secmap, BP.pubmap, BP.secmapD, BP.vmap});auto.
    swap{1} 13 1. 
call(_ : true).  call(E_kgen_extractpk HRO.ERO).  
while (={w, HRO.ERO.m }); auto; progress;  smt(). 
swap{1} [8..11] -7.  swap{1} 12 -5. swap{1} 5 2. 
 
seq 6 5 : (
    ={glob HRO.ERO, glob A, glob C, glob Ve, glob E, glob S, BP.secmapD, 
      BP.setHcheck, BP.setD, BP.setidents, BP.setH,
      BP.bb0, BP.bb1, BP.bb, BP.sethappy, BP.vmap, BP.pk, BP.sk, 
      BP.setchecked, BP.secmap, BP.pubmap, BP.r}
    /\ (BP.pk{2} = extractPk BP.sk{2})
    /\ pk0{1} = BP.pk{1}
).
swap{2} 5 -1. wp;rnd. 
while(={j, dbb, BP.sk, glob HRO.ERO, glob E, BP.bb}); first by sim. 
auto;progress. 

(*************   Starting Cases                                    ***********)
(*************   case(!(BP.setHcheck{2} \subset fdom BP.vmap{2})). ***********)

case(!(BP.setHcheck{2} \subset fdom BP.vmap{2})).
rcondt{2} 1;progress. 
rcondt{1} 7;progress. auto.
   while(true); auto.
    swap{1} 7 -6. 
    case((BP.setHcheck{2} \subset fdom BP.vmap{2}) /\ BP.valid{2} /\ 
    (BP.setHcheck{2} \subset BP.setchecked{2}) /\ (BP.setHcheck{2} \subset BP.sethappy{2})).
    +rcondt{2} 7.
auto. call(_: true). auto.  call(_:true);auto.

call{2} (A_a5_ll (<: BZK(E,P,C,Ve,A,HRO.ERO,S).O)).
proc. auto. call(_: true). auto. auto. proc. auto. auto. apply(So_ll).
wp. while{1} (0 <= i0{1} <= size bb{1}) (size bb{1} - i0{1}). 
progress. wp;sp. 
if => //. 
call (C_vi_ll HRO.ERO HRO.ERO_o_ll). auto;progress;smt(). auto;progress;smt(). 
    call{2}(Sp_ll). 
 call{2}(R_m_ll).
    auto.
+rcondf{2} 7;auto.
 
   call(_ : true). auto. call(_: true). auto. auto.
while{1} (0 <= i0{1} <= size bb{1}) (size bb{1} - i0{1});progress. 
wp;sp.
if => //. call(C_vi_ll HRO.ERO HRO.ERO_o_ll). auto;progress;smt().  auto;progress;smt(). 
    call{2}(Sp_ll). 
 call{2}(R_m_ll).
wp. rnd. skip;progress.  rewrite size_ge0. smt(). 
 
 
(*************   case((BP.setHcheck{2} \subset fdom BP.vmap{2})).      ***********)

+ rcondf{2} 1;  auto.
+ rcondf{1} 7 ; auto.  while(true); auto.
  
seq 6 7 : (
   (={HRO.ERO.m, glob A, glob C,  glob Ve, glob E, glob S, BP.secmapD,
       BP.setHcheck, BP.setD, BP.setidents, BP.setH, BP.bb0, BP.bb1, BP.bb,
       BP.sethappy, BP.vmap, BP.pk, BP.sk, BP.setchecked, BP.secmap,
       BP.pubmap, BP.r} /\
   BP.pk{2} = extractPk BP.sk{2} /\ pk0{1} = BP.pk{1}) /\ bb{1} = BP.bb{2} /\
  (BP.setHcheck{2} \subset fdom BP.vmap{2})
  /\ valid{1} = BP.valid{2}
).
wp. while(={i0, bb, e1, e2, HRO.ERO.m, glob C} /\ pk0{1} = pk{2}); first by sim. 
auto;progress. 
 
if => //.  
case((BP.setHcheck{2} \subset fdom BP.vmap{2}) /\ BP.valid{2} /\ 
     (BP.setHcheck{2} \subset BP.setchecked{2}) /\ (BP.setHcheck{2} \subset BP.sethappy{2})). 
rcondt{2} 7;progress. 
wp. call(_:true);auto. call(_:true);auto. call(_:true);auto. 
call{2} (A_a5_ll (<: BZK(E,P,C,Ve,A,HRO.ERO,S).O)). proc;inline*;auto. proc;auto. apply So_ll. 
wp;call{2} (Sp_ll). call{2} R_m_ll. wp. 
call(_:true). auto;progress.

rcondf{2} 7;progress. 
wp;call(_:true);auto. call(_:true);auto. call(_:true);auto. 
wp;call{2} (Sp_ll). call{2} R_m_ll. wp. 
call(_:true).  auto;progress. 

seq 1 1 : (
   ((bb{1} = BP.bb{1} /\
    ={HRO.ERO.m, glob A,  glob Ve,  glob E, glob S, BP.secmapD, BP.setHcheck, BP.setD,
        BP.setidents, BP.setH, BP.bb0, BP.bb1, BP.bb, BP.sethappy, BP.vmap,
        BP.pk, BP.sk, BP.setchecked, BP.secmap, BP.pubmap, BP.r} /\ valid{1} = BP.valid{2}
    /\ BP.pk{2} = extractPk BP.sk{2} /\ pk0{1} = BP.pk{1}) /\ valid{1} /\
   (BP.setHcheck{2} \subset fdom BP.vmap{2}) /\ bb{1} = BP.bb{2}
 )).
call(_: ={BP.bb, BP.vmap, BP.pubmap, BP.secmap, BP.bb0, BP.bb1, 
          glob HRO.ERO, glob S, BP.sethappy, BP.setchecked});[1..3: by sim]. 
auto;progress. 
 
if => //. 
case((BP.setHcheck{2} \subset fdom BP.vmap{2}) /\ BP.valid{2} /\ 
     (BP.setHcheck{2} \subset BP.setchecked{2}) /\ (BP.setHcheck{2} \subset BP.sethappy{2})). 
rcondt{2} 7;progress. 
wp;call(_: true);auto. call(_:true);auto. 
call{2} (A_a5_ll (<: BZK(E,P,C,Ve,A,HRO.ERO,S).O)). proc;inline*;auto. proc;auto. apply So_ll. 
wp. 
call{2} (Sp_ll). call{2} (R_m_ll). 
by wp;rnd. 

rcondf{2} 7;progress. 
wp;call(_:true);auto. call(_:true);auto. 
    wp. call{2} (Sp_ll). call{2} R_m_ll.
by wp;rnd. 

    case (!(BP.setHcheck{2} \subset BP.sethappy{2})).
    rcondt{2} 1;auto.
    rcondt{1} 1;auto.

    case((BP.setHcheck{2} \subset fdom BP.vmap{2}) /\ BP.valid{2} /\ 
         (BP.setHcheck{2} \subset BP.setchecked{2}) /\ (BP.setHcheck{2} \subset BP.sethappy{2})).

    rcondt{2} 7. auto. call( _ : true ). auto. call(_: true). auto. auto. call(_: true). auto.
    rcondf{1} 2. auto. call(_: true). auto.

call{2} (A_a5_ll (<: BZK(E,P,C,Ve,A,HRO.ERO,S).O)).
    proc;inline*;auto. proc;auto. apply So_ll.

wp. 
call{2} (Sp_ll). call{2} (R_m_ll). 

    auto.  call(_ : true). auto.

rcondf{2} 7. auto.
call (_ : true); auto. call(_ : true); auto.
call(_:true).  auto.



rcondf{1} 2. auto.
    call(_: true).  auto. wp.
 call{2} (Sp_ll). call{2} R_m_ll. 
auto.
    sim.
simplify. 
rcondf{1} 1;progress. 
rcondf{2} 1;progress.
rcondt{1} 1;progress.  
rcondt{2} 6;progress. 
auto. call( _ : true ). auto. call(_: true). auto. auto. 

call(_: ={glob HRO.ERO, glob S, BP.bb0, BP.bb1}). sim.  sim. sim. 
wp.
call(_: true). call{2} R_m_ll. 
by auto. 
qed. 

(*************** Bounding the difference |G0_L - G1_L| by 2*VFR + |ZKL - ZKR| ***************)

local lemma G0L_G1L_zk_vfr &m : 
  `|Pr[G0L(E,P,Ve,C,A,HRO.ERO,G).main() @ &m : res]
    - Pr[G1L(E,Ve,C,A,HRO.ERO,S).main() @ &m : res]| 
    <= 
     Pr[VFR(E, BVFR(MV(E,P,Ve,C), A), R(E), HRO.ERO, G).main() @ &m : res]
     + Pr[VFR(E, BVFR(MV(E,P,Ve,C), A), R(E), HRO.ERO, S).main() @ &m : res]
     + `|Pr[ZK_L(R(E,HRO.ERO), P, BZK(E,P,C,Ve,A,HRO.ERO), G).main() @ &m : res]
         - Pr[ZK_R(R(E,HRO.ERO), S, BZK(E,P,C,Ve,A,HRO.ERO)   ).main() @ &m : res]|.
proof. 
  rewrite (G0_L_ZKFL_equiv) (G1_L_ZKFR_equiv). 
  have H0 : forall (x y z w : real), 
               `|x - y| <= `|x - z| + `|z - w| + `|y - w| 
            by smt(@Real). 
  have H1 := H0 Pr[ZKFL(E,R,P,BZK(E,P,C,Ve,A), HRO.ERO, G).main() @ &m : res] 
             Pr[ZKFR(E,R,S,BZK(E,P,C,Ve,A),HRO.ERO    ).main() @ &m : res] 
             Pr[ZK_L(R(E,HRO.ERO),P,BZK(E,P,C,Ve,A,HRO.ERO),G).main() @ &m : res]
             Pr[ZK_R(R(E,HRO.ERO),S,BZK(E,P,C,Ve,A,HRO.ERO)  ).main() @ &m : res].  
  have H2 := (ZKFL_ZKL_VFR &m); 
  have H3 := (ZKFR_ZKR_VFR &m); 
  smt(). 
qed. 

(****************************************************************************************************)
(************************************** End of ZK part **********************************************)
(****************************************************************************************************)

(*** We now stop decrypting honestly created ciphertexts, ***)
(*** and instead pick the correct vote from vmap          ***)
local module G2L (E:Scheme, Ve:Verifier, C:ValidInd, A:OMB_BPRIV_adv, H:HOracle.Oracle, S:Simulator)  = {

  var bb   : (ident * cipher) list 

  module MV = MV(E,P,Ve,C,H,S)

  module O  = {
    proc h = H.o
    proc g = S.o

    proc vote_core(id, v, sl) = {
      var p, b, s;
      
      (p, b, s) <@ MV.vote(BP.pk, id, id, sl, v);

      return (p, b, s);
    }

    proc vote (id : ident, v0 v1 : vote) = {
      var p, b, s;

      if ((id \in BP.setH)) {
        (p, b, s) <@ vote_core(id, v0, oget BP.secmap.[id]);

        BP.vmap.[id] <- (b, s, v0) :: (odflt [] BP.vmap.[id]);

        bb <- (id, b) :: bb; 

      }
    }
  

    proc verify(id:ident) : unit = {
      var ok, sv;

      BP.setchecked <- BP.setchecked `|` (fset1 id);
      sv <- odflt [] (BP.vmap.[id]);
      ok <@ MV.verifyvote(id,(oget (ohead sv)).`2, BP.bb, id, id);
      if (ok) {
        BP.sethappy <- BP.sethappy `|` (fset1 id);
      }
    }

    proc board() : pubBB = {
      return miniPublish (bb);
    } 
  }

  module A  = A(O)

    proc main() : bool = {   
    var i, id, valid, sv;
    var dbb,j,idl,b,v, k;

    
    BP.vmap       <- empty; 
    BP.pubmap     <- empty;
    BP.secmap     <- empty;
    BP.secmapD    <- empty;
    BP.bb0        <- [];
    BP.bb1        <- [];
    BP.setchecked <- fset0;
    BP.sethappy   <- fset0;
    BP.bbstar     <- None;
    bb            <- [];
    
    H.init();
    S.init();

   (BP.pk, BP.sk) <@ MV.setup();

    (* registration *)
    i <- 0;
    while (i < card BP.setidents) {   
      id <- nth witness (elems BP.setidents) i;
      BP.secmap.[id] <- id;
      BP.pubmap.[id] <- id;
      if (id \in BP.setD) { 
        BP.secmapD.[id] <- oget BP.secmap.[id];
      }  
    i <- i + 1;
    }  

     (* adversary creates first bulletin board *)
     BP.bb <@ A.a1(BP.pk, BP.secmapD, BP.pubmap);
     valid <@ MV.validboard(BP.bb, BP.pk);
    
     (* tally *)
     dbb     <- [];
      j      <- 0;
    while (j < size BP.bb) {
     (idl, b) <- nth witness BP.bb j;
     if ( (idl, b) \in bb) {
      (* Get the vote from the vmap element which matches the ballot *)
      sv <- odflt [] BP.vmap.[idl]; (* the list for that voter *)
       k <- find (fun (x : cipher * cipher *  vote) => x.`1 = b) sv; (* The first index where b appears *)
       v <- Some (oget (onth sv k)).`3; (* the vote at that index *) 
       } else {
           v <@ E(H).dec(BP.sk, idl, b);
       }
       dbb   <- dbb ++ [(idl, v)];
        j    <- j + 1;
      }
      BP.r   <$ Rho dbb;
      BP.pk  <- extractPk BP.sk;
         
      if (!(BP.setHcheck \subset fdom BP.vmap)) { 
      BP.d <$ {0,1};
      } else { 
        if (!valid) {  
          BP.d <@ A.a2();
        } else { 
          A.a3();
          if (!BP.setHcheck \subset BP.setchecked) {
            BP.d <$ {0,1};
          } else {
          if (!(BP.setHcheck \subset BP.sethappy)){
            BP.d <@ A.a4();
          } 
          if (BP.setHcheck \subset BP.sethappy){         
            BP.pi  <@ S.prove(BP.pk, miniPublish BP.bb, BP.r);
            BP.d <@ A.a5(BP.r, BP.pi);    
          }
        }
      } 
    } 
  return BP.d; 
  }   
}.

(*****************************)
(* Intermediary lemma *)
local lemma odflt_notNone['a] (x1 x2:'a) (z: 'a option):
   z <> None => odflt x1 z = odflt x2 z.
    proof. by case: z. qed.

(* Prove that G1L and G2L are equivalent *)
local lemma G1L_G2L_equiv &m :
     BP.setidents{m} = BP.setH{m} `|` BP.setD{m}
  =>   Pr[G1L(E,Ve,C,A,HRO.ERO,S).main() @ &m : res]
     = Pr[G2L(E,Ve,C,A,HRO.ERO,S).main() @ &m : res].
proof.   
move=> H_IHD.
byequiv (_: ={glob A, glob E, glob Ve, glob C, glob S, BP.setidents, 
              BP.setD, BP.setH, BP.setHcheck}
            /\ (BP.setidents, BP.setH, BP.setD){m} 
               = (BP.setidents, BP.setH, BP.setD){2} ==> _) => //; proc.

(************************************************************************************************)
(* First we prove that everything is more or less equal before the adversary creates the board  *)
(************************************************************************************************)
seq 15 16: (   ={glob A, glob C, glob Ve, glob S, glob E, glob HRO.ERO}
            /\ ={setHcheck, secmapD, setD, setidents, setH, vmap,
                 sk, pk, bb, pubmap, sethappy, setchecked, secmap}(BP, BP)
            /\ BP.setidents{2} = BP.setH{2} `|` BP.setD{2}
            /\ BP.pk{1} = extractPk BP.sk{1}
            /\ (rem_ids BP.bb0{1} = G2L.bb{2}) 
            /\ (forall idl b,
                     (idl, b) \in G2L.bb{2}
                  =>   dec_cipher BP.sk idl b HRO.ERO.m
                     = Some (oget (onth (odflt [] BP.vmap.[idl]) 
                              (find (fun (x : _ * _ * _)  => x.`1 = b)
                                    (odflt [] BP.vmap.[idl])))).`3){2}
            /\ (forall id id', BP.pubmap.[id] = Some id' => id =id'){2}
            /\ (forall id, id \in BP.setidents => id \in BP.pubmap){2}).

+ call (:   ={glob C, glob Ve, glob S, glob E, glob HRO.ERO}
         /\ ={setHcheck, secmapD, setD, setidents, setH, vmap,
              sk, pk, pubmap, sethappy, setchecked}(BP, BP)
         /\ BP.pk{1} = extractPk BP.sk{1}
         /\ BP.setidents{2} = BP.setH{2} `|` BP.setD{2}
         /\ (rem_ids BP.bb0{1} = G2L.bb{2}) 
         /\ (forall idl b,
                  (idl, b) \in G2L.bb{2}
               =>   dec_cipher BP.sk idl b HRO.ERO.m
                  = Some (oget (onth (odflt [] BP.vmap.[idl]) 
                           (find (fun (x : _ * _ * _)  => x.`1 = b)
                                 (odflt [] BP.vmap.[idl])))).`3){2}
         /\ (forall id id', BP.pubmap.[id] = Some id' => id = id'){2}
         /\ (forall id, id \in BP.setidents => id \in BP.pubmap){2}).

  + proc; if=> //.
    inline {1} 2; wp=> //=.
    conseq (:    ={glob E}
              /\ b0{1} = b{2}
              /\ s0{1} = s{2}
              /\ s0{1} = s{2}
              /\ (dec_cipher BP.sk p0 b0 HRO.ERO.m = Some v0){1}
              /\ p0{1} = oget BP.pubmap.[id]{2})=> />.
    + move=> &1 &2 ih pubmapI setidents_sub_pubmap id_is_hon b s.
      rewrite {1}/rem_ids {1}/rem_id /=.
      have: id{2} \in BP.pubmap{2}.
      + by apply: setidents_sub_pubmap; rewrite in_fsetU id_is_hon.
      rewrite domE.
      case: {-1}(BP.pubmap.[id]{2}) (eq_refl BP.pubmap.[id]{2})=> //= id' /pubmapI <<-.
      rewrite -/(rem_ids BP.bb0{1}) //=.
      move=> dec_correct id' b'; case: ((id', b') = (id, b){2})=> />.
      + by rewrite get_set_sameE.
      rewrite negb_and; case: (id' = id{2})=> /> => neq_id.
      + rewrite get_set_sameE //=.
        move: neq_id; rewrite eq_sym=> -> /=.
        pose b0 := List.find _ _ + 1 = 0.
        by have -> /ih: !b0 by smt(find_ge0).
      by rewrite get_set_neqE=> // /ih.
    inline *; wp; sp.
    exists * BP.sk{1}, v{1}, pc{1}, (glob E){1}; elim * => sk1 v1 pc1 ge.
    wp; call{1} (Ee_eq ge).
    wp; call (:   ={glob HRO.ERO, glob E, arg, glob Ve}
               /\ arg{1} = (extractPk sk1, pc1, v1)
               /\ (glob E){1} = ge
               ==>    ={glob HRO.ERO, glob E, res}
                   /\ dec_cipher sk1 pc1 res{1} HRO.ERO.m{1} = Some v1
                   /\ (glob E){1} = ge).
    + by conseq (Eenc_dec sk1 pc1 v1) (Ee_hr ge)=> /#.
    auto=> /> &1 &2 ih pubmapI setident_sub_pubmap id_is_hon.
    have: (id \in BP.pubmap){2}.
    + by apply: setident_sub_pubmap; rewrite in_fsetU id_is_hon.
    rewrite domE.
    by case: {-1}(BP.pubmap.[id]{2}) (eq_refl BP.pubmap.[id]{2})=> //= id' /pubmapI.
  + by proc; inline *; auto.
  + by proc; auto.
  + by conseq So_ll2.
  
  while (   ={i, BP.setidents, BP.secmap, BP.pubmap, BP.secmapD, BP.setD, BP.vmap}
         /\ (forall id id', BP.pubmap{2}.[id] = Some id' => id =id')
         /\ (forall j, 0<= j < i{2} => 
                (nth witness (elems BP.setidents{2}) j) \in BP.pubmap{2})
         /\ 0 <= i{2} <= card BP.setidents{2}).
  + auto=> /> &2 pubmapI setidents_sub_pubmap_pre ge0_i _ gti_card.
    case: ((nth witness (elems BP.setidents) i \in BP.setD){2})=> //= [ith_in_setD|ith_notin_setD].
    + split=> [id0 id'|].
      + by rewrite get_setE /#.
      split=> [j0|/#].
      by rewrite mem_set /#.
    split=> [id0 id'|].
    + by rewrite get_setE /#.
    split=> [j0|/#].
    by rewrite mem_set /#.

  inline *; auto.
  call (E_kgen_extractpk HRO.ERO).
  call(: true).
  while (={w, HRO.ERO.m}); first by sim.
  auto =>/> ? ?.    
  split.
  + smt(emptyE fcard_ge0).  
  + progress.
    have His: i_R = size (elems BP.setidents{m}).
    + smt().
    have:= H2 (index id0 (elems BP.setidents{m})) _.
    + by rewrite His index_mem index_ge0 -memE H5.
    rewrite nth_index.
    + by rewrite -memE H5.
    by done. 


(************************************************************************************************)
(*** We show that everything is equivalent upto the proof produced                            ***)
(************************************************************************************************)

seq  6  6: ( ={glob A, glob C, glob Ve, glob S, glob E, glob HRO.ERO, BP.setHcheck, 
               BP.secmapD, BP.setD, BP.setidents, BP.setH, BP.vmap, BP.sk, BP.pk, 
               BP.bb, BP.sethappy, BP.setchecked, BP.r, BP.pubmap, BP.secmap, valid}
            /\ rem_ids BP.bb0{1} = G2L.bb{2}); 
  last first.
+ if=> //; first by auto. 
  if=> //; sim.
  seq 1 1: ( ={glob A, glob C, glob Ve, glob S, glob E, glob HRO.ERO, BP.setHcheck,
               BP.secmapD, BP.setD, BP.setidents, BP.setH, BP.vmap, BP.sk, BP.pk,
               BP.bb, BP.sethappy, BP.setchecked, BP.r, BP.pubmap, BP.secmap, valid} 
            /\ rem_ids BP.bb0{1} = G2L.bb{2}
            /\ (BP.setHcheck{1} \subset fdom BP.vmap{1})
            /\ valid{1}).
  + call (: ={glob HRO.ERO, glob S, BP.setchecked, BP.vmap, BP.bb, BP.pubmap, 
              BP.secmap, BP.sethappy}).
    + by proc; inline*; sim.  
    + by sim. 
    + by sim. 
    by auto.
  if =>/>; sim.
  if =>/>.
  + rcondf{1} 2; progress.
    + by call(: true).
    rcondf{2} 2; progress.
    + by call(: true).
    by sim.
  rcondt{1} 1; progress.
  rcondt{2} 1; progress.
  call(:  ={glob HRO.ERO, glob S} 
         /\ rem_ids BP.bb0{1} = G2L.bb{2}). 
  + by proc; inline*; auto. 
  + by proc; auto.
  + by conseq So_ll2.
  wp; call(: true).
  by auto.

auto.
while (   ={j, BP.bb, glob HRO.ERO, glob E, BP.sk, dbb}
       /\ (forall (idl : ident) (b : cipher),
              (idl, b) \in G2L.bb{2}  =>
                Some (oget (onth (odflt []  BP.vmap{2}.[idl])
                     (find (fun (x : _ * _ * _ )  => x.`1 = b)
                           (odflt [] BP.vmap{2}.[idl])))).`3
                = dec_cipher BP.sk{2} idl b HRO.ERO.m{2})).

            sp; if {2}; auto.
+ exists * (glob E){1}, BP.sk{1}, idl{1}, b{1};
  elim * => ee sk1 idl1 b1.
  call {1} (Edec_Odec ee sk1 idl1 b1).
  by auto=> /> &2 <- /> h _ /h ->.
exists* (glob E){1}, BP.sk{1}, idl{1}, b{1};
elim * => ee sk1 idl1 b1.
by call (Edec_Odec_eq sk1 idl1 b1); auto=> /> &2 <- />.
inline *; auto.
while (={i0, bb, e1, e2, pk, glob HRO.ERO, glob C}).
+ by sim.
by auto=> /> &1 &2 H _ _ _ _ _ id b /H <-.
qed. 
 

(********************************************************************************************************)
(************************** Here come the games starting from the right *********************************)
(********************************************************************************************************)
 

(******* We start with a game where we just unpack some procs in the security definition ********)
local module G0R' (E:Scheme, P:Prover, Ve:Verifier, C:ValidInd, A:OMB_BPRIV_adv, H:HOracle.Oracle, G:GOracle.Oracle, S:Simulator)  = {

  module O  = MB_BPRIV_oracles(MV(E, P, Ve, C), H, S, Right)
  module A  = A(O)
  module MV = MV(E,P,Ve,C,H,S)

  proc main() : bool = {
    var i, id, p, c, valid,dbb,j,idl,b,v;

    BP.vmap       <- empty; 
    BP.pubmap     <- empty;
    BP.secmap     <- empty;
    BP.secmapD    <- empty;
    BP.bb0        <- [];
    BP.bb1        <- [];
    BP.setchecked <- fset0;
    BP.sethappy   <- fset0;
    BP.bbstar     <- None;

    H.init();
    S.init();
    G.init();

(* setup: key generation *)
    (BP.pk, BP.sk) <@ MV.setup();
    
    (* registration *)
    i <- 0;
    while (i < card BP.setidents) {
      id <- nth witness (elems BP.setidents) i;
      (p,c)  <@ MV.register(id,BP.pk,BP.sk);
      BP.secmap.[id] <- c;
      BP.pubmap.[id] <- p;
      if (id \in BP.setD) {
        BP.secmapD.[id] <- oget BP.secmap.[id];
      }
      i <- i + 1;
    }

    (* bulletin board created by adversary *)
    BP.bb <@ A.a1(BP.pk, BP.secmapD, BP.pubmap); 

    (* Adversary makes a guess if everything looks fine *)
    if (!(BP.setHcheck \subset fdom BP.vmap)) {
      BP.d <$ {0,1};
    } else {
      valid <@ MV.validboard(BP.bb, BP.pk);
      if (!valid) {
        BP.d <@ A.a2();
      } else {
        A.a3(); (* overify with BP.bbstar = None and unused *)
        if (!BP.setHcheck \subset BP.setchecked) {
          BP.d <$ {0,1};
        } else {
          if (!BP.setHcheck \subset BP.sethappy) {
            BP.d <@ A.a4();
          }
          if (BP.setHcheck \subset BP.sethappy) {
            BP.bb' <@ Recover'.rec(rem_ids BP.bb0, rem_ids BP.bb1, BP.bb);
             dbb   <- [];
              j    <- 0;
            while (j < size BP.bb') {
              (idl, b) <- nth witness BP.bb' j;
                  v    <@ E(H).dec(BP.sk, idl, b);
                 dbb   <- dbb ++ [(idl, v)];
                  j    <- j + 1;
            }
            BP.r      <$ Rho dbb;
            BP.pk     <- extractPk BP.sk;
            BP.pi     <@ P(G).prove((BP.pk, miniPublish BP.bb', BP.r), (BP.sk, BP.bb'));
            BP.pi'    <@ S.prove(BP.pk, miniPublish BP.bb, BP.r);
            BP.d      <@ A.a5(BP.r, BP.pi');
          }
        }
      }
    }
    return BP.d;
  }  
}. 


(******** Lemma proving that the above game is equivalent to security definition *******)

local lemma MB_BPRIV_R_G0'_R_equiv &m (H <: HOracle.Oracle { -E, -BP, -G, -A, -C, -Ve, -S, -R, -P }) : 
  Pr[OMB_BPRIV_R(MV(E, P, Ve, C), A, H, G, S, Recover').main() @ &m : res] =
  Pr[G0R'(E, P, Ve, C, A, H, G, S).main() @ &m : res].
proof.
  byequiv =>/>; proc.
  inline*. sim.
qed.

(********* We now move the tally and the valid check outside of the if-else statements **********)
local module G0R (E:Scheme, P:Prover, Ve:Verifier, C:ValidInd, 
                  A:OMB_BPRIV_adv, H:HOracle.Oracle,S:Simulator)  = {

  module O  = MB_BPRIV_oracles(MV(E, P, Ve, C), H, S, Right)
  module A  = A(O)
  module MV = MV(E,P,Ve,C,H,S)

  proc main() : bool = {
    var i, id,  valid,dbb,j,idl,b,v;

    BP.vmap       <- empty; 
    BP.pubmap     <- empty;
    BP.secmap     <- empty;
    BP.secmapD    <- empty;
    BP.bb0        <- [];
    BP.bb1        <- [];
    BP.setchecked <- fset0;
    BP.sethappy   <- fset0;
    BP.bbstar     <- None;

    H.init();
    S.init();

    (* setup: key generation *)
    (BP.pk, BP.sk) <@ MV.setup();
    
    (* registration *)
    i <- 0;
    while (i < card BP.setidents) {
      id <- nth witness (elems BP.setidents) i;
      BP.secmap.[id] <- id;
      BP.pubmap.[id] <- id;
      if (id \in BP.setD) {
        BP.secmapD.[id] <- oget BP.secmap.[id];
      }
      i <- i + 1;
    }

    (* bulletin board created by adversary *)
    BP.bb <@ A.a1(BP.pk, BP.secmapD, BP.pubmap); 

    (* check if the board is valid *)
    valid <@ MV.validboard(BP.bb, BP.pk);

    (* recover the board and tally *)
    BP.bb' <@ Recover'.rec(rem_ids BP.bb0, rem_ids BP.bb1, BP.bb);
     dbb   <- [];
      j    <- 0;
     while (j < size BP.bb') {
       (idl, b) <- nth witness BP.bb' j;
          v     <@ E(H).dec(BP.sk, idl, b);
         dbb    <- dbb ++ [(idl, v)];
          j     <- j + 1;
     }
     BP.r      <$ Rho dbb;
     BP.pk     <- extractPk BP.sk;


    (* Adversary makes a guess if everything looks fine *)     
    if (!(BP.setHcheck \subset fdom BP.vmap)) {
      BP.d <$ {0,1};
    } else {
      if (!valid) {
        BP.d <@ A.a2();
      } else {
        A.a3(); 
        if (!BP.setHcheck \subset BP.setchecked) {
          BP.d <$ {0,1};
        } 
        else {
          if (!BP.setHcheck \subset BP.sethappy) {
            BP.d <@ A.a4();
          }
          if (BP.setHcheck \subset BP.sethappy) {
          
            BP.pi' <@ S.prove(BP.pk, miniPublish BP.bb, BP.r);
            BP.d   <@ A.a5(BP.r, BP.pi');
          }
        }
      }
    }
    return BP.d;
  }  
}. 




(**** Lemma proving that G0R' and G0R are equivalent ****)
local lemma G0R'_G0R_equiv &m : 
  Pr[G0R'(E,P,Ve,C,A,HRO.ERO,G,S).main() @ &m : res] =
  Pr[G0R(E,P,Ve,C,A,HRO.ERO,S).main() @ &m : res]. 
  proof.
  byequiv (_: ={glob A, glob C, glob Ve, glob S, glob E, glob P, 
                BP.setHcheck, BP.secmapD, BP.setD, BP.setidents, 
                BP.d, BP.setH, BP.bb'} ==> _) => //.     
proc.   
seq 16 15 : (={HRO.ERO.m, glob A, glob C, glob Ve, glob E, glob S, glob P, 
               BP.pk, BP.sk, BP.bb, BP.bb', BP.vmap, BP.setchecked, BP.setHcheck, 
               BP.sethappy, BP.d, BP.bb0, BP.bb1, BP.pubmap, BP.secmap,
               BP.setH, BP.secmap, BP.secmapD, BP.setidents}).
  inline*. 
  call(_: ={HRO.ERO.m, glob E, glob S, BP.secmap, BP.pubmap, 
            BP.pk, BP.sk, BP.setH, BP.bb0, BP.bb1, BP.vmap}).
  + sim. sim. sim. sim. 
  while(={i, BP.setidents, BP.secmap, BP.pubmap, BP.setD, BP.secmapD}). 
  + by auto. 
  wp; call(E_kgen_extractpk HRO.ERO). 
  swap{1} 14 -1. call(_:true). 
  call{1} Gi_ll. 
  while(={w, HRO.ERO.m}); first by sim.  
  by auto;progress. 



  inline*. 
(* First case: setHcheck \subset fdom BP.vmap *)
(* In other words: voters we expect will verify, do indeed vote *)
case (!(BP.setHcheck{1} \subset fdom BP.vmap{1})). 
    (* First the case where this is false *)
rcondt{1} 1;progress;rcondt{2} 20;progress. 
wp;rnd. 
while(0 <= j <= size BP.bb'); first by wp;call(_:true);auto;smt().
wp;while (0 <= i1 <= size bb2); first by auto;smt(). 
wp;while (0 <= i0 <= size bb).
sp 1; if => //. 
sp 1; if => //. 
wp;call(_:true);auto;smt().  
auto;smt(). 
if=>//;wp. call(_:true);auto;smt(). 
auto;smt().  
wp;skip;progress.
rnd. wp;rnd{2}. 
while{2} (0 <= j{2} <= size BP.bb'{2}) (size BP.bb'{2} - j{2});progress. 
wp;call(E_dec_ll HRO.ERO HRO.ERO_o_ll);auto;progress; [1..3: by smt()]. 
wp; while{2} ( 0 <= i1{2} <= size bb2{2}) (size bb2{2} - i1{2});progress.  
sp 1; if => //;sp 1;wp;skip;smt(). 
wp;while{2} (0 <= i0{2} <= size bb{2}) (size bb{2} - i0{2});progress. 
sp 1; if => //.
sp 1; if => //. 
wp;call(C_vi_ll HRO.ERO HRO.ERO_o_ll);by auto;smt(). 
auto;smt(). 
if => //;wp. call(C_vi_ll HRO.ERO HRO.ERO_o_ll);auto;smt(). 
auto;smt().
wp;skip;progress; [rewrite size_ge0 | smt() | rewrite size_ge0 | smt() | 
                   rewrite size_ge0 | smt() | smt(Rho_weight)]. 


(* Now the case where it is true *)
rcondf{1} 1;progress. 

seq 7 7 : (={HRO.ERO.m, glob A, glob C, glob Ve, glob E, glob S, glob P, 
             BP.pk, BP.sk, BP.bb, BP.vmap, BP.pubmap,
             BP.setchecked, BP.setHcheck, BP.sethappy, BP.d, BP.bb0, BP.bb1, 
             BP.setH, BP.secmap, BP.bb', valid, BP.setidents} 
             /\ BP.setHcheck{1} \subset fdom BP.vmap{1}).
wp;while (={i0, bb, e1, e2, pk, glob HRO.ERO, glob C}); [ sim | auto ].   
rcondf{2} 13;progress.    
auto. while (0 <= j <= size BP.bb'). 
wp;call(_:true);auto;progress;smt(). 
wp;while (0 <= i1 <= size bb2); first by auto;progress;smt(). 
wp;skip;progress.

(* Next case: is the BP.bb valid? *)
(* First the case where BP.bb is invalid *)
case (!valid{1}). 
rcondt{1} 1;progress;rcondt{2} 13; progress. 
auto.  
while(0 <= j <= size BP.bb'). 
wp;call(_:true);auto;progress;smt(). 
wp;while(0 <= i1 <= size bb2); first by auto;progress;smt(). 
wp;skip;progress.
call(_: true). 



wp;rnd{2};while{2} (0 <= j{2} <= size BP.bb'{2}) (size BP.bb'{2} - j{2});progress.  
wp;call(E_dec_ll HRO.ERO HRO.ERO_o_ll);auto;progress; first 3 by smt(). 
wp; while{2} (0 <= i1{2} <= size bb2{2}) (size bb2{2} - i1{2});progress. 
auto;progress;smt(). 
wp;skip;progress; [rewrite size_ge0 | smt() | rewrite size_ge0 | smt() | smt(Rho_weight)]. 




(* Then the case where BP.bb is valid *)
rcondf{1} 1;progress;rcondf{2} 13;progress. 
wp;rnd.  
while (0 <= j <= size BP.bb'); first by wp;call(_:true);auto;progress;smt().   
wp;while(0 <= i1 <= size bb2); first by auto;progress;smt(). 
wp;skip;progress.

swap {2} 13 -12.
seq 1 1: (={HRO.ERO.m, glob A, glob C, glob Ve, glob E, glob S, 
            glob P, BP.pk, BP.sk, BP.bb, BP.vmap, BP.pubmap, 
            BP.setchecked, BP.setHcheck, BP.sethappy, BP.d, BP.bb0, 
            BP.bb1, BP.setH, BP.secmap, BP.bb', valid, BP.setidents}
          /\ (BP.setHcheck{1} \subset fdom BP.vmap{1})
          /\ valid{1}). 
  + call(: ={glob HRO.ERO, glob S, BP.bb, BP.vmap, BP.secmap, BP.pubmap, BP.setchecked, BP.sethappy}). 
    + sim. sim. sim.
    by auto =>/>. 

if{1} =>/>.
+ rcondt{2} 13; auto.
  + while(true); first by auto. 
    wp; while (true); first by auto.
    by auto.
  while{2} (0 <= j{2} <= size BP.bb'{2})
           (size BP.bb'{2} - j{2})
           ; progress.
  + wp; call (E_dec_ll' HRO.ERO_o_ll); auto.
    smt().
  wp; while{2} (0<= i1{2} <= size bb2{2})
               (size bb2{2} - i1{2})
               ; progress.
  by auto; smt().
  auto=>/>; progress. 
  + by rewrite size_ge0. 
  + smt().
  + by rewrite size_ge0.
  + smt().
  + smt ( Rho_weight).

rcondf{2} 13; progress.
+ wp; rnd; while(true); first by auto. 
  wp; while (true); first by auto.
  by auto.

if{1} =>/>.
+ rcondt{2} 13; progress.
  + wp; rnd; while(true); first by auto. 
    wp; while (true); first by auto.
    by auto.
  swap{2} 13 -12.
  seq 1 1: (={HRO.ERO.m, glob A, glob C, glob Ve, glob E, glob S, 
            glob P, BP.pk, BP.sk, BP.bb, BP.vmap, BP.pubmap, 
            BP.setchecked, BP.setHcheck, BP.sethappy, BP.d, BP.bb0, 
            BP.bb1, BP.setH, BP.secmap, BP.bb', valid, BP.setidents}
          /\ (BP.setHcheck{1} \subset fdom BP.vmap{1})
          /\ valid{1}
          /\ (BP.setHcheck{1} \subset BP.setchecked{1})
          /\ ! (BP.setHcheck{1} \subset BP.sethappy{1}));
    first by call(: true).
  rcondf{1} 1; progress.
  rcondf{2} 13; progress.  
  + wp; rnd; while(true); first by auto. 
    wp; while (true); first by auto.
    by auto.
  wp; rnd{2}.
  while{2} (0 <= j{2} <= size BP.bb'{2})
           (size BP.bb'{2} - j{2})
           ; progress.
  + wp; call (E_dec_ll' HRO.ERO_o_ll); auto.
    smt().
  wp; while{2} (0<= i1{2} <= size bb2{2})
               (size bb2{2} - i1{2})
               ; progress.
  + by auto; smt().
  auto=>/>; progress. 
  + by rewrite size_ge0. 
  + smt().
  + by rewrite size_ge0.
  + smt().
  + smt(Rho_weight).

rcondt{1} 1; progress.
rcondf{2} 13; progress.
+ wp; rnd; while(true); first by auto. 
  wp; while (true); first by auto.
  by auto.
rcondt{2} 13; progress.
+ wp; rnd; while(true); first by auto. 
  wp; while (true); first by auto.
  by auto.   
sim.
by wp; call{1} (PS_p_ll G Go_ll); wp; sim. 
qed.


(*** We now stop decrypting honest ciphertexts and use plain votes from BP.vmap instead. ***)
(*** Ballots added by the adversary is decrypted as usual.                               ***)

local module G1R (E:Scheme, P:Prover, Ve:Verifier, C:ValidInd, A:OMB_BPRIV_adv, 
                  H:HOracle.Oracle,S:Simulator)  = {
 
  module MV = MV(E,P,Ve,C, H, S)
  
  module O  = {
    proc h = H.o
    proc g = S.o

    proc vote_core(id, v, sl) = {
      var p, b, s;
      
      (p, b, s) <@ MV.vote(BP.pk, id, id, sl, v);

      return (p, b, s);
    }

    proc vote (id : ident, v0 v1 : vote) = {
      var p0, b0, s0;
      var p1, b1, s1;

      if ((id \in BP.setH)) {
        (s0, b0, p0)  <@ vote_core(id, v0, oget BP.secmap.[id]); 
        (s1, b1, p1)  <@ vote_core(id, v1, oget BP.secmap.[id]);

        BP.vmap.[id] <- (b0, b1,  v0) ::  (odflt [] BP.vmap.[id]);
        BP.bb0 <- (id, id, b0) :: BP.bb0;
        BP.bb1 <- (id, id, b1) :: BP.bb1;
      }
    }
  

    proc verify(id:ident) : unit = {
      var ok, sv; 
      BP.setchecked <- BP.setchecked `|` (fset1 id);
      sv <- odflt [] (BP.vmap.[id]);
      ok <@ MV.verifyvote(id,(oget (ohead sv)).`2, BP.bb, id, id); 
      if (ok) {
        BP.sethappy <- BP.sethappy `|` (fset1 id);
      }      
    }

    proc board() : pubBB = {
      return miniPublish(rem_ids BP.bb1);
    }
  }

  module A  = A(O)

  proc main() : bool = {
    var i, id,  valid,dbb,j,idl,b,v;
    var sv,k;

    BP.vmap       <- empty; 
    BP.pubmap     <- empty;
    BP.secmap     <- empty;
    BP.secmapD    <- empty;
    BP.bb0        <- [];
    BP.bb1        <- [];
    BP.setchecked <- fset0;
    BP.sethappy   <- fset0;
    BP.bbstar     <- None;

    H.init();
    S.init();

    (* setup: key generation *)
    (BP.pk, BP.sk) <@ MV.setup();
    
    (* registration *)
    i <- 0;
    while (i < card BP.setidents) {
      id <- nth witness (elems BP.setidents) i;
      (*(p,c)  <@ MV.register(id,BP.pk,BP.sk);*)
      BP.secmap.[id] <- id;
      BP.pubmap.[id] <- id;
      if (id \in BP.setD) {
        BP.secmapD.[id] <- oget BP.secmap.[id];
      }
      i <- i + 1;
    }

    (* bulletin board created by adversary *)
    BP.bb <@ A.a1(BP.pk, BP.secmapD, BP.pubmap); 

    (* check if board is valid *)
    valid <@ MV.validboard(BP.bb, BP.pk);

    (* recover and tally *)
    BP.bb' <@ Recover'.rec(rem_ids BP.bb0, rem_ids BP.bb1, BP.bb);
     dbb   <- [];
       j   <- 0;
     while (j < size BP.bb') {
       (idl, b) <- nth witness BP.bb' j;
        if ( (idl, b) \in rem_ids BP.bb0) {
          (* Get the vote from the vmap element which matches the ballot *)
          sv <- odflt [] BP.vmap.[idl]; (* the list for that voter *)
          k  <- find (fun (x:cipher*cipher*vote) => x.`1 = b) sv;(* The first index where b appears *)
          v <- Some (oget (onth sv k)).`3; (* the vote at that index *) 
       } else {
           v <@ E(H).dec(BP.sk, idl, b);
       }
       dbb   <- dbb ++ [(idl, v)];
        j    <- j + 1;
      }
   
     BP.r      <$ Rho dbb;
     BP.pk     <- extractPk BP.sk;
         
    if (!(BP.setHcheck \subset fdom BP.vmap)) {
      BP.d <$ {0,1};
    } else {
      if (!valid) {
        BP.d <@ A.a2();
      } else {
        A.a3();
        if (!BP.setHcheck \subset BP.setchecked) {
          BP.d <$ {0,1};
        } 
        else {
          if (!BP.setHcheck \subset BP.sethappy) {
            BP.d <@ A.a4();
          }
          if (BP.setHcheck \subset BP.sethappy) {
          
            BP.pi' <@ S.prove(BP.pk, miniPublish BP.bb, BP.r);
            BP.d   <@ A.a5(BP.r, BP.pi');
          }
        }
      }
    }
    return BP.d;
  }  
}. 


local lemma odflt_is_some['a] (x1 x2:'a) (z: 'a option):
   is_some z => odflt x1 z = odflt x2 z. print odflt. 
proof.
  by case: z. 
qed.

(* Prove that G0R and G1R are equivalent *)
local lemma G0R_G1R_equiv &m : 
  BP.setidents{m} = BP.setH{m} `|` BP.setD{m} =>
  Pr[G0R(E,P,Ve,C,A,HRO.ERO,S).main() @ &m : res] 
  = Pr[G1R(E,P,Ve,C,A,HRO.ERO,S).main() @ &m : res]. 
proof.
 move => H_IHD.
 byequiv(_: ={ glob A, glob C, glob E, glob Ve, glob S,  BP.setidents, BP.setHcheck, 
               BP.setH, BP.secmapD, BP.setD, BP.d}
            /\ BP.setD{1} = BP.setD{m}
            /\ BP.setidents{1} = BP.setidents{m}
            /\ BP.setH{1} = BP.setH{m} ==> _) => //; proc.  

(************************************************************************************************)
(* First we prove that everything is more or less equal before the adversary creates the board  *)
(************************************************************************************************)
seq 15 15 : (={glob Ve,  glob C,  glob S, glob E, glob A, glob HRO.ERO, 
                BP.setHcheck, BP.secmapD, BP.setD, BP.setidents,  BP.setH,  
                BP.sk, BP.pk, BP.bb, BP.sethappy, BP.setchecked, BP.bb0, BP.bb1, 
                BP.pubmap}
             /\ fdom BP.vmap{1} = fdom BP.vmap{2}
             /\ (forall idl j, 
                   rem_fst3 (oget (onth (odflt [] BP.vmap{1}.[idl]) j)) 
                   = rem_fst3 (oget (onth (odflt [] BP.vmap{2}.[idl]) j)))
             /\ (forall idl b,  
                   (idl, b) \in rem_ids BP.bb0{2}  =>  
                       Some (oget (onth (odflt [] BP.vmap{2}.[idl]) 
                                  (find (fun (x : cipher * cipher *  vote)  => x.`1 =b)  
                                        (odflt [] BP.vmap{2}.[idl])))).`3
                        = dec_cipher BP.sk{2} idl b HRO.ERO.m{2})
            /\ (forall id id', BP.pubmap{2}.[id] = Some id' => id =id')
            /\ (forall id, id \in BP.setidents{2} => id \in BP.pubmap{2})).



call(_: ={glob Ve,  glob HRO.ERO,  glob S, glob C, glob E, BP.pk, BP.secmapD, BP.pubmap, 
           BP.sk, BP.pk, BP.secmap, BP.setH, BP.setidents, BP.bb0, BP.bb1}
         /\ fdom BP.vmap{1} = fdom BP.vmap{2}
         /\ (forall idl j, 
               rem_fst3 (oget (onth (odflt [] BP.vmap{1}.[idl]) j)) 
               = rem_fst3 (oget (onth (odflt [] BP.vmap{2}.[idl]) j)))
         /\ BP.pk{1} = extractPk BP.sk{1}
         /\ (forall idl b,  
               (idl, b) \in rem_ids BP.bb0{2}  =>  
                  Some (oget (onth (odflt [] BP.vmap{2}.[idl]) 
                            (find (fun (x : cipher * cipher *  vote)  => x.`1 =b)  
                                  (odflt [] BP.vmap{2}.[idl])))).`3
                 = dec_cipher BP.sk{2} idl b HRO.ERO.m{2}) 
         /\ (forall idl b, (idl, b) \in rem_ids BP.bb0{2} => 
                 is_some BP.vmap{2}.[idl])
         /\ (forall id id', BP.pubmap{2}.[id] = Some id' => id =id')
         /\ (forall id, id \in BP.setH{2} => id \in BP.pubmap{2})).
                   + proc.
                 if => //.
    inline*. wp; sp.
seq 1 1 : ( ={glob Ve, id, v0, v1,  HRO.ERO.m, glob S, glob C, glob E, BP.pk, BP.secmapD, 
                    BP.pubmap, BP.secmap, BP.setH,  BP.setidents,  BP.sk, BP.bb0, 
                    BP.bb1}
                 /\ fdom BP.vmap{1} = fdom BP.vmap{2}
                 /\ (forall idl j, 
                       rem_fst3 (oget (onth (odflt [] BP.vmap{1}.[idl]) j)) 
                        = rem_fst3 (oget (onth (odflt [] BP.vmap{2}.[idl]) j)))
                 /\ BP.pk{1} = extractPk BP.sk{1}
                 /\ (forall idl b,  
                       (idl, b) \in rem_ids BP.bb0{2}  =>  
                         Some (oget (onth (odflt [] BP.vmap{2}.[idl]) 
                            (find (fun (x : cipher * cipher *  vote)  => x.`1 =b)  
                                  (odflt [] BP.vmap{2}.[idl])))).`3
                         = dec_cipher BP.sk{2} idl b HRO.ERO.m{2}) 
                 /\ (forall idl b, (idl, b) \in rem_ids BP.bb0{2} => 
                         is_some BP.vmap{2}.[idl])
                 /\ (forall id id', BP.pubmap{2}.[id] = Some id' => id =id')
                 /\ (forall id, id \in BP.setH{2} => id \in BP.pubmap{2})
                 /\ BP.pk{1} = extractPk BP.sk{1}
                 /\ Some v0{1} <> None
                 /\ Some v0{1} = dec_cipher BP.sk{1} id{1} b{1} HRO.ERO.m{1}
                 /\ ={pc, id0, pk}
                 /\ id0{2} = id{2} 
                 /\ id2{2} =id{2}
                 /\ v{1} = v3{2}
                 /\ sl{2} = oget BP.secmap{2}.[id{2}] 
                 /\ pk{2} = BP.pk{2} 
                 /\ sc{2} = sl{2} 
                 /\ v3{2} = v{2}                    
                 /\ v00{1} = v0{1} 
                 /\ v10{1} = v1{1} 
                 /\ pb0{1} = oget BP.pubmap{1}.[id{1}] 
                 /\ pb1{1} = oget BP.pubmap{1}.[id{1}]
                 /\ sl0{1} = oget BP.secmap{1}.[id{1}] 
                 /\ sl1{1} = oget BP.secmap{1}.[id{1}] 
                 /\ pk{1} = BP.pk{1} 
                 /\ id1{1} = id0{1} 
                 /\ pc{1} = pb0{1} 
                 /\ sc{1} = sl0{1} 
                 /\ v{1} = v00{1} 
                 /\ b{1} = b3{2}
                           /\ id{1} \in BP.setH{2}).
                         + inline*; wp;sp.  

exists* BP.sk{1}, BP.pk{1}, v{1}, id1{1};elim* => sk1 pk1 v1 id1. 
 pose kp := (pk1 = extractPk sk1). 
      have em_kp : kp \/ !kp by smt. 
      elim em_kp.
      move => h;wp.
      call{1} (Eenc_dec sk1 id1 v1);auto;progress.
      + smt(). 

move => h.  
      conseq (_: _ ==> !(BP.pk{1} = extractPk BP.sk{1})) => //. 
      call{1} (E_enc_ll HRO.ERO HRO.ERO_o_ll);
      call{2} (E_enc_ll HRO.ERO HRO.ERO_o_ll); first skip. 
      move => &1 &2 ?; smt(). 

    wp;inline*;wp. 
    exists* (glob E){1}; elim* => ee.
    call (_ : ={ glob HRO.ERO, BP.pk, glob S}); first by sim. 
    auto =>/>;progress. 
smt(@SmtMap).

(** Proof that BP.vmap without the first element is equal on both sides **)
    + case (id{2} = idl) => [Heq|Hneq].  
+ rewrite Heq !get_set_sameE //=.  
        case(j=0) => Hj.
        + by rewrite /rem_fast4 oget_some //=.
        by exact H0. 
      rewrite !get_set_neqE 1,2:eq_sym //.
      by exact: H0.

+ (** Proof that the vote stored in vmap is a decryption of the stored ciphertext **)
      case (id{2} = idl)=> [Heq|Hneq]. 
      + rewrite get_set_eqE; first by rewrite Heq //=.
        rewrite //=.   
        case (b3{2}= b5)=> [Hbe|Hbne].  
        + by rewrite -Hbe -Heq //=.  
        rewrite //=. 
        have ->: !(find (fun (x : cipher * cipher *  vote) => x.`1 = b5)
                        (odflt [] BP.vmap{2}.[id{2}]) + 1 = 0)
            by smt(find_ge0).
                          rewrite //= (H1 id{2} b5 _).

                         + move: H7; rewrite /rem_ids map_cons Heq //=. 
          rewrite eq_sym in Hbne. 
          by rewrite Hbne //=.
           (* move => [] //=. apply: contraLR. rewrite eq_sym in Hbne. rewrite Hbne //=. *)
                          by rewrite Heq.

                       - rewrite get_set_neqE; first by rewrite eq_sym Hneq.
      move: H7; rewrite /rem_ids map_cons //=.
      rewrite eq_sym in Hneq. 
      rewrite /rem_id//= Hneq //=. 
                          by apply (H1 idl b5).
                   
      case (id{2} = idl)=> [Heq|Hneq]. 
      + rewrite get_set_eqE; first by rewrite Heq //=.
        by rewrite //=.   
      - rewrite get_set_neqE; first by rewrite eq_sym Hneq.
        move: H7; rewrite /rem_ids /rem_id map_cons //=.
        rewrite eq_sym in Hneq; rewrite Hneq //=. 
        by apply (H2 idl b5). 
                      
  (* resuming *)
  + proc;inline*;auto. progress.  
  + proc;skip;progress. 
  + by conseq So_ll2. 
                      
(* Registration procedures are equivalent *)   
while ( ={i, BP.setidents, BP.secmap, BP.pubmap, BP.secmapD, BP.setD}
       /\ (forall id id', BP.pubmap{2}.[id] = Some id' => id =id')
       /\ (forall j, 0<= j < i{2} => 
              (nth witness (elems BP.setidents{2}) j) \in BP.pubmap{2})
      /\ 0<= i{2} <= card BP.setidents{2}).
          auto=>/>; progress.


                + case (nth witness (elems BP.setidents{2}) i{2} = id0) => He. 
    + move: H5.  rewrite get_set_eqE 1: He //=.
      rewrite /Flabel /idfun //=.  
      by rewrite He //=.       
    - move: H5; rewrite get_set_neqE;
       first by rewrite eq_sym He //=. 
      by exact (H _ _). 


          + rewrite mem_set.  smt().
  + smt(). smt().
  + case (nth witness (elems BP.setidents{2}) i{2} = id0) => He. 
    + move: H5.  rewrite get_set_eqE 1: He //=.
      rewrite /Flabel /idfun //=.  
      by rewrite He //=.       
    - move: H5; rewrite get_set_neqE;
       first by rewrite eq_sym He //=. 
                by exact (H _ _).
          
          + rewrite mem_set.  smt(). 
  + smt(). smt().

(* Initializing the different sets and maps and random oracles *)
  wp;inline*;wp.
  call(E_kgen_extractpk HRO.ERO).  
  call(_: true ). 
  while ( ={w, HRO.ERO.m, glob S} ); first sim.
  auto=>/>; progress. 
  + rewrite emptyE in H0. smt().
  + smt(). 
  + by rewrite fcard_ge0.        
  + have Hm: id0 \in (elems BP.setidents{m}).
    + by rewrite -memE H_IHD in_fsetU H6. 
    have Ho:= nth_index witness id0 (elems BP.setidents{m}) Hm. 
    rewrite -Ho (H3 (index id0 (elems BP.setidents{m})) _).
    rewrite index_ge0. 
    smt(@List).
  + rewrite memE in H13.
    have Ho:= nth_index witness id0 (elems BP.setidents{m}) H13.
    rewrite -Ho (H3 (index id0 (elems BP.setidents{m})) _).
    rewrite index_ge0. 
    smt(@List).
   
            
(************************************************************************************************)
(**************** We show that everything is equivalent upto the proof produced *****************)
(************************************************************************************************)
seq 7 7 : (={ glob A, glob C, glob Ve, glob S, glob E, glob HRO.ERO, BP.setHcheck,
              BP.secmapD, BP.setD, BP.setidents, BP.setH, BP.sk, BP.pk, BP.bb, BP.bb', 
              BP.sethappy, BP.setchecked, BP.bb0, BP.bb1, BP.pubmap, valid, dbb, BP.r} 
           /\ fdom BP.vmap{1} = fdom BP.vmap{2}
           /\ (forall idl j, 
                  rem_fst3 (oget (onth (odflt [] BP.vmap{1}.[idl]) j)) 
                  = rem_fst3 (oget (onth (odflt [] BP.vmap{2}.[idl]) j)))
           /\ (forall (idl : ident) (b : cipher),  (idl, b) \in rem_ids BP.bb0{2} =>  
                   Some (oget (onth (odflt [] BP.vmap{2}.[idl]) 
                              (find (fun (x : cipher*cipher*vote)  => x.`1 =b)  
                                    (odflt [] BP.vmap{2}.[idl])))).`3
                   = dec_cipher BP.sk{2} idl b HRO.ERO.m{2})
          /\ (forall id id', BP.pubmap{2}.[id] = Some id' => id =id')
          /\ (forall id, id \in BP.setidents{2} => id \in BP.pubmap{2}) );last first. 

               
if => //;progress; [1..2: by smt()].  
by rnd;progress.
if=>// ; auto; sim.

seq 1 1 : (={ glob A, glob C, glob Ve, glob S, glob E, glob HRO.ERO, BP.setHcheck,
              BP.secmapD, BP.setD, BP.setidents, BP.setH, BP.sk, BP.pk, BP.bb, BP.bb', 
              BP.sethappy, BP.setchecked, BP.bb0, BP.bb1, BP.pubmap, valid, dbb, BP.r} 
           /\ fdom BP.vmap{1} = fdom BP.vmap{2}
           /\ (forall idl j, 
                  rem_fst3 (oget (onth (odflt [] BP.vmap{1}.[idl]) j)) 
                  = rem_fst3 (oget (onth (odflt [] BP.vmap{2}.[idl]) j)))
           /\ (forall (idl : ident) (b : cipher),  (idl, b) \in rem_ids BP.bb0{2} =>  
                   Some (oget (onth (odflt [] BP.vmap{2}.[idl]) 
                              (find (fun (x : cipher*cipher*vote)  => x.`1 =b)  
                                    (odflt [] BP.vmap{2}.[idl])))).`3
                   = dec_cipher BP.sk{2} idl b HRO.ERO.m{2})
          /\ (forall id id', BP.pubmap{2}.[id] = Some id' => id =id')
          /\ (forall id, id \in BP.setidents{2} => id \in BP.pubmap{2}) );last first. 
+ if; auto. 
  if; auto. 
 + rcondf{1} 2; progress.
    + by call(: true).
    rcondf{2} 2; progress.
    + by call(: true).
    by sim. 
  rcondt{1} 1; progress.
  rcondt{2} 1; progress.
  call(_: ={HRO.ERO.m, glob S, BP.bb1}).   
  + by proc; inline*; wp.     
  + by sim.   
  + by sim. 
  call (: ={BP.pk, BP.bb, BP.r}). 
  by auto. 

  call (: ={ glob HRO.ERO, glob S, BP.setidents, BP.setHcheck, BP.setchecked, 
               BP.sethappy, BP.bb, BP.pubmap}
          /\ fdom BP.vmap{1} = fdom BP.vmap{2}
          /\ (forall idl0 j0,
                rem_fst3 (oget (onth (odflt [] BP.vmap{1}.[idl0]) j0))
                = rem_fst3 (oget (onth (odflt [] BP.vmap{2}.[idl0]) j0)))
          /\ (forall id id', BP.pubmap{1}.[id] = Some id' => id =id')
          /\ (forall id, id \in BP.setidents{2} => id \in BP.pubmap{1})).
  + proc; inline*.
    auto=> />; progress.
    + have:= (H0 id{2} 0).
      rewrite ?/oget -?(nth_onth witness).
      rewrite ? nth0_head ?(head_ohead witness).
      rewrite /rem_fst3; move => [H2a H2b].
      smt().
    + have:= (H0 id{2} 0).
      rewrite ?/oget -?(nth_onth witness).
      rewrite ? nth0_head ?(head_ohead witness).
      rewrite /rem_fst3; move => [H2a H2b].
      smt().
  + by proc. 
  + by conseq So_ll2. 
  by auto=>/>. 
              

seq 7 7 :  (={glob A, glob C, glob Ve, glob S, glob E, glob HRO.ERO, BP.setHcheck,
              BP.secmapD, BP.setD, BP.setidents, BP.setH, BP.sk,
              BP.pk, BP.bb, BP.bb', BP.sethappy, BP.setchecked, BP.bb0, BP.bb1, 
              BP.pubmap, valid, dbb, BP.r}  /\

              fdom BP.vmap{1} = fdom BP.vmap{2} /\

              (forall (idl0 : ident) (j0 : int),
                 rem_fst3 (oget (onth (odflt [] BP.vmap{1}.[idl0]) j0)) =
                 rem_fst3 (oget (onth (odflt [] BP.vmap{2}.[idl0]) j0)))  /\

             (forall (idl : ident) (b : cipher),  (idl, b) \in rem_ids BP.bb0{2} =>  
                Some (oget (onth (odflt [] BP.vmap{2}.[idl]) 
                     (find (fun (x : cipher*cipher*vote)  => x.`1 =b)  
                     (odflt [] BP.vmap{2}.[idl])))).`3
               = dec_cipher BP.sk{2} idl b HRO.ERO.m{2}) /\

             (forall id id', BP.pubmap{2}.[id] = Some id' => id =id') /\
          
              (forall id, id \in BP.setidents{2} => id \in BP.pubmap{2})).

seq 2 2 :  (={glob A, glob C, glob Ve, glob S, glob E, glob HRO.ERO, BP.setHcheck,
              BP.secmapD, BP.setD, BP.setidents, BP.setH,  BP.sk,
              BP.pk, BP.bb, BP.bb', BP.sethappy, BP.setchecked, BP.bb0, BP.bb1,
              BP.pubmap, valid} /\

              fdom BP.vmap{1} = fdom BP.vmap{2} /\

              (forall (idl0 : ident) (j0 : int),
                rem_fst3 (oget (onth (odflt [] BP.vmap{1}.[idl0]) j0)) =
                rem_fst3 (oget (onth (odflt [] BP.vmap{2}.[idl0]) j0))) /\

              (forall (idl : ident) (b : cipher),  (idl, b) \in rem_ids BP.bb0{2} =>  
                  Some (oget (onth (odflt [] BP.vmap{2}.[idl]) 
                       (find (fun (x : cipher*cipher*vote)  => x.`1 = b)  
                       (odflt [] BP.vmap{2}.[idl])))).`3
                  = dec_cipher BP.sk{2} idl b HRO.ERO.m{2}) /\

              (forall id id', BP.pubmap{2}.[id] = Some id' => id = id') /\
             
              (forall id, id \in BP.setidents{2} => id \in BP.pubmap{2}) );inline*. 

  sp;wp. 
  while (={i1,bb0,bb1,bb2,bb'}); first by sim. 
  wp;while(={i0,e1,e2,pk,bb, glob HRO.ERO, glob C, glob A}); first by sim.  
  auto;progress.  

   seq 3 3 :  (={glob A, glob C, glob Ve, glob S,  glob E, glob HRO.ERO, BP.setHcheck,
                 BP.secmapD, BP.setD, BP.setidents, BP.setH, BP.sk,
                 BP.pk, BP.bb, BP.bb', BP.sethappy, BP.setchecked, BP.bb0, BP.bb1, 
                 BP.pubmap, valid, dbb, j} /\

                 fdom BP.vmap{1} = fdom BP.vmap{2} /\
 
                 (forall (idl0 : ident) (j0 : int),
                 rem_fst3 (oget (onth (odflt [] BP.vmap{1}.[idl0]) j0)) =
                 rem_fst3 (oget (onth (odflt [] BP.vmap{2}.[idl0]) j0))) /\

                 (forall (idl : ident) (b : cipher),  (idl, b) \in rem_ids BP.bb0{2} =>  
                      Some (oget (onth (odflt [] BP.vmap{2}.[idl]) 
                      (find (fun (x : cipher*cipher*vote)  => x.`1 = b)  
                      (odflt [] BP.vmap{2}.[idl])))).`3
                  = dec_cipher BP.sk{2} idl b HRO.ERO.m{2}) /\

                (forall id id', BP.pubmap{2}.[id] = Some id' => id = id') /\

                (forall id, id \in BP.setidents{2} => id \in BP.pubmap{2})). 

  sp;while (={j, BP.bb', glob HRO.ERO, glob E, BP.sk, dbb}
             /\ (forall (idl : ident) (b : cipher),  (idl, b) \in rem_ids BP.bb0{2} =>  
                 Some (oget (onth (odflt [] BP.vmap{2}.[idl]) 
                      (find (fun (x : cipher*cipher*vote) => x.`1 = b)  
                      (odflt [] BP.vmap{2}.[idl])))).`3
                 = dec_cipher BP.sk{2} idl b HRO.ERO.m{2})); sp;wp.

      if{2} => //; wp. 
      exists* (glob E){1}, BP.sk{1}, idl{1}, b{1};elim* => ee sk1 idl1 b1;progress.
      call{1} (Edec_Odec ee sk1 idl1 b1). 
      skip;progress. rewrite H1. apply H4.
      by move: H H0=> <- />.
      exists* (glob E){1}, BP.sk{1}, idl{1}, b{1};elim* => ee sk1 idl1 b1;progress. 
      by call (Edec_Odec_eq sk1 idl1 b1); auto=> /> &2 <-.
      skip;trivial.
      wp; rnd;trivial. auto;progress. 
qed.       


(*** Stop recovering and set BP.bb' to be BP.bb ***)
local module G2R (E:Scheme, P:Prover, Ve:Verifier, C:ValidInd, A:OMB_BPRIV_adv, 
                  H:HOracle.Oracle,S:Simulator)  = {

  module MV = MV(E,P,Ve,C, H, S)
  module O  = {
    proc h = H.o
    proc g = S.o

    proc vote_core(id, v, sl) = {
      var p, b, s;
      
      (p, b, s) <@ MV.vote(BP.pk, id, id, sl, v);

      return (p, b, s);
    }

    proc vote (id : ident, v0 v1 : vote) = {
      var p0, b0, s0;
      var p1, b1, s1;

      if ((id \in BP.setH)) {
        (s0, b0, p0)  <@ vote_core(id, v0, oget BP.secmap.[id]); 
        (s1, b1, p1)  <@ vote_core(id, v1, oget BP.secmap.[id]);

        BP.vmap.[id] <- (b1, b1,  v0) ::  (odflt [] BP.vmap.[id]);
        BP.bb0 <- (id, id, b0) :: BP.bb0;
        BP.bb1 <- (id, id, b1) :: BP.bb1;
      }
    }
  

    proc verify(id:ident) : unit = {
      var ok, sv; 
      BP.setchecked <- BP.setchecked `|` (fset1 id);
      sv <- odflt [] (BP.vmap.[id]);
      ok <@ MV.verifyvote(id,(oget (ohead sv)).`2, BP.bb, id, id); 
      if (ok) {
        BP.sethappy <- BP.sethappy `|` (fset1 id);
      }      
    }

    proc board() : pubBB = {
      return miniPublish(rem_ids BP.bb1);
    }
  }

  module A  = A(O)

  proc main() : bool = {
    var i, id,  valid,dbb,j,idl,b,v;
    var sv,k;

    BP.vmap       <- empty; 
    BP.pubmap     <- empty;
    BP.secmap     <- empty;
    BP.secmapD    <- empty;
    BP.bb0        <- [];
    BP.bb1        <- [];
    BP.setchecked <- fset0;
    BP.sethappy   <- fset0;
    BP.bbstar     <- None;

    H.init();
    S.init();

    (* setup: key generation *)
    (BP.pk, BP.sk) <@ MV.setup();
    
    (* registration *)
    i <- 0;
    while (i < card BP.setidents) {
      id <- nth witness (elems BP.setidents) i;
      BP.secmap.[id] <- id;
      BP.pubmap.[id] <- id;
      if (id \in BP.setD) {
        BP.secmapD.[id] <- oget BP.secmap.[id];
      }
      i <- i + 1;
    }

    (* bulletin board created by adversary *)
    BP.bb <@ A.a1(BP.pk, BP.secmapD, BP.pubmap); 

    (* check if board is valid *)
    valid <@ MV.validboard(BP.bb, BP.pk);

    (* tally, now without recovering *)
     dbb <- [];
      j  <- 0;
     while (j < size BP.bb) {
       (idl, b) <- nth witness BP.bb j;
         if ( (idl, b) \in rem_ids BP.bb1) {
          (* Get the vote from the vmap element which matches the ballot *)
          sv <- odflt [] BP.vmap.[idl]; (* the list for that voter *)
          k  <- find (fun (x:cipher*cipher*vote) => x.`1 = b) sv; (* The first index where b appears *)
          v  <- Some (oget (onth sv k)).`3; (* the vote at that index *) 
       } else {
           v <@ E(H).dec(BP.sk, idl, b);
       }
       dbb   <- dbb ++ [(idl, v)];
        j    <- j + 1;
     }
   
     BP.r      <$ Rho dbb;
     BP.pk     <- extractPk BP.sk;
    
    (* Adversary makes a guess if everything looks fine *)
    if (!(BP.setHcheck \subset fdom BP.vmap)) {
      BP.d <$ {0,1};
    } else {
      if (!valid) {
        BP.d <@ A.a2();
      } else {
        A.a3(); (* overify with BP.bbstar = None and unused *)
        if (!BP.setHcheck \subset BP.setchecked) {
          BP.d <$ {0,1};
        } 
        else {
          if (!BP.setHcheck \subset BP.sethappy) {
            BP.d <@ A.a4();
          }
          if (BP.setHcheck \subset BP.sethappy) {
          
            BP.pi' <@ S.prove(BP.pk, miniPublish BP.bb, BP.r);
            BP.d   <@ A.a5(BP.r, BP.pi');
          }
        }
      }
    }
    return BP.d;
  }  
}. 

(*** Proof that G1R and G2R are equivalent ***) 

local lemma G1R_G2R_equiv &m : 
  Pr[G1R(E,P,Ve,C,A,HRO.ERO,S).main() @ &m : res] 
   = Pr[G2R(E,P,Ve,C,A,HRO.ERO,S).main() @ &m : res].
proof. 
byequiv (_ : ={BP.pi', BP.vmap, glob A, glob C, glob Ve, glob S, 
               glob E, glob P,  BP.setHcheck, BP.secmapD, BP.setD,
               BP.setidents, BP.setH, BP.d}  ==> _) => //; proc. 


  (* 1/3 The first part should be exactly indentical *)
  seq 14 14 : (={BP.pi' , BP.vmap, glob A, glob S, glob C, glob E,  
                glob HRO.ERO, glob P, BP.pk, BP.sk, glob Ve, BP.setidents,
                BP.bb0, BP.bb1, BP.sethappy, BP.setchecked, BP.secmap, 
                BP.secmapD, BP.pubmap, BP.setH, BP.setHcheck}

              /\ BP.bb0{1} = BP.bb1{1} /\ BP.bb0{1} = []

              /\ (forall id, (oget (ohead (odflt [] BP.vmap{1}.[id]))).`2 = 
                 (oget (ohead (odflt [] BP.vmap{2}.[id]))).`2)

              /\ (BP.pk{1} = extractPk BP.sk{1})).

  sp;while (={i, BP.setidents, glob P, BP.secmapD, BP.secmap, 
              BP.setidents, BP.setD, BP.pubmap}); first by sim. 
  inline*;wp;call (E_kgen_extractpk HRO.ERO).
  call (_ : true); while (={w, glob HRO.ERO}); first by sim. 
  auto;progress.  


(* 2/3 As should the last *)
seq 8 7 : (={ BP.pk, BP.r, BP.pi', (*BP.vmap,*) glob A, glob S, glob C, 
              glob E, glob HRO.ERO, glob P, BP.sk, glob Ve, BP.setHcheck, 
              dbb, valid, BP.bb0, BP.bb1, BP.bb, BP.sethappy, 
              BP.setchecked, BP.setidents}

           /\ fdom BP.vmap{1} = fdom BP.vmap{2}

           /\ (forall id, (oget (ohead (odflt [] BP.vmap{1}.[id]))).`2 
                           = (oget (ohead (odflt [] BP.vmap{2}.[id]))).`2));
  last first.

  (* Beginning ifs *)
  + if =>/>; progress. 
    + by rewrite -H H1.
    + by rewrite H H1.
    + by sim.
    if =>/>.
    + by sim.
    seq 1 1: ( ={ BP.pk, BP.r, BP.pi', glob A, glob S, glob C, glob E, HRO.ERO.m, glob P,
                  BP.sk, glob Ve, BP.setHcheck, dbb, valid, BP.bb0, BP.bb1, BP.bb,
                  BP.sethappy, BP.setchecked, BP.setidents} 
               /\ fdom BP.vmap{1} = fdom BP.vmap{2} 
               /\ (forall id, (oget (ohead (odflt [] BP.vmap{1}.[id]))).`2 
                              = (oget (ohead (odflt [] BP.vmap{2}.[id]))).`2)
               /\ (BP.setHcheck{1} \subset fdom BP.vmap{1})
               /\ valid{1}).
    + call (: ={ BP.bb, BP.sethappy, BP.setchecked, glob S, HRO.ERO.m }
              /\ fdom BP.vmap{1} = fdom BP.vmap{2} 
              /\ (forall id, (oget (ohead (odflt [] BP.vmap{1}.[id]))).`2 
                              = (oget (ohead (odflt [] BP.vmap{2}.[id]))).`2)). 
      + proc. 
        inline G1R(E, P, Ve, C, A, HRO.ERO, S).MV.verifyvote
               G2R(E, P, Ve, C, A, HRO.ERO, S).MV.verifyvote. 
        auto=>/>; progress. 
        + have Hid:= (H0 id{2}).
          move: H1; rewrite -Hid; move => H1.
          smt(). 
        + have Hid:= (H0 id{2}).
          move: H1; rewrite -Hid; move => H1.
          smt(). 
      + by proc.
      + by conseq So_ll2.
      by auto=>/>.
    
    if =>/>; first by sim. 
    if =>/>; first by sim. 
    rcondt{1} 1; progress. 
    rcondt{2} 1; progress.
    by sim. 

(* end for last part of the seq 8 7, continue with first *) 

seq 1 1 : (={ BP.pi', glob A, glob S, glob C, glob E,  
              glob HRO.ERO, glob P, BP.sk, BP.pk, glob Ve, BP.setHcheck,
              BP.bb0, BP.bb1, BP.bb, BP.sethappy, BP.setchecked, BP.setH, 
              BP.secmap, BP.secmapD, BP.setidents}

            /\ fdom BP.vmap{1} = fdom BP.vmap{2}
           
            /\ (forall id, (oget (ohead (odflt [] BP.vmap{1}.[id]))).`2 = 
               (oget (ohead (odflt [] BP.vmap{2}.[id]))).`2)

            /\ (forall (idl : ident) (b : cipher), (idl, b) \in rem_ids BP.bb0{1}  =>  
                  Some (oget (onth (odflt [] BP.vmap{1}.[idl]) 
                             (find (fun (x : cipher*cipher*vote)  => x.`1 =b)  
                                   (odflt [] BP.vmap{1}.[idl])))).`3
                   = dec_cipher BP.sk{2} idl b HRO.ERO.m{2})

            /\ (forall j, (nth witness (rem_ids BP.bb0{2}) j).`1 = 
                          (nth witness (rem_ids BP.bb1{2}) j).`1)
    
            /\ size (rem_ids BP.bb0{1}) = size (rem_ids BP.bb1{1})
    
            /\ (forall idl b2, (idl, b2) \in rem_ids BP.bb1{2} =>
                   Some (oget (onth (odflt [] BP.vmap{1}.[idl]) 
                              (find  (fun (x : cipher * cipher *  vote) => x.`1 =  
                               (nth witness (rem_ids BP.bb0{2}) 
                               (index (idl, b2) (rem_ids BP.bb1{2}))).`2)
                               (odflt [] BP.vmap{1}.[idl])))).`3 
                   = Some (oget (onth (odflt [] BP.vmap{2}.[idl]) 
                                (find (fun (x : cipher * cipher *  vote) => x.`1 = b2)
                                      (odflt [] BP.vmap{2}.[idl])))).`3)).

                            
    call (_ :  ={ glob S, glob C, glob E,  glob HRO.ERO, glob P, BP.sk, 
                  BP.pk, glob Ve, BP.setHcheck, BP.bb0, BP.bb1, BP.sethappy, 
                  BP.setchecked, BP.setH, BP.secmap, BP.secmapD}

              /\ fdom BP.vmap{1} = fdom BP.vmap{2} 

              /\ size (rem_ids  BP.bb0{1}) =  size (rem_ids BP.bb1{1})

              /\ (forall id, 
                    (oget (ohead (odflt [] BP.vmap{1}.[id]))).`2 
                    = (oget (ohead (odflt [] BP.vmap{2}.[id]))).`2)

              /\ (forall (idl : ident) (b : cipher), (idl, b) \in rem_ids BP.bb0{1}  =>  
                     Some (oget (onth (odflt [] BP.vmap{1}.[idl]) 
                                 (find (fun (x : cipher*cipher*vote)  => x.`1 =b)  
                                       (odflt [] BP.vmap{1}.[idl])))).`3
                     = dec_cipher BP.sk{2} idl b HRO.ERO.m{2})

              /\ (forall j, (nth witness (rem_ids BP.bb0{2}) j).`1 
                    = (nth witness (rem_ids BP.bb1{2}) j).`1)

              /\ (forall (idl : ident) (b : cipher), 
                   (idl, b) \in rem_ids BP.bb0{1} \/ (idl, b) \in rem_ids BP.bb1{2}  =>
                       is_some BP.vmap{1}.[idl] /\ is_some BP.vmap{2}.[idl])

              /\  size (rem_ids BP.bb0{1}) = size (rem_ids BP.bb1{1})

              /\ (forall idl b2,  (idl, b2) \in rem_ids BP.bb1{2} =>
                      Some (oget (onth (odflt [] BP.vmap{1}.[idl]) 
                           (find  (fun (x : cipher * cipher *  vote) => x.`1 =
                           (nth witness (rem_ids BP.bb0{2}) (index (idl, b2) (rem_ids BP.bb1{2}))).`2)
                                        (odflt [] BP.vmap{1}.[idl])))).`3 
                      = Some (oget (onth (odflt [] BP.vmap{2}.[idl]) 
                                   (find (fun (x : cipher * cipher *  vote) => x.`1 = b2)
                                         (odflt [] BP.vmap{2}.[idl])))).`3)
              /\ BP.pk{1} = extractPk BP.sk{1}).

    + proc. 
      if => //.  
      (* We extract the core features from voting core before proceding *)
      seq 2 2 : (={ glob S, glob C, glob E, glob HRO.ERO, glob P, BP.sk, 
                    BP.pk, glob Ve, BP.setHcheck, BP.bb0, BP.bb1, BP.sethappy, 
                    BP.setchecked, id, BP.secmap, BP.secmapD, BP.setH, id, v0, v1,
                    s0,b0,p0,s1,b1,p1}

                /\ fdom BP.vmap{1} = fdom BP.vmap{2} 

                /\ size (rem_ids BP.bb0{1})  = size (rem_ids BP.bb1{1})

                /\ (forall id, (oget (ohead (odflt [] BP.vmap{1}.[id]))).`2 
                       = (oget (ohead (odflt [] BP.vmap{2}.[id]))).`2) 

                /\ (forall idl b,  (idl, b) \in rem_ids BP.bb0{1} =>
                       Some (oget  (onth (odflt [] BP.vmap{1}.[idl])   
                                   (find (fun (x : cipher * cipher *  vote) => x.`1 = b)
                                         (odflt [] BP.vmap{1}.[idl])))).`3 
                       =  dec_cipher BP.sk{2} idl b HRO.ERO.m{2}) 

                /\ (forall j, (nth witness (rem_ids BP.bb0{2}) j).`1 = 
                              (nth witness (rem_ids BP.bb1{2}) j).`1)

                /\ size (rem_ids BP.bb0{1}) = size (rem_ids BP.bb1{1})

                /\ (forall (idl : ident) (b : cipher), 
                        (idl, b) \in rem_ids BP.bb0{1} \/ (idl, b) \in rem_ids BP.bb1{2}  =>
                            is_some BP.vmap{1}.[idl] /\ is_some BP.vmap{2}.[idl])

                /\ Some v0{1} = dec_cipher BP.sk{1} id{1} b0{1} HRO.ERO.m{1} 

                /\ Some v1{1} = dec_cipher BP.sk{1} id{1} b1{1} HRO.ERO.m{1}  

                /\ (forall idl b2, (idl, b2) \in rem_ids BP.bb1{2} =>
                      Some (oget (onth (odflt [] BP.vmap{1}.[idl]) 
                                 (find  (fun (x : cipher * cipher *  vote) => x.`1 
                      =  (nth witness (rem_ids BP.bb0{2}) (index (idl, b2) 
                         (rem_ids BP.bb1{2}))).`2) (odflt [] BP.vmap{1}.[idl])))).`3 
                      =  Some (oget (onth (odflt [] BP.vmap{2}.[idl]) 
                                    (find (fun (x : cipher * cipher *  vote) => x.`1 = b2)
                                          (odflt [] BP.vmap{2}.[idl])))).`3)

                /\  BP.pk{1} = extractPk BP.sk{1}).

      (* Into the core *)
      inline*; wp; sp.
      seq 1 1 :  (={ glob S, glob C, glob E,  glob HRO.ERO, glob P, BP.sk, 
                     BP.pk, glob Ve, BP.setHcheck, BP.bb0, BP.bb1, BP.sethappy, 
                     BP.setchecked, id, BP.secmap, BP.secmapD, BP.setH, 
                     b3, id, v0, v1, id0, v, sl, pk, id2, sc, v3, pc}

                 /\ fdom BP.vmap{1} = fdom BP.vmap{2} 

                 /\ size (rem_ids BP.bb0{1}) = size (rem_ids BP.bb1{1})

                 /\ (forall id, (oget (ohead (odflt [] BP.vmap{1}.[id]))).`2
                        = (oget (ohead (odflt [] BP.vmap{2}.[id]))).`2) 

                 /\ (forall (idl : ident) (b : cipher), (idl, b) \in rem_ids BP.bb0{1} =>
                         Some (oget (onth (odflt [] BP.vmap{1}.[idl])
                                   (find (fun (x : cipher * cipher *  vote) => x.`1 = b)
                                         (odflt [] BP.vmap{1}.[idl])))).`3 =
                         dec_cipher BP.sk{2} idl b HRO.ERO.m{2})

                 /\ (forall j, (nth witness (rem_ids BP.bb0{2}) j).`1 = 
                               (nth witness (rem_ids BP.bb1{2}) j).`1) 

                 /\ size (rem_ids BP.bb0{1}) = size (rem_ids BP.bb1{1})  

                 /\ (forall (idl : ident) (b : cipher), 
                    (idl, b) \in rem_ids BP.bb0{1} \/ (idl, b) \in rem_ids BP.bb1{2}  =>
                        is_some BP.vmap{1}.[idl] /\ is_some BP.vmap{2}.[idl])

                 /\  Some v0{1} = dec_cipher BP.sk{1} id{1} b3{1} HRO.ERO.m{1}

                 /\ (forall idl b2, (idl, b2) \in rem_ids BP.bb1{2} =>
                           Some (oget (onth (odflt [] BP.vmap{1}.[idl]) 
                                 (find  (fun (x : cipher * cipher *  vote) => x.`1 = 
                                 (nth witness (rem_ids BP.bb0{2}) (index (idl, b2) 
                                 (rem_ids BP.bb1{2}))).`2)
                                 (odflt [] BP.vmap{1}.[idl])))).`3 
                            = Some (oget (onth (odflt [] BP.vmap{2}.[idl]) 
                                   (find (fun (x : cipher * cipher *  vote) => x.`1 = b2)
                                         (odflt [] BP.vmap{2}.[idl])))).`3)

                 /\  BP.pk{1} = extractPk BP.sk{1}). 



exists* BP.sk{1}, BP.pk{1}, v3{1}, id2{1};elim* => sk1 pk1 v0 id1.
      pose kp := (pk1 = extractPk sk1). 
      have em_kp : kp \/ !kp by smt(@Logic).  
      elim em_kp.
      move => h;wp. 
      call (Eenc_dec sk1 id1 v0);skip;progress. 
      move => h. 
      conseq (_: _ ==> !(BP.pk{1} = extractPk BP.sk{1})) => //.  
      call(_: ={glob HRO.ERO}); first by sim. 
      skip;progress;smt().

      (* second encryption *)
      sp; wp; progress.
      exists* BP.sk{1}, BP.pk{1}, v4{1}, pc0{1};elim* => sk1 pk1 v0 id1.
      pose kp := (pk1 = extractPk sk1). 
      have em_kp : kp \/ !kp by smt(@Logic).  
      elim em_kp.
      move => h;wp. 
      call (Eenc_dec sk1 id1 v0).
      by auto.  
      move => h. 
      conseq (_: _ ==> !(BP.pk{1} = extractPk BP.sk{1})) => //. wp. 
      call(_: ={glob HRO.ERO}); first by sim. skip;progress;smt().

                               
    (* Resuming *)
      sp;skip;progress; [1..2: by smt(@SmtMap @List)]. 
      case (id{2} = id0).
      move => a; rewrite  a !get_set_sameE; first smt(@List). 
      rewrite eq_sym=> a.
      rewrite !get_set_neqE // H1 //.
      case (id{2} = idl).  
      move => a; rewrite a get_set_sameE; simplify. 
      case (b0{2} = b); simplify. 
      move => c; rewrite -a -c;apply H6. 
      move => c; have H12 : (forall a, 0 <= a => a+ 1 <> 0) by smt().
      rewrite H12. smt(@List). simplify. 
      have H13 : (id{2}, b0{2}) :: rem_ids bb0_R = rem_ids ((id{2}, id{2}, b0{2}) :: bb0_R) by smt(@List). 
      have H14 : (idl, b) \in rem_ids bb0_R by smt().  apply H2 in H14. 
      have H15 : (idl,b) \in rem_ids bb0_R by smt(@List).
      have H16 :  (idl, b) \in rem_ids bb0_R \/ (idl, b) \in rem_ids bb1_R by smt().
      apply H5 in H16. rewrite -H14 //.
      rewrite eq_sym=> a; rewrite get_set_neqE //.
      apply H2;have H12 : (idl, b) \in rem_ids bb0_R ++ [(id{2}, b0{2})] by smt(@List). smt(). 



      have H9 : forall a b, rem_ids ((a,a,b) :: bb0_R) = (a,b) :: rem_ids bb0_R by smt(). rewrite H9.
      have H10 : forall a b, rem_ids ((a,a,b) :: bb1_R) = (a, b) :: rem_ids bb1_R by smt(). 
      rewrite H10. simplify. case (j=0); first trivial.
      move =>a; apply H3. 

      elim H9. move => a. 
      case(id{2} = idl). move => c; rewrite c. smt(@SmtMap).  move => c.
      have H9 : (idl, b) \in rem_ids bb0_R ++ [(id{2}, b0{2})] by smt(@List).
      have H10 : (idl,b) \in rem_ids bb0_R by smt(). 
      have H11 :  (idl, b) \in rem_ids bb0_R \/  (idl, b) \in rem_ids bb1_R by smt().
      apply H5 in H11; first smt(@SmtMap). 
      move => a. case(id{2} = idl). move => c;rewrite c. smt(@SmtMap). move => c.
      have H9 : (idl, b) \in rem_ids bb1_R ++ [(id{2}, b1{2})] by smt(@List).
      have H10 : (idl,b) \in rem_ids bb1_R by smt(). 
      have H11 :  (idl, b) \in rem_ids bb0_R \/  (idl, b) \in rem_ids bb1_R by smt().
      apply H5 in H11; first smt(@SmtMap).  elim H9. move => a. 
      case(id{2} = idl). move => c;rewrite c. smt(@SmtMap @List).  move => c.
      have H9 : (idl, b) \in rem_ids bb0_R ++ [(id{2}, b0{2})]. smt(@List).
      have H10 : (idl,b) \in rem_ids bb0_R by smt(). 
      have H11 :  (idl, b) \in rem_ids bb0_R \/  (idl, b) \in rem_ids bb1_R by smt().
      apply H5 in H11; first smt(@Logic @SmtMap). move => a. case(id{2} = idl). 
      move => c; rewrite c. smt(@Logic @SmtMap).  move => c.
      have H9 : (idl, b) \in rem_ids bb1_R ++ [(id{2}, b1{2})] by smt(@List).
      have H10 : (idl,b) \in rem_ids bb1_R by smt(). 
      have H11 :  (idl, b) \in rem_ids bb0_R \/  (idl, b) \in rem_ids bb1_R by smt().
      apply H5 in H11; first smt(@Logic @SmtMap). smt().

     
   case (id{2} = idl).  
   move => a; rewrite  a !get_set_sameE.
   (* ids are equal *)
   have [//|]:= eqVneq b2 (b1{2}).
    (*The right ballot is unequal *)
   move => b. have H11 : rem_ids ((id{2}, id{2}, b1{2}) :: bb1_R) = 
              (id{2},b1{2}) :: rem_ids bb1_R by smt().
   have H12 : (idl,b2) \in rem_ids bb1_R by smt(). 
   have H13 : (idl, b2) \in rem_ids bb0_R \/ (idl, b2) \in rem_ids bb1_R by smt(). 
   apply H5 in H13.
   have H16 : (find (fun (x : cipher * cipher *  vote) => x.`1 = b2)
    ((b1{2}, b0{2}, v0{2}) :: odflt [] vmap_R.[idl])) = 
    (find (fun (x : cipher *  cipher * vote) => x.`1 = b2)
    ((odflt [] vmap_R.[idl]))) + 1. by smt(). 
   rewrite H16. have H17 : (index (idl, b2) (rem_ids ((idl, idl, b1{2}) :: bb1_R))) =
  (index (idl, b2) (rem_ids bb1_R)) + 1 by smt(). rewrite H17.
   have drop_odflt: forall x (y : (cipher * cipher *  vote) list option), 
        odflt [] (Some (x :: odflt [] y)) = x :: odflt [] y.
   + move=> x y //=.
   + rewrite !drop_odflt.
    have H18 : forall (a : cipher*cipher*vote) b j, 0 <= j => 
    onth (a::b) (j+1) = onth b j. move => c d e f. smt(). 
    have H19 : forall j, 0 <= j => 
      forall (a : ident*cipher) b,  nth witness (a::b) (j+1) = 
      nth witness b j. move => c d e f. smt().
      rewrite H18.  smt(@List). 
      have H20 : rem_ids ((idl, idl, b0{2}) :: bb0_R) = 
                 (idl,b0{2}) :: rem_ids  bb0_R by smt(). rewrite H20 H19.
    rewrite index_ge0. rewrite -H8; first smt(). simplify. 
    case ( b0{2} = (nth witness (rem_ids bb0_R) (index (idl, b2) (rem_ids bb1_R))).`2).
    move => c. simplify. 
    rewrite -c. have H21 : (idl = (nth witness (rem_ids bb0_R) (index (idl, b2) 
                                  (rem_ids bb1_R))).`1) by smt(@List).
    have H22 : (idl,  b0{2}) \in rem_ids bb0_R by smt(@List). 
    have H23 : forall (a b : vote), Some a = Some b => a = b. move => a0 b3 H23.  
    rewrite (someI a0 b3); trivial. apply H23.
    rewrite H2 ; first smt(). rewrite H6; first  smt().
    move => c. have H21 : forall e, 0 <= e => e + 1 <> 0 by smt(). rewrite H21.
    smt(@List @SmtMap). trivial.   

  
   (* case - ids not equal *) 
   move => a.
      have H10 : forall a b c (d : (ident, (cipher * cipher *  vote) list) fmap), 
                 a <> b => d.[a <- c].[b] = d.[b] by smt(@SmtMap).
     rewrite H10; first smt(). rewrite H10; first smt().  
     have H11 : (idl, b2) \in rem_ids (bb1_R) ++ [(id{2}, b1{2})] by smt(@List).
     have H12 :  (idl, b2) \in rem_ids bb1_R by smt().  
     have H13 :  (nth witness (rem_ids ((id{2}, id{2}, b0{2}) :: bb0_R))
               (index (idl, b2) (rem_ids ((id{2}, id{2}, b1{2}) :: bb1_R)))) = 
               (nth witness (rem_ids (bb0_R)))
               (index (idl, b2) (rem_ids (bb1_R))) by smt (@List). rewrite H13;apply H8. trivial. 
  
      (* Now we need to show the invariant held going in *)
      proc;skip;progress. 
      proc;skip;progress. 
      conseq So_ll2;progress. auto;progress;[1..4: by smt(@SmtMap)]. 

             
  (* Validity  *)
  seq 1 1 : (={BP.pi', glob A, glob S, glob C, glob E,glob HRO.ERO, 
              glob P, BP.sk, BP.pk, glob Ve, BP.setHcheck,
              BP.bb0, BP.bb1, BP.bb, BP.sethappy, BP.setchecked, 
              BP.setH, BP.secmap, BP.secmapD, valid, BP.setidents}

             /\ fdom BP.vmap{1} = fdom BP.vmap{2}

             /\ (forall id, (oget (ohead (odflt [] BP.vmap{1}.[id]))).`2 = 
                (oget (ohead (odflt [] BP.vmap{2}.[id]))).`2)

             /\ (forall (idl : ident) (b : cipher), (idl, b) \in rem_ids BP.bb0{1}  =>  
                 Some (oget (onth (odflt [] BP.vmap{1}.[idl]) 
                      (find (fun (x : cipher*cipher*vote)  => x.`1 = b)  
                      (odflt [] BP.vmap{1}.[idl])))).`3
                 = dec_cipher BP.sk{2} idl b HRO.ERO.m{2})

             /\ (forall j, (nth witness (rem_ids BP.bb0{2}) j).`1 = 
                (nth witness (rem_ids BP.bb1{2}) j).`1)

             /\ size (rem_ids BP.bb0{1}) = size (rem_ids BP.bb1{1})

             /\ (forall (idl0 : ident) (b2 : cipher), (idl0, b2) \in rem_ids BP.bb1{2} => 
                  Some (oget (onth (odflt [] BP.vmap{1}.[idl0])  
                       (find (fun (x : cipher * cipher *  vote) =>  
                       x.`1 = (nth witness (rem_ids BP.bb0{2}) 
                              (index (idl0, b2) (rem_ids BP.bb1{2}))).`2) 
                              (odflt [] BP.vmap{1}.[idl0])))).`3 =
                  Some (oget (onth (odflt [] BP.vmap{2}.[idl0]) 
                       (find (fun (x : cipher *  cipher * vote) => x.`1 = b2)
                       (odflt [] BP.vmap{2}.[idl0])))).`3)).

  call (_ : ={glob HRO.ERO, glob C, glob A, BP.bb0}). 
  while(={pk,bb,i,e1,e2, glob HRO.ERO, glob C}); first sim.
  auto; progress. skip;progress.


     
  (* We have now shown the that boards produced                                                       *)
  (* by the adversary are the same in both games                                                      *)
  (* and that they are both valid                                                                     *)
  (* We are now going to prove some facts about recovery                                              *)
  (*   1. For a given position j, if bb{j} is not in bb1, then bb' and bb agree at that position      *)
  (*   2. bb' and bb agree on id at all positions                                                     *)
  (*   3. If in right than in left                                                                    *)
  (*   4. If in left and right then right is left                                                     *)
  (*                                                                                                  *)

  seq 3 2 : (={BP.pi', glob A, glob S, glob C, glob E, glob HRO.ERO, 
               glob P, BP.sk, glob Ve, BP.setHcheck, dbb,
               valid, BP.bb0, BP.bb1, BP.bb, BP.sethappy, BP.setchecked, 
               BP.bb, valid, dbb,  j, BP.setidents}

            /\ fdom BP.vmap{1} = fdom BP.vmap{2} 
  
            /\ size BP.bb'{1} = size BP.bb{2} 

            /\ j{1} = 0 
      
            /\ (forall id, (oget (ohead (odflt [] BP.vmap{1}.[id]))).`2 = 
               (oget (ohead (odflt [] BP.vmap{2}.[id]))).`2)

            /\ (forall (idl : ident) (b : cipher), (idl, b) \in rem_ids BP.bb0{1}  =>  
                   Some (oget (onth (odflt [] BP.vmap{1}.[idl]) 
                        (find (fun (x : cipher*cipher*vote)  => x.`1 =b)  
                        (odflt [] BP.vmap{1}.[idl])))).`3
                = dec_cipher BP.sk{2} idl b HRO.ERO.m{2})

            /\ (forall j, ! nth witness BP.bb{2} j \in rem_ids BP.bb1{1} => 
                  nth witness BP.bb'{1} j = nth witness BP.bb{2} j)

            /\ (forall j, (nth witness BP.bb'{1} j).`1 = (nth witness BP.bb{2} j).`1)

            /\ (forall j, (nth witness (rem_ids BP.bb0{1}) j).`1 = 
                          (nth witness (rem_ids BP.bb1{1}) j).`1)

            /\ size (rem_ids BP.bb0{1}) = size (rem_ids BP.bb1{1})

            /\ (forall (idl0 : ident) (b2 : cipher), (idl0, b2) \in rem_ids BP.bb1{2} => 
                  Some (oget (onth (odflt [] BP.vmap{1}.[idl0])  
                       (find (fun (x : cipher * cipher *  vote) =>  
                       x.`1 = (nth witness (rem_ids BP.bb0{2}) (index (idl0, b2) 
                              (rem_ids BP.bb1{2}))).`2) (odflt [] BP.vmap{1}.[idl0])))).`3 
                  = Some (oget (onth (odflt [] BP.vmap{2}.[idl0]) 
                         (find (fun (x : cipher *  cipher * vote) => x.`1 = b2)
                         (odflt [] BP.vmap{2}.[idl0])))).`3)

             /\ (forall j, 0 <= j < size BP.bb'{1} => 
                  (nth witness BP.bb{2} j) \in rem_ids BP.bb1{1} =>
                  (nth witness BP.bb'{1} j \in rem_ids BP.bb0{1}))

             /\ (forall j, 0<= j < size BP.bb'{1} => 
                  (nth witness BP.bb{2} j)  \in rem_ids BP.bb1{2} =>
                  (nth witness BP.bb'{1} j) = nth witness (rem_ids BP.bb0{1}) 
                                                          (index (nth witness BP.bb{2} j) 
                                                          (rem_ids BP.bb1{2})))).
  inline*.


  (* Preparing for while *)
   seq 5 0 : (={BP.pi', glob A, glob S, glob C, glob E,  glob HRO.ERO, 
                glob P, BP.sk, glob Ve, BP.setHcheck, valid, BP.bb0, BP.bb1, 
                BP.bb, BP.sethappy, BP.setchecked, BP.bb, valid, BP.setidents}

              /\ fdom BP.vmap{1} = fdom BP.vmap{2} 

              /\ bb'{1} = [] /\ bb0{1} = rem_ids BP.bb0{1} /\ bb{1} = BP.bb{1} 

              /\ bb1{1} = rem_ids BP.bb1{1} /\ i0{1} = 0

              /\ (forall id, (oget (ohead (odflt [] BP.vmap{1}.[id]))).`2 = 
                             (oget (ohead (odflt [] BP.vmap{2}.[id]))).`2)

              /\ (forall (idl : ident) (b : cipher), (idl, b) \in rem_ids BP.bb0{1} =>  
                     Some (oget (onth (odflt [] BP.vmap{1}.[idl]) 
                          (find (fun (x : cipher*cipher*vote) => x.`1 = b)  
                          (odflt [] BP.vmap{1}.[idl])))).`3
                     = dec_cipher BP.sk{2} idl b HRO.ERO.m{2})

              /\ (forall j, j < size bb'{1} =>  
                  ! nth witness BP.bb{2} j \in rem_ids BP.bb1{1} =>
                    nth witness bb'{1} j = nth witness BP.bb{2} j)

              /\ (forall j, (nth witness (rem_ids BP.bb0{1}) j).`1 = 
                            (nth witness (rem_ids BP.bb1{1}) j).`1)

              /\ size (rem_ids BP.bb0{1}) = size (rem_ids BP.bb1{1})

              /\ (forall (idl0 : ident) (b2 : cipher), (idl0, b2) \in rem_ids BP.bb1{2} => 
                  Some (oget (onth (odflt [] BP.vmap{1}.[idl0])  
                       (find (fun (x : cipher *  cipher * vote) =>  
                       x.`1 = (nth witness (rem_ids BP.bb0{2}) 
                              (index (idl0, b2) (rem_ids BP.bb1{2}))).`2) 
                              (odflt [] BP.vmap{1}.[idl0])))).`3 =
                  Some (oget (onth (odflt [] BP.vmap{2}.[idl0]) 
                       (find (fun (x : cipher *  cipher * vote) => x.`1 = b2)
                       (odflt [] BP.vmap{2}.[idl0])))).`3)

              /\ (forall j, 0 <= j < size bb'{1} => 
                   (nth witness BP.bb{2} j) \in rem_ids BP.bb1{1} =>
                   (nth witness bb'{1} j \in rem_ids BP.bb0{1}))  
              
              /\ (forall j, 0<= j < size bb'{1} => 
                    (nth witness BP.bb{2} j)  \in rem_ids BP.bb1{2} =>
                    (nth witness bb'{1} j) = nth witness (rem_ids BP.bb0{1}) 
                                                         (index (nth witness BP.bb{2} j) 
                                                         (rem_ids BP.bb1{2})))).
      sp;skip;progress; [smt(@List) | smt() | smt()].

  (* Start of dealing with while (2 goals remaining) *)
  seq 1 0 : (={BP.pi', glob A, glob S, glob C, glob E,  glob HRO.ERO, 
               glob P, BP.sk, glob Ve, BP.setHcheck, valid, BP.bb0, BP.bb1, 
               BP.bb, BP.sethappy, BP.setchecked, BP.bb, valid, BP.setidents}

             /\ fdom BP.vmap{1} = fdom BP.vmap{2} /\ (size bb'{1} = size BP.bb{1})

             /\ (forall id, (oget (ohead (odflt [] BP.vmap{1}.[id]))).`2 = 
                (oget (ohead (odflt [] BP.vmap{2}.[id]))).`2)

             /\ (forall (idl : ident) (b : cipher) (v : vote), 
                    (idl, b) \in rem_ids BP.bb0{1}  =>  
                    Some (oget (onth (odflt [] BP.vmap{1}.[idl]) 
                         (find (fun (x : cipher*cipher*vote)  => x.`1 = b)  
                         (odflt [] BP.vmap{1}.[idl])))).`3
                 = dec_cipher BP.sk{2} idl b HRO.ERO.m{2})

             /\ (forall j, j < size bb'{1} =>  
                  ! nth witness BP.bb{2} j \in rem_ids BP.bb1{1} =>
                    nth witness bb'{1} j = nth witness BP.bb{2} j)

             /\ (forall j, (nth witness bb'{1} j).`1 = (nth witness BP.bb{2} j).`1)

             /\ (forall j, (nth witness (rem_ids BP.bb0{1}) j).`1 = 
                           (nth witness (rem_ids BP.bb1{1}) j).`1)

             /\ size (rem_ids BP.bb0{1}) = size (rem_ids BP.bb1{1})

             /\ (forall (idl0 : ident) (b2 : cipher), (idl0, b2) \in rem_ids BP.bb1{2} => 
                  Some (oget (onth (odflt [] BP.vmap{1}.[idl0])  
                       (find (fun (x : cipher * cipher *  vote) =>  
                       x.`1 = (nth witness (rem_ids BP.bb0{2}) 
                              (index (idl0, b2) (rem_ids BP.bb1{2}))).`2) 
                              (odflt [] BP.vmap{1}.[idl0])))).`3 =
                   Some (oget (onth (odflt [] BP.vmap{2}.[idl0]) 
                        (find (fun (x : cipher *  cipher * vote) => x.`1 = b2)
                        (odflt [] BP.vmap{2}.[idl0])))).`3)

             /\ (forall j, 0 <= j < size bb'{1} => 
                  (nth witness BP.bb{2} j) \in rem_ids BP.bb1{1} =>
                  (nth witness bb'{1} j \in rem_ids BP.bb0{1})) 

             /\ (forall j, 0 <= j < size bb'{1} => 
                   (nth witness BP.bb{2} j)  \in rem_ids BP.bb1{2} =>
                   (nth witness bb'{1} j) = nth witness (rem_ids BP.bb0{1}) 
                                                        (index (nth witness BP.bb{2} j) 
                                                        (rem_ids BP.bb1{2})))).


 (* Beginning while (we have 2 undischarged sequences ) *) 
while {1} ( ={ BP.bb,BP.bb0,BP.bb1}
            /\ 0 <= i0{1} <= size bb{1} 
            /\ size bb'{1} = i0{1}
            /\ size (rem_ids BP.bb0{1}) = size (rem_ids BP.bb1{1})
            /\ (forall j, 
                  j < size bb'{1} => 
                  ! nth witness BP.bb{2} j \in rem_ids BP.bb1{1} =>
                        nth witness bb'{1} j = nth witness BP.bb{2} j) 
            /\ bb0{1} = rem_ids BP.bb0{1} 
            /\ bb{1} = BP.bb{1} 
            /\ bb1{1} = rem_ids BP.bb1{1} 
            /\ (forall j, 
                  (nth witness (rem_ids BP.bb0{1}) j).`1 = 
                  (nth witness (rem_ids BP.bb1{1}) j).`1) 
            /\ (forall j, 
                  j < size bb'{1} => 
                     (nth witness bb'{1} j).`1 = (nth witness BP.bb{2} j).`1) 
            /\ (forall j, 
                  0 <= j < size bb'{1} => 
                     (nth witness BP.bb{2} j) \in rem_ids BP.bb1{1} =>
                          (nth witness bb'{1} j \in rem_ids BP.bb0{1}))  
            /\ (forall j, 
                  0<= j < size bb'{1} => 
                     (nth witness BP.bb{2} j)  \in rem_ids BP.bb1{2} =>
                         (nth witness bb'{1} j)
                          = nth witness (rem_ids BP.bb0{1}) 
                              (index (nth witness BP.bb{2} j) (rem_ids BP.bb1{2})))) 
          (size bb{1} - i0{1}); first progress.
   (* inductive case (3 goals remaing *) sp 1.
   (* 5 remaining *) if => //. 
 auto=>//=; progress. 
   + smt(). + smt(). + smt(size_cat). 
   + smt(size_cat nth_cat). 
   + case (j1 < size bb'{hr}) => Hj; first by smt(nth_cat). 
     rewrite nth_cat Hj //=. 
     have ->: j1 = size bb'{hr}; first by move: H10; rewrite size_cat //=; smt().
     by rewrite //= -H //= H4 nth_index. 
   + case (j1 < size bb'{hr}) => Hj; first by smt(nth_cat). 
     rewrite nth_cat Hj //=. 
     have ->: j1 = size bb'{hr}; first by move: H11; rewrite size_cat //=; smt().
     by rewrite //= mem_nth index_ge0 H2 index_mem H9. 
   + case (j1 < size bb'{hr}) => Hj; first by smt(nth_cat). 
     rewrite nth_cat Hj //=. 
     have ->: j1 = size bb'{hr}; first by move: H11; rewrite size_cat //=; smt().
     by rewrite //= -H //= H4 nth_index. 
   + smt().



          (* second if case *)
   auto=>//=; progress.
   + smt(size_ge0). + smt(size_ge0). 
   + by rewrite cats1 size_rcons. 
   + case (j1 < size bb'{hr}) => Hj; first by smt(nth_cat). 
     rewrite nth_cat Hj //=. 
     have ->: j1 = size bb'{hr}; first by move: H10; rewrite size_cat //=; smt().
     by done. 
   + case (j1 < size bb'{hr}) => Hj; first by smt(nth_cat). 
     rewrite nth_cat Hj //=. 
     have ->: j1 = size bb'{hr}; first by move: H10; rewrite size_cat //=; smt().
     by rewrite //= -H. 
   + smt(nth_cat size_cat). 
   + smt (nth_cat size_cat). 
   + smt (). 
  (* seq 1 0 *)
  auto =>//=; progress.
  + by rewrite size_ge0. 
  + smt(nth_out).
  + smt(). + smt(). + smt(nth_out).
  
  auto=>/>; progress. 
  smt (nth_out).


wp;rnd.
          
(* We are ready to enter the while loop and prove dbb eq *)
while (={j, glob HRO.ERO, glob E, dbb, BP.sk, BP.bb0, BP.bb1, BP.sk, dbb}  
      
      /\ size BP.bb'{1} = size BP.bb{2}

      /\ (forall (idl : ident) (b : cipher) (v : vote), (idl, b) \in rem_ids BP.bb0{1} =>  
          Some (oget (onth (odflt [] BP.vmap{1}.[idl]) 
               (find (fun (x : cipher*cipher*vote)  => x.`1 = b) 
               (odflt [] BP.vmap{1}.[idl])))).`3
      = dec_cipher BP.sk{2} idl b HRO.ERO.m{2}) 

      /\ 0 <= j{1}

      /\ (forall j,  ! nth witness BP.bb{2} j \in rem_ids BP.bb1{1} => 
            nth witness BP.bb'{1} j = nth witness BP.bb{2} j)

      /\ (forall j, (nth witness BP.bb'{1} j).`1 = (nth witness BP.bb{2} j).`1)

      /\ (forall (idl0 : ident) (b2 : cipher), (idl0, b2) \in rem_ids BP.bb1{2} => 
           Some (oget (onth (odflt [] BP.vmap{1}.[idl0])  
                (find (fun (x : cipher *  cipher * vote) =>  
                x.`1 = (nth witness (rem_ids BP.bb0{2}) (index (idl0, b2) 
                       (rem_ids BP.bb1{2}))).`2) (odflt [] BP.vmap{1}.[idl0])))).`3 =
           Some (oget (onth (odflt [] BP.vmap{2}.[idl0]) 
                (find (fun (x : cipher *  cipher * vote) => x.`1 = b2)
                (odflt [] BP.vmap{2}.[idl0])))).`3)

        /\ (forall (j0 : int),
               0 <= j0 && j0 < size BP.bb'{1} =>
               nth witness BP.bb{2} j0 \in rem_ids BP.bb1{1} =>
               nth witness BP.bb'{1} j0 \in rem_ids BP.bb0{1}) 

        /\ (forall j, 0<= j < size BP.bb'{1} => 
               (nth witness BP.bb{2} j)  \in rem_ids BP.bb1{2} =>
                  (nth witness BP.bb'{1} j)
                   = nth witness (rem_ids BP.bb0{1}) 
                            (index (nth witness BP.bb{2} j) (rem_ids BP.bb1{2})))).
  progress;wp;sp.

  if {1}; last first. 
  + if {2}; last first.
    + (* The case where the ballots didn't come form the voting oracle *)
      call (_ : ={glob HRO.ERO}); first by proc. 
                        auto=>//=; progress.

                        
      + by have:= H5 j{2}; rewrite -H -H0 //=.
      + by rewrite H in H12; have:= H4 j{2} H12; rewrite -H -H0 //=. 
      + smt(). + smt(). + smt(). 
    - (* case where it was in the right but not the left *)
      exists* (glob E){1}, BP.sk{1}, idl{1}, b{1}; 
         elim* => ee sk1 idl1 b1;progress.
     call{1} (Edec_Odec ee sk1 idl1 b1). 
     auto=>//=; progress. 
     + have := H7 j{2} _ _.
       + by rewrite H3 H9. 
       + by rewrite -H H12. 
       by rewrite -H0 H11. 
     + have := H7 j{2} _ _.
       + by rewrite H3 H9. 
       + by rewrite -H H12. 
       by rewrite -H0 H11. 
     + smt(). + smt(). smt().


  - if{2} =>//=. 
    + (* same code on both sides *)
      auto=>/>; progress. 
      + have:= H5 j{2}; rewrite -H -H0 //=.
        move => Heq; rewrite Heq.
        have := (H6 idl{2} b{2} H12). 
        have ->: (nth witness (rem_ids BP.bb0{2})
               (index (idl{2}, b{2}) (rem_ids BP.bb1{2}))).`2 = b{1};
         first by smt(). 
        smt (). 
      + have:= H5 j{2}; rewrite -H -H0 //=.
        move => Heq; rewrite Heq.
        have := (H6 idl{2} b{2} H12). 
        have ->: (nth witness (rem_ids BP.bb0{2})
               (index (idl{2}, b{2}) (rem_ids BP.bb1{2}))).`2 = b{1};
         first by smt(). 
        smt (). 
      + smt(). + smt(). + smt().

    - (* vmap on left and dec on right side *)
      exists* (glob E){1}, BP.sk{1}, idl{1}, b{2};
        elim* => ee sk1 idl1 b1;progress.
      call{2} (Edec_Odec ee sk1 idl1 b1).
      auto=>/>; progress. 
      + by have:= H5 j{2}; rewrite -H -H0 //=.
      + rewrite H in H12; have:= H4 j{2} H12; rewrite -H -H0 //=. 
        rewrite (H2 idl{2} b{1} H11). 
        by done. 
      + rewrite H in H12; have:= H4 j{2} H12; rewrite -H -H0 //=.   
        rewrite (H2 idl{2} b{1} H11).
        by done.
      + smt(). + smt(). + smt().
(* end while loop *)
auto=>/>; progress. 
+ smt(). + smt().
qed.


(****************************************************************************************************)
(** Modify G2R to a game where we use a single board rather than BP.bb0 and BP.bb1 similar to G2L. **)
(** We add b1 to the board, but we pick v0 from vmap and use this in the tally.                    **)
(****************************************************************************************************)


local module G3R (E:Scheme, P:Prover, Ve:Verifier, C:ValidInd, 
                  A:OMB_BPRIV_adv, H:HOracle.Oracle,S:Simulator)  = {
  var bb : (ident * cipher) list
  module MV = MV(E,P,Ve,C, H, S)
  module O  = {
    proc h = H.o
    proc g = S.o

    proc vote_core(id, v, sl) = {
      var p, b, s;
      
      (p, b, s) <@ MV.vote(BP.pk, id, id, sl, v);

      return (p, b, s);
    }

    proc vote (id : ident, v0 v1 : vote) = {
      var p1, b1, s1;

      if ((id \in BP.setH)) {
        (s1, b1, p1)  <@ vote_core(id, v1, oget BP.secmap.[id]);
        BP.vmap.[id] <- (b1, b1,  v0) ::  (odflt [] BP.vmap.[id]);
        bb <- (id, b1) :: bb;
      }
    }
  

    proc verify(id:ident) : unit = {
      var ok, sv; 
      BP.setchecked <- BP.setchecked `|` (fset1 id);
      sv <- odflt [] (BP.vmap.[id]);
      ok <@ MV.verifyvote(id,(oget (ohead sv)).`2, BP.bb, id, id); 
      if (ok) {
        BP.sethappy <- BP.sethappy `|` (fset1 id);
      }
      
    }

    proc board() : pubBB = {
      return miniPublish (bb);
    }
  }


  module A  = A(O)

  proc main() : bool = {
    var i, id,  valid,dbb,j,idl,b,v;
    var sv,k;

    BP.vmap       <- empty; 
    BP.pubmap     <- empty;
    BP.secmap     <- empty;
    BP.secmapD    <- empty;
    BP.bb0        <- [];
    BP.bb1        <- [];
    BP.setchecked <- fset0;
    BP.sethappy   <- fset0;
    BP.bbstar     <- None;

    bb <- [];

    H.init();
    S.init();

    (* setup: key generation *)
    (BP.pk, BP.sk) <@ MV.setup();
    
    (* registration *)
    i <- 0;
    while (i < card BP.setidents) {
      id <- nth witness (elems BP.setidents) i;
      BP.secmap.[id] <- id;
      BP.pubmap.[id] <- id;
      if (id \in BP.setD) {
        BP.secmapD.[id] <- oget BP.secmap.[id];
      }
      i <- i + 1;
    }

    (* bulletin board created by adversary *)
    BP.bb <@ A.a1(BP.pk, BP.secmapD, BP.pubmap); 
    
    (* check if the board is valid *)
    valid <@ MV.validboard(BP.bb, BP.pk);
     dbb  <- [];
       j  <- 0;
     while (j < size BP.bb) {
       (idl, b) <- nth witness BP.bb j;
       if ( (idl, b) \in bb) {
          (* Get the vote from the vmap element which matches the ballot *)
          sv <- odflt [] BP.vmap.[idl]; (* the list for that voter *)
          k <- find (fun (x:cipher*cipher*vote) => x.`1 = b) sv; (* The first index where b appears *)
          v <- Some (oget (onth sv k)).`3; (* the vote at that index *) 
       } else {
           v <@ E(H).dec(BP.sk, idl, b);
       }
       dbb   <- dbb ++ [(idl, v)];
        j    <- j + 1;
     }
   
    BP.r      <$ Rho dbb;
         
    if (!(BP.setHcheck \subset fdom BP.vmap)) {
      BP.d <$ {0,1};
    } else {
      if (!valid) {
        BP.d <@ A.a2();
      } else {
        A.a3(); 
        if (!BP.setHcheck \subset BP.setchecked) {
          BP.d <$ {0,1};
        } 
        else {
          if (!BP.setHcheck \subset BP.sethappy) {
            BP.d <@ A.a4();
          }
          if (BP.setHcheck \subset BP.sethappy) {
          
            BP.pi'        <@ S.prove(BP.pk, miniPublish BP.bb, BP.r);
            BP.d <@ A.a5(BP.r, BP.pi');
          }
        }
      }
    }
    return BP.d;
  }  
}. 

local lemma G2R_G3R_equiv &m :
  Pr[G2R(E,P,Ve,C,A,HRO.ERO,S).main() @ &m : res] 
  = Pr[G3R(E,P,Ve,C,A,HRO.ERO,S).main() @ &m : res]. 
proof. 
byequiv (_: ={ BP.bb1, BP.pi',glob A, glob C, glob Ve, glob S, glob E, 
               BP.setHcheck, BP.secmapD, BP.setD, BP.setidents, BP.setH, BP.bbstar} ==> _) => //. 
proc. swap{2} 6 -2. 


(**** Everything up until the adversary creates BP.bb should be equivalent ****)
seq 14 15 : (={ BP.pi', BP.bb1, glob A, glob HRO.ERO, glob C, glob Ve, 
                glob S, glob E, BP.setHcheck, BP.secmapD, BP.setD, 
                BP.setidents, BP.setH,BP.bbstar, BP.pk, BP.sk, BP.vmap, 
                BP.pubmap, BP.secmap, BP.setchecked, BP.sethappy}
  /\ (rem_ids BP.bb1{1} = G3R.bb{2}) /\ (BP.pk{1} = extractPk BP.sk{1})
).

  while (={i, BP.setidents, BP.secmap, BP.pubmap, BP.setD, BP.secmapD}); first by sim. 
  wp. 
  inline*. 
  wp; call (E_kgen_extractpk HRO.ERO); call(_:true).  
  while (={w, HRO.ERO.m}); first by sim.
  by auto;progress. 


(**** We now do the if sentences, which should be more or less equal on the two sides ****)
seq 7 6 :(={ BP.pi', BP.setHcheck, valid, BP.vmap, BP.bbstar, BP.r, BP.pk, BP.sk, BP.setchecked, 
             BP.sethappy, BP.bb, BP.bbstar, glob HRO.ERO, glob C, glob S, glob Ve, glob E, glob A, 
             BP.setidents} 
          /\ rem_ids BP.bb1{1} = G3R.bb{2}); last first.
+ if => //; first by rnd. 
  if => //. 
  + by call(_: true); skip; progress. 

seq 1 1 : (
  ((={BP.setHcheck, valid, BP.vmap, BP.bbstar, BP.r, BP.pk, BP.sk, BP.pi',  
      BP.setchecked, BP.sethappy, BP.bb, glob HRO.ERO, glob C,
        glob S, glob Ve, glob E, glob A, BP.setidents} /\
    rem_ids BP.bb1{1} = G3R.bb{2} /\
    ! ! (BP.setHcheck{1} \subset fdom BP.vmap{1})) /\
   ! !valid{1})
).

call(_: ={glob HRO.ERO, glob S, BP.setchecked, BP.setidents, BP.sethappy, BP.vmap, BP.bb}). 
  proc;inline*;auto. progress. sim. sim. auto;progress. 


if => //. rnd;skip;progress.
if => //. 


seq 1 1 : (
  ((={BP.setHcheck, valid, BP.vmap, BP.bbstar, BP.r, BP.pk, 
      BP.sk, BP.pi', BP.d,  BP.setchecked, BP.sethappy, BP.bb, glob HRO.ERO, glob C,
        glob S, glob Ve, glob E, glob A, BP.setidents} /\
    rem_ids BP.bb1{1} = G3R.bb{2} /\
    ! ! (BP.setHcheck{1} \subset fdom BP.vmap{1})) /\
   ! !valid{1})
); first by call(_: true).  
if => //.

auto.
wp.

 call(_: ={glob S,HRO.ERO.m}
         /\ rem_ids BP.bb1{1} = G3R.bb{2}).  
 + by proc. 
 + by proc. 
 + by conseq So_ll2.
call(: ={BP.pk, BP.bb, BP.r}). 
by auto. 
 
if => //. 
 call(_: ={glob S,HRO.ERO.m}
         /\ rem_ids BP.bb1{1} = G3R.bb{2}).  
 + by proc. 
 + by proc. 
 + by conseq So_ll2.
 by call(_:true).    
(**** end of if sentences ****)

    wp;rnd.


(**** While loop for tally, should be ok as longs as bb1{1} match bb{2} ****)
while ( ={ j, BP.bb, glob E, glob HRO.ERO, BP.sk, dbb, BP.vmap} 
        /\ rem_ids BP.bb1{1} = G3R.bb{2}). 
  wp;sp.  
  if => //=. 
  + progress;smt(). 
  + auto=>/>;progress. 
    + rewrite -H in H0. 
      move: H0; move => [#] Hi Hb.
      by rewrite Hi Hb.
  call(_: ={glob HRO.ERO}); first by sim. 
  auto=>/>; progress;
  [1..2: by rewrite -H in H0; move: H0; move => [#] Hi Hb]. 
inline*.



  
(* Validity check for BP.bb *)
wp.  
while ( ={i0, bb, e1, e2, glob C, pk, HRO.ERO.m});first by sim.  
wp.
call(: ={glob E, glob HRO.ERO, glob S, BP.setidents, BP.setH, BP.pk, BP.sk, BP.secmap, BP.vmap} 
       /\ (rem_ids BP.bb1{1} = G3R.bb{2})
       /\ (BP.pk{1} = extractPk BP.sk{1})).

  (*** Vote oracle ***)
  + proc. 
    if => //.  
    inline*; wp. 
    seq 9 0 : ( ={id, v0, v1, glob E, glob HRO.ERO, glob S, BP.setidents, BP.setH, BP.pk, 
                  BP.sk, BP.secmap, BP.vmap}
                /\ (rem_ids BP.bb1{1} = G3R.bb{2}) 
                /\ (BP.pk{1} = extractPk BP.sk{1}) 
                /\ (id{1} \in BP.setH{1})
                /\ id0{1} = id{1} /\ v3{1} = v0{1} /\ id2{1} = id{1} ).
    + exists* (glob E){1}; elim* => ge. 
      by call{1} (Ee_eq ge);auto;progress.
    sp.

    exists* BP.sk{1}, pk0{1}, id3{1}, v4{1}. 
      elim* => sk pk id v.  
    pose kp := pk = extractPk sk. 
    have em_kp : kp \/ !kp by exact/orbN. 
    elim em_kp. 
    + move => h. 
      call{1} (Eenc_dec sk id v). 
      by auto;progress. (*skip.*) 
    - move => h. 
      call{1} (E_enc_ll HRO.ERO HRO.ERO_o_ll); 
        call{2} (E_enc_ll HRO.ERO HRO.ERO_o_ll). 
      by auto;progress;smt(). 

  + by proc. 
  + by proc.
  + by conseq So_ll2. 

by auto=>/>.
qed.  

  (** Proof that the left side IND1CCA experiment using BCCA as adversary is equivalent to G2L **)

local lemma G2L_CCA_left_equiv &m : 
    Pr[G2L(E,Ve,C,A,HRO.ERO,S).main() @ &m : res] = 
    Pr[Ind1CCA(E,BCCA(MV(E,P,Ve,C), A, S), HRO.ERO, Left).main() @ &m : res].
proof. 
byequiv(_: ={BP.pi, glob A, glob C, glob E, glob Ve, glob S, glob G, 
             BP.setidents, BP.setHcheck, BP.setH, BP.secmapD, BP.setD}  ==> _) => //. 
proc. 
inline Ind1CCA(E, BCCA(MV(E,P,Ve,C), A,S),HRO.ERO,Left).A.main.
swap{2} [6..11] -5. swap{2} 12 -2. swap{2} [9..10] -2. 
  swap{2} 13 -2. swap{2} [8..10] -1.



(** Up to the point where adversary creates BP.bb, everything is more or less equivalent **)
seq 15 17 : (
    ={BP.pi, BP.bbstar, glob HRO.ERO, glob S, glob C, glob E, glob Ve, 
      glob A, glob G, BP.pk, BP.setidents, BP.setHcheck, BP.setH, BP.secmapD, 
      BP.setD, BP.sethappy, BP.setchecked, BP.vmap, BP.pubmap}
    /\ (G2L.bb{1} = BP.bb'{2})
    /\ (BP.sk{1} = BS.sk{2})
    /\ (BP.pk{2} = BS.pk{2})
    /\ (size BP.bb'{2} = size BS.encL{2})
    /\ (!BS.decQueried{2})
    /\ (forall (id : ident) (b : cipher), (id, b) \in BP.bb'{2} <=> (b, id) \in BS.encL{2})
    /\ (BP.pk{1} = extractPk BP.sk{1})
). 

inline*.
 while ( ={BP.pi, i, BP.setidents, BP.secmap, BP.secmapD, BP.setD, 
          BP.setidents, BP.pubmap} ); first by sim; wp.  
swap{2} 16 -2. wp.  call (E_kgen_extractpk HRO.ERO). call(_:true).  
wp; while (={w, HRO.ERO.m}); first by sim. 
auto; progress.    

(** The if sentences at the end should also be equivalent **)
seq 7 7 : (
    ={BP.setchecked, BP.pi, BP.bbstar, glob HRO.ERO, glob A, glob S, glob G, 
      glob Ve, valid, BP.setidents, BP.setHcheck, BP.vmap, BP.r,  BP.bb, 
      BP.setchecked, BP.sethappy, BP.pk}
    /\ (G2L.bb{1} = BP.bb'{2})
    /\ (BP.sk{1} = BS.sk{2})
); last first. 
wp. 
if => //; first by rnd. 
if => //. call(_: true); progress. 


seq 1 1 : ((={glob HRO.ERO,  glob A, glob S, glob G, glob Ve, valid,  BP.setHcheck, BP.bbstar, BP.pk,
       BP.vmap, BP.r, BP.pi, BP.bb, BP.setchecked, BP.sethappy, BP.setidents} /\
   ! ! (BP.setHcheck{1} \subset fdom BP.vmap{1})) /\
  ! !valid{1}
  /\ (G2L.bb{1} = BP.bb'{2})
).
inline*. 
    wp.
    call(_: ={BP.bb,BP.vmap, glob S, HRO.ERO.m, BP.bbstar,  BP.setchecked, BP.sethappy}). 
progress.
    proc.
sim. 
progress.


progress. sim. sim.
progress.

if => //.  auto.
if => //.

seq 1 1 : ((={BP.d, glob HRO.ERO,  glob A, glob S, glob G, glob Ve, valid,  
              BP.setHcheck, BP.bbstar, BP.pk, BP.vmap, BP.r, BP.pi, BP.bb, 
              BP.setchecked, BP.sethappy, BP.setidents} /\
   ! ! (BP.setHcheck{1} \subset fdom BP.vmap{1})) /\
  ! !valid{1}
  /\ (G2L.bb{1} = BP.bb'{2})
).

call(_: ={glob S}).  skip. progress.
if => //.
call(_: ={HRO.ERO.m, glob S} /\ G2L.bb{1} = BP.bb'{2}).  
sim. progress. sim. sim.

    call(_: true).   progress.

if => // .
call(_: ={glob S, HRO.ERO.m, BP.bbstar,  BP.setchecked, BP.sethappy}/\ (G2L.bb{1} = BP.bb'{2})). 
    sim. sim. sim.

    call(_: true). progress.

wp;rnd. 
inline*. 
(** tally while loop **)
while ( ={j, BP.bb, dbb, BP.vmap, glob HRO.ERO} /\ (0 <= j{2})
     /\ (BP.sk{1} = BS.sk{2})
     /\ (BP.pk{1} = BS.pk{2})
     /\ (G2L.bb{1} = BP.bb'{2})
     /\ (mL{2} = map (fun (ci : cipher * ident) => 
                 if !( (ci.`2, ci.`1) \in BP.bb'{2} ) 
                then dec_cipher BS.sk{2} ci.`2 ci.`1 HRO.ERO.m{2}
                else None) (flip BP.bb{2}))). 

wp;sp. 
  if{1} =>//=. 
  + auto=>/>; progress.
    + do 3! congr.
      + smt().
      do 4! congr.
      + smt().
      by move: H; case: ((nth witness BP.bb j){2})=> /#.
    + smt().
    + smt().
    smt(). 
  exists* (glob E){1}, BP.sk{1}, idl{1}, b{1};
    elim* => ge sk idl b. 
  call{1} (Edec_Odec ge sk idl b). 
  auto=>/>; progress.
  + smt(). smt(). 
  + rewrite -H //=. 
    do 3! congr. 
    rewrite /flip. rewrite -map_comp /(\o) //=. 
    smt (nth_map). 
  + smt(). 



swap{2} [14..15] -5. 
rcondt{2} 14;progress. 
wp;while (0 <= i0 <= size bb). wp;sp. 
if => //. 
call(_:true); first by auto. 
auto;progress;smt(). 
auto;progress;smt(). 
wp. 
call(_:true);auto. 
progress;rewrite size_ge0. 
wp. 

while{2} (0 <= i1{2} <= size cL{2} 
         /\ mL0{2} = map (fun (ci : cipher * ident) =>
            if !(ci \in BS.encL{2})
            then dec_cipher BS.sk{2} ci.`2 ci.`1 HRO.ERO.m{2} 
            else None) (take i1{2} cL{2})) 
(size cL{2} - i1{2}); progress. 
  wp;sp. 
  exists* (glob E), c0, l, BS.sk{hr}; elim* => ge c l sk.  
  call{1} (Edec_Odec ge sk l c).  
  auto =>/>;progress. 
  + smt(). smt(). 
  + rewrite (take_nth witness); first by rewrite H0 H2. 
    by rewrite map_rcons //= -H H3 //= cats1. 
  + smt(). smt(). smt().  
  + rewrite (take_nth witness); first by rewrite H0 H2. 
    by rewrite map_rcons //= -H H3 //= cats1. 
  + smt().

(* valid check *)
wp; while (={i0, bb, e1, e2, glob HRO.ERO, glob C} /\ pk{1} = pk0{2}); first sim. 
wp.  

(* A.a1 call *)
call(_: ={ BP.pi, BP.bbstar, glob C, glob E, glob HRO.ERO, glob S, BP.pk, BP.setH, BP.vmap} 
        /\ (!BS.decQueried{2})
        /\ (G2L.bb{1} = BP.bb'{2}) 
        /\ (BP.pk{1} = BS.pk{2})
        /\ (BP.sk{1} = BS.sk{2})
        /\ (size G2L.bb{1} = size BS.encL{2})
        /\ (forall id b, (id, b) \in BP.bb'{2} <=> (b, id) \in BS.encL{2})
        /\ (BP.pk{1} = extractPk BP.sk{1})).
proc. 
if => //. 
inline*.  

seq 9 6 : (
     ={BP.pi, BP.bbstar, id, v0, v1, glob C, glob E, glob HRO.ERO, glob S, BP.pk, BP.setH, BP.vmap}
     /\ !BS.decQueried{2}
     /\ G2L.bb{1} = BP.bb'{2} 
     /\ BP.pk{1} = BS.pk{2} /\ BP.sk{1} = BS.sk{2}
     /\ (id{1} \in BP.setH{1})
     /\ v0{1} = v{1} /\ p{2} = v0{2} /\ l{2} = id{2} /\ id1{1} = id{1} /\ p{2} = v2{1} /\ id1{1} = l{2}
     /\ c{2} = b1{1}
     /\ (size G2L.bb{1} = size BS.encL{2})
     /\ (forall (id : ident) (b : cipher), (id, b) \in BP.bb'{2} <=> (b, id) \in BS.encL{2})
     /\ (BP.pk{1} = extractPk  BP.sk{1})
     
).


call(_: ={BP.pi,  glob HRO.ERO}); first sim. 
auto;progress. 
auto;progress;smt(@List).   
proc;inline*;auto;progress. 
proc;inline*;auto;progress. 
conseq So_ll2;progress. auto;progress.
rewrite size_ge0. 
smt(@List). smt().


have Hx : i1_R = size (flip result_R) by smt(). 
have -> : take i1_R (flip result_R) = flip result_R;
  first by rewrite Hx take_size. print eq_map.
apply eq_map; rewrite //=.
move => x.
rewrite (H7 x.`2 x.`1) //=.
by have ->: x = (x.`1, x.`2) by smt().
qed.


(**** Proof that G3R is equivalent to right hand IND1CCA game ****)

local lemma G3R_CCA_right_equiv &m : 
    Pr[G3R(E,P,Ve,C,A,HRO.ERO,S).main() @ &m : res] = 
    Pr[Ind1CCA(E,BCCA(MV(E,P,Ve,C), A, S), HRO.ERO, Right).main() @ &m : res].
proof. 
byequiv(_: ={glob A, glob C, glob E, glob Ve, glob S,  
             BP.setidents, BP.setHcheck, BP.setH, BP.secmapD, BP.setD}  ==> _) => //. 
proc. 
inline Ind1CCA(E, BCCA(MV(E,P,Ve,C), A,S),HRO.ERO,Right).A.main.
swap{2} [6..11] -5; swap{2} 12 -2; swap{2} [9..10] -2. 



(** Up to the point where adversary creates BP.bb, everything is more or less equivalent **)
seq 15 17 : (
    ={glob HRO.ERO, glob S, glob C, glob E, glob Ve, glob A, BP.pk, BP.setidents, BP.setHcheck, BP.setH, BP.secmapD, BP.setD, BP.sethappy, BP.vmap,
      BP.setchecked, BP.pubmap}
    /\ (G3R.bb{1} = BP.bb'{2})
    /\ (BP.sk{1} = BS.sk{2})
    /\ (BP.pk{2} = BS.pk{2})
    /\ (size BP.bb'{2} = size BS.encL{2})
    /\ (!BS.decQueried{2})
    /\ (forall (id : ident) (b : cipher), (id, b) \in BP.bb'{2} <=> (b, id) \in BS.encL{2})
      /\ (BP.pk{1} = extractPk BP.sk{1} )
). 



inline*.  
while ( ={i, BP.setidents, BP.secmap, BP.secmapD, BP.setD, BP.pubmap} ).
  by auto.  
wp. 


    swap{1} 11 1.
swap{1} 14 1.
call(_:true). wp. 
call (E_kgen_extractpk  HRO.ERO). wp.  
while (={w, HRO.ERO.m}); first by sim. 
auto;progress.

(** The if sentences at the end should also be equivalent **)
seq 6 7 : (={ glob HRO.ERO, glob A, glob S,  glob Ve, valid, BP.setHcheck, 
              BP.r, BP.bb, BP.setchecked, BP.sethappy, BP.pk, BP.vmap, BP.setidents}
    /\ (fdom BP.vmap{1} = fdom BP.vmap{2})
    /\ (G3R.bb{1} = BP.bb'{2})
    /\ (BP.sk{1} = BS.sk{2})); 
  last first. 
  + if => //;progress. 
    + by wp; rnd. 
    if => //. 
    + by wp; call(_ : true); progress.
    
    seq 1 1: (={ HRO.ERO.m, glob A, glob S, glob Ve, valid, BP.setHcheck, BP.r, 
                 BP.vmap, BP.bb, BP.setchecked, BP.sethappy, BP.pk, BP.setidents} 
              /\ G3R.bb{1} = BP.bb'{2} 
              /\ BP.sk{1} = BS.sk{2}
              /\ (BP.setHcheck{1} \subset fdom BP.vmap{1}) 
              /\ valid{1}). 
    + call(: ={ BP.sethappy, BP.setchecked, glob S, HRO.ERO.m, 
                BP.bb, BP.vmap}).
      + sim. sim. sim. 
      by auto.
    if =>/>; first by wp; rnd.
    if =>/>.   
    + rcondf{1} 2; progress.
      + by call (: true).
      rcondf{2} 2; progress.
      + by call(: true).
      by sim.
    rcondt{1} 1; progress.
    rcondt{2} 1; progress. 
    by wp; sim.
rnd.
while ( ={j, BP.bb, dbb, BP.vmap, glob HRO.ERO} /\ (0 <= j{2})
     /\ (BP.sk{1} = BS.sk{2})
     /\ (BP.pk{1} = BS.pk{2})
     /\ (G3R.bb{1} = BP.bb'{2})
     /\ (mL{2} = map (fun (ci : cipher * ident) => 
                   if !( (ci.`2, ci.`1) \in BP.bb'{2} ) 
                     then dec_cipher BS.sk{2} ci.`2 ci.`1 HRO.ERO.m{2}
                     else None) 
                   (flip BP.bb{2}))).
  + wp; sp. 
    if{1}. 
    + wp;skip;progress.
      + rewrite -H. smt(). 
      + smt(). 
      + rewrite -H. smt(). 
      + smt().
      exists* (glob E){1}, BP.sk{1}, idl{1}, b{1}. 
        elim* => ge sk idl b. 
      call{1} (Edec_Odec ge sk idl b). 
      auto=>/>;progress. 
      + smt(). 
      + smt(). 
      + do 3! congr. smt(). 
        rewrite (nth_map witness witness _ j{2} _) . smt(@List).
        have ? : (b, idl) = nth witness (flip BP.bb{2}) j{2}. smt(@List). 
        smt(). 
      + smt(). 

inline Ind1CCA_Oracles(E, HRO.ERO, Right).dec; wp. 
seq 2 2: (={ glob HRO.ERO, glob S, glob C, glob E, glob Ve, glob A, BP.pk,
             BP.setidents, BP.setHcheck, BP.setH, BP.secmapD, BP.setD, 
             BP.sethappy, BP.vmap, BP.setchecked, BP.pubmap, valid, BP.bb} 
          /\ G3R.bb{1} = BP.bb'{2}
          /\ BP.sk{1} = BS.sk{2} 
          /\ BP.pk{2} = BS.pk{2} 
          /\ size BP.bb'{2} = size BS.encL{2} 
          /\ !BS.decQueried{2} 
          /\ (forall (id0 : ident) (b0 : cipher),
                   (id0, b0) \in BP.bb'{2} <=> (b0, id0) \in BS.encL{2}) 
          /\ BP.pk{1} = extractPk BP.sk{1}).
+ call (: ={BP.bb, BP.pk, glob C, HRO.ERO.m}).
    by sim.
  call(_: ={glob C, glob E, glob HRO.ERO, glob S, BP.pk, BP.setH, BP.vmap} 
          /\ (!BS.decQueried{2})
          /\ (G3R.bb{1} = BP.bb'{2}) 
          /\ (BP.pk{1} = BS.pk{2})
          /\ (BP.sk{1} = BS.sk{2})
          /\ (size G3R.bb{1} = size BS.encL{2})
          /\ (forall id b, (id, b) \in BP.bb'{2} <=> (b, id) \in BS.encL{2})
          /\ (BP.pk{1} = extractPk BP.sk{1})).
  + (* ovote *)
    proc.
    if =>//=.
    inline*; wp.
    call(: ={ HRO.ERO.m}).
    + by sim.
    auto =>/>; progress.
    + rewrite size_cat //=. smt().
    + smt(mem_cat).
    + smt(mem_cat).

  + by proc. 
  + by proc.
  + by conseq So_ll2.
  by auto.

rcondt{2} 4; progress.
+ by wp.

wp; 
while{2} (   0 <= i0{2} <= size cL{2}
          /\ mL0{2} = map (fun (ci : cipher * ident) => 
                           if !(ci \in BS.encL{2}) 
                           then dec_cipher BS.sk{2} ci.`2 ci.`1 HRO.ERO.m{2}
                           else None) 
                     (take i0{2} cL{2}))
         (size cL{2} - i0{2}); progress.
  + wp; sp.
    exists* (glob E), BS.sk, l, c. 
      elim* => ge sk idl b. 
    call{1} (Edec_Odec ge sk idl b). 
    auto=>/>;progress. 
    + smt(). 
    + smt(). 
    + rewrite (take_nth witness); first by rewrite H0 H2.  
      rewrite map_rcons -cats1 //=. 
      by rewrite -H H3.  
    + smt(). 
    + smt(). 
    + smt(). 
    + rewrite (take_nth witness); first by rewrite H0 H2.  
      rewrite map_rcons -cats1 //=. 
      by rewrite -H H3. 
    + smt().
auto=>/>; progress.
+ by rewrite size_ge0.
+ smt(). 
+ smt().
+ have ->: i0_R = size (flip BP.bb{2}) by smt().
  rewrite take_size. 
  rewrite (eq_map (fun (ci : cipher * ident) =>
                      if ! (ci \in BS.encL{2})
                      then dec_cipher BS.sk{2} ci.`2 ci.`1 HRO.ERO.m{2}
                      else None) 
                  (fun (ci : cipher * ident) =>
                      if ! ((ci.`2, ci.`1) \in BP.bb'{2}) 
                      then dec_cipher BS.sk{2} ci.`2 ci.`1 HRO.ERO.m{2}
                      else None) 
                  _ (flip BP.bb{2})). 
  + move => x //=. 
    smt().
  by done.
qed.

(**** Helpful lemmas for the final smt call ****)
local lemma G2L_G3R_cca &m : 
    `|Pr[G2L(E,Ve,C,A,HRO.ERO,S).main() @ &m : res] - 
      Pr[G3R(E,P,Ve,C,A,HRO.ERO,S).main() @ &m : res]| =
    `|Pr[Ind1CCA(E,BCCA(MV(E,P,Ve,C),A,S),HRO.ERO,Left).main() @ &m : res] - 
      Pr[Ind1CCA(E,BCCA(MV(E,P,Ve,C),A,S),HRO.ERO,Right).main() @ &m : res]|.
proof.  
by rewrite G2L_CCA_left_equiv G3R_CCA_right_equiv. 
qed.

print G0R_G1R_equiv.
local lemma MB_BPRIV_R_G3R_equiv  &m : 
  BP.setidents{m} = BP.setH{m} `|` BP.setD{m} =>
    Pr[OMB_BPRIV_R(MV(E,P,Ve,C),A,HRO.ERO,G,S,Recover').main() @ &m : res] 
     = Pr[G3R(E,P,Ve,C,A,HRO.ERO,S).main() @ &m : res]. 
proof.
move => IHD.  
by rewrite -G2R_G3R_equiv -G1R_G2R_equiv  -(G0R_G1R_equiv &m IHD) -G0R'_G0R_equiv 
           (MB_BPRIV_R_G0'_R_equiv &m HRO.ERO).  
qed.  


local lemma MB_BPRIV_L_G1L_equiv &m : 
    Pr[OMB_BPRIV_L(MV(E,P,Ve,C),A,HRO.ERO,G).main() @ &m : res] = 
    Pr[G0L(E,P,Ve,C,A,HRO.ERO,G).main() @ &m : res]. 
proof.  
 by rewrite (MB_BPRIV_L_G0L'_equiv &m HRO.ERO)(G0L'_G0L''_equiv &m) G0L''_G0L_equiv.
qed. 



local lemma G1L_IND1CCA_L_equiv &m :
   BP.setidents{m} = BP.setH{m} `|` BP.setD{m} => 
    Pr[G1L(E,Ve,C,A,HRO.ERO,S).main() @ &m : res] = 
    Pr[Ind1CCA(E,BCCA(MV(E,P,Ve,C),A,S),HRO.ERO,Left).main() @ &m : res]. 
proof. 
 move => IHD.
by rewrite (G1L_G2L_equiv &m IHD) G2L_CCA_left_equiv. 
qed.

(**** Final lemma ****)
lemma mb_bpriv &m :
  BP.setidents{m} = BP.setH{m} `|` BP.setD{m} => 
 `|Pr[OMB_BPRIV_L(MV(E,P,Ve,C),A,HRO.ERO,G).main() @ &m : res] 
   - Pr[OMB_BPRIV_R(MV(E,P,Ve,C),A,HRO.ERO,G,S,Recover').main() @ &m : res]|
   <=  
     Pr[VFR(E, BVFR(MV(E,P,Ve,C), A), R(E), HRO.ERO, G).main() @ &m : res] 
   + Pr[VFR(E, BVFR(MV(E,P,Ve,C), A), R(E), HRO.ERO, S).main() @ &m : res] 
   + `|Pr[ZK_L(R(E,HRO.ERO), P, BZK(E,P,C,Ve,A,HRO.ERO), G).main() @ &m : res] 
       -  Pr[ZK_R(R(E,HRO.ERO), S, BZK(E,P,C,Ve,A,HRO.ERO)   ).main() @ &m : res]|
   + `|Pr[Ind1CCA(E,BCCA(MV(E,P,Ve,C),A,S),HRO.ERO,Left).main() @ &m : res] 
       -  Pr[Ind1CCA(E,BCCA(MV(E,P,Ve,C),A,S),HRO.ERO,Right).main() @ &m : res]|.
proof. 

(* add and subtract G1L to first abs value *)
have -> :  `|Pr[OMB_BPRIV_L(MV(E,P,Ve,C),A,HRO.ERO,G).main() @ &m : res] - 
             Pr[OMB_BPRIV_R(MV(E,P,Ve,C),A,HRO.ERO,G,S,Recover').main() @ &m : res]| = 
             `|Pr[OMB_BPRIV_L(MV(E,P,Ve,C),A,HRO.ERO,G).main() @ &m : res] - 
               Pr[G1L(E,Ve,C,A,HRO.ERO,S).main() @ &m : res] +
            Pr[G1L(E,Ve,C,A,HRO.ERO,S).main() @ &m : res] - 
            Pr[OMB_BPRIV_R(MV(E,P,Ve,C),A,HRO.ERO,G,S,Recover').main() @ &m : res]| by smt(@Real). 
(* triangle inequality *)
have ? : `|Pr[OMB_BPRIV_L(MV(E, P, Ve, C), A, HRO.ERO, G).main() @ &m : res] - 
           Pr[G1L(E, Ve, C, A, HRO.ERO, S).main() @ &m : res] +
           Pr[G1L(E, Ve, C, A, HRO.ERO, S).main() @ &m : res] - 
           Pr[OMB_BPRIV_R(MV(E, P, Ve, C), A, HRO.ERO, G, S, Recover').main() @ &m : res]| <=
         `|Pr[OMB_BPRIV_L(MV(E, P, Ve, C), A, HRO.ERO, G).main() @ &m : res] - 
           Pr[G1L(E, Ve, C, A, HRO.ERO, S).main() @ &m : res]| +
         `|Pr[G1L(E, Ve, C, A, HRO.ERO, S).main() @ &m : res] - 
           Pr[OMB_BPRIV_R(MV(E, P, Ve, C), A, HRO.ERO, G, S, Recover').main() @ &m : res]| by smt(@Real). 
by smt. 
qed.

end section MB_BPRIV. 
