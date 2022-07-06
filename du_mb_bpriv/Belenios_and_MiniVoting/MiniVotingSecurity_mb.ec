require import Int Bool Real SmtMap. 
require import List Distr Core FSet. 
require import Logic. 
require import LeftOrRight. 
require (*  *) MiniVotingDefinition_mb. 
require (*  *) ROM.

clone include MiniVotingDefinition_mb.  

(* eager random oracle *)

clone include ROM with
  type in_t       <- h_in,
  type out_t      <- h_out,
  op dout(x:h_in) <- dh_out. 

clone FiniteEager as HRO. 

(****** DU-MB-BPRIV *******)

section DU_MB_BPRIV. 

(** Random oracle **)
declare module G  <: GOracle.Oracle { -BP, -HRO.ERO, -BPS, -BS }.
(** Encryption scheme **)
declare module E  <: Scheme { -BP, -HRO.ERO, -G, -BPS, -BS, -PKEvf.H.Count, -PKEvf.H.HybOrcl, -WrapAdv}.
(** Proof system **)
declare module S  <: Simulator { -BP, -HRO.ERO, -G, -E, -BPS, -BS, -PKEvf.H.Count, -PKEvf.H.HybOrcl, -WrapAdv }.
declare module Ve <: Verifier { -BP, -HRO.ERO, -G, -E, -S, -BPS, -BS }.
declare module P  <: Prover { -BP, -HRO.ERO, -G, -E, -S, -Ve, -BPS, -BS }.
declare module R  <: VotingRelation' { -BP, -HRO.ERO, -G, -E, -S, -Ve, -P, -BPS, -BS }.
(** Validity checker **)
declare module C  <: ValidInd { -BP, -HRO.ERO, -G, -E, -S, -Ve, -P, -R, -BPS, -BS }.

(** Adversary **)
declare module A  <: DU_MB_BPRIV_adv { -BP, -HRO.ERO, -G, -E, -S, -Ve, -P, -R, -C, -BPS, -BS }.

(**** Lossless assumptions ****)

(** Oracles **)
declare axiom Gi_ll : islossless G.init. 
declare axiom Go_ll : islossless G.o. 

(** DU-MB-BPRIV adversary **)
declare axiom A_a1_ll (O <: DU_MB_BPRIV_oracles { -A }):
  islossless O.vote  => 
  islossless O.board => 
  islossless O.h     => 
  islossless O.g     => 
  islossless A(O).create_bb. 
declare axiom A_a2_ll (O <: DU_MB_BPRIV_oracles { -A }): 
  islossless O.board => 
  islossless O.h     => 
  islossless O.g     => 
  islossless A(O).get_tally. 
declare axiom A_a3_ll (O <: DU_MB_BPRIV_oracles { -A }): 
  islossless O.verify => 
  islossless O.h      => 
  islossless O.g      => 
  islossless A(O).final_guess. 
declare axiom A_a4_ll (O <: DU_MB_BPRIV_oracles { -A }): 
  islossless O.h => 
  islossless O.g => 
  islossless A(O).initial_guess. 

(** Proof system **)
declare axiom PS_p_ll (G <: GOracle.POracle { -P })  : islossless G.o => islossless P(G).prove. 
declare axiom PS_v_ll (G <: GOracle.POracle { -Ve }) : islossless G.o => islossless Ve(G).verify. 

(** Encryption **)
declare axiom E_kg_ll  (H <: HOracle.POracle { -E }) : islossless H.o => islossless E(H).kgen. 
declare axiom E_enc_ll (H <: HOracle.POracle { -E }) : islossless H.o => islossless E(H).enc. 
declare axiom E_dec_ll (H <: HOracle.POracle { -E }) : islossless H.o => islossless E(H).dec. 

(** Encryption with HRO.ERO **)
lemma E_kg_ll'  : islossless E(HRO.ERO).kgen by apply (E_kg_ll HRO.ERO HRO.ERO_o_ll). 
lemma E_enc_ll' : islossless E(HRO.ERO).enc by apply (E_enc_ll HRO.ERO HRO.ERO_o_ll). 
lemma E_dec_ll' : islossless E(HRO.ERO).dec by apply (E_dec_ll HRO.ERO HRO.ERO_o_ll). 

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

hoare ERO_eager (gh : (glob HRO.ERO)):
  HRO.ERO.o: (glob HRO.ERO) = gh ==> (glob HRO.ERO) = gh.
proof. by proc; auto. qed.

(* axiom on result distribution *)
declare axiom Rho_weight x:
  weight (Rho x) = 1%r. 

(* axiom linking key generation and getPK operator *)
declare axiom E_kgen_getPK_hr (H <: HOracle.POracle { -E }):
  hoare [E(H).kgen: true ==> res.`1 = getPK res.`2].

equiv E_kgen_getPK (H <: HOracle.POracle { -E }):
  E(H).kgen ~ E(H).kgen : ={glob H, glob E} 
        ==> ={glob H, glob E, res} /\ res{1}.`1 = getPK res{1}.`2.
proof. by conseq (: _ ==> ={glob H, glob E, res}) (E_kgen_getPK_hr H); sim. qed.

(* voting relation does not change state of eager random oracle *)
phoare relConstraint (gh : (glob HRO.ERO)):
  [ R(E,HRO.ERO).main : 
      (glob HRO.ERO) = gh ==> (glob HRO.ERO) = gh] = 1%r.
proof.
conseq R_m_ll (: (glob HRO.ERO) = gh ==> (glob HRO.ERO) = gh)=> //.
by proc ((glob HRO.ERO) = gh)=> //; exact: ERO_eager.
qed.

(* decryption operator with access to a map of values, 
     instead of random oracle*)
op dec_cipher: skey -> label -> cipher -> (h_in, h_out) SmtMap.fmap -> vote option.

(* axiom for linking E.dec to dec_cipher operator *)   
declare axiom Edec_Odec_hr (ge: (glob E)) (sk2: skey)(l2: label) (c2: cipher):
  hoare [E(HRO.ERO).dec:  
           (glob E) = ge /\ arg = (sk2, l2, c2)
           ==> (glob E) = ge /\
               res = dec_cipher sk2 l2 c2 HRO.ERO.m ].

phoare Edec_Odec (ge: (glob E)) (sk2: skey)(l2: label) (c2: cipher):
  [E(HRO.ERO).dec:
      (glob E) = ge /\ arg = (sk2, l2, c2)
      ==>   
      (glob E) = ge /\
      res = dec_cipher sk2 l2 c2 HRO.ERO.m ] = 1%r.
proof. by conseq E_dec_ll' (Edec_Odec_hr ge sk2 l2 c2). qed.

equiv Edec_Odec_eq (sk2: skey)(l2: label) (c2: cipher):
  E(HRO.ERO).dec ~ E(HRO.ERO).dec :
     ={glob HRO.ERO, glob E, arg}/\ arg{1} = (sk2, l2, c2)
     ==>   
     ={glob HRO.ERO, glob E, res} /\
     res{1} = dec_cipher sk2 l2 c2 HRO.ERO.m{1}.
proof.
exists* (glob E){1}; elim* => ge.
conseq (: _ ==> ={glob HRO.ERO, glob E, res}) (Edec_Odec_hr ge sk2 l2 c2)=> //.
by sim.
qed.

(* axiom on the state of the encryption scheme E *)
declare axiom Ee_hr (ge: (glob E)):
  hoare [E(HRO.ERO).enc: (glob E) = ge ==> (glob E) = ge].

phoare Ee_eq (ge: (glob E)):
  [E(HRO.ERO).enc: (glob E) = ge ==> (glob E) = ge] = 1%r.
proof. by conseq E_enc_ll' (Ee_hr ge). qed.

(* axiom for transforming an encryption into decryption (one-sided) *)
declare axiom Eenc_decL_hr (ge: (glob E)) (sk2: skey) 
                   (l2: label) (p2: vote): 
  hoare [E(HRO.ERO).enc : 
          (glob E) = ge /\ arg=(getPK sk2, l2, p2) 
          ==> 
          (glob E) = ge /\
          Some p2 = dec_cipher sk2 l2 res HRO.ERO.m ].

phoare Eenc_decL (ge : (glob E)) _sk _l _p:
  [E(HRO.ERO).enc:
     (glob E) = ge /\ arg = (getPK _sk, _l, _p)
     ==> (glob E) = ge /\ dec_cipher _sk _l res HRO.ERO.m = Some _p] = 1%r.
proof. by conseq (Ee_eq ge) (Eenc_decL_hr ge _sk _l _p)=> /> &0 r <-. qed.
                
equiv Eenc_dec (sk2: skey) (l2: label) (p2: vote): 
  E(HRO.ERO).enc ~ E(HRO.ERO).enc : 
     ={glob HRO.ERO, glob E, arg} /\ arg{1} = (getPK sk2, l2, p2) 
     ==> 
     ={glob HRO.ERO, glob E,  res} /\
     Some p2 = dec_cipher sk2 l2 res{1} HRO.ERO.m{1}.
proof.
exists * (glob E){1}; elim * => ge.
conseq (: _ ==> ={glob HRO.ERO, glob E, res}) (Eenc_decL_hr ge sk2 l2 p2)=> //.
by sim.
qed.

(* injectivity of Flabel *)
lemma Flabel_inj x y:
  Flabel x = Flabel y => x = y by apply inj_idfun.

(* the state of the simulator oracle is the same in two-sided call *)
local equiv So_ll2: S.o ~ S.o : ={arg, glob S} ==> ={res, glob S}.
proof. by proc true. qed.    

(* Operator to reverse the order of tuples *)
op flip['a] (bb : ('a * cipher) list) = map (fun b : ('a * cipher) => (b.`2, b.`1)) bb. 

(* Operator removing the first element of a three tuple *)
op rem_fst3 (x : ('a * 'b * 'c)) = (x.`2, x.`3).

(* Operator removing first element of a four tuple *)
op rem_fst4 (x : ('a * 'b * 'c * 'd)) = (x.`2, x.`3, x.`4).

(*******************************************************************************************************)
(******************** Constructed adversaries from du-mb-bpriv adversary *******************************)
(*******************************************************************************************************)

(************ Construct a ZK adversary from du-mb-bpriv adversary *************)
module type VotingAdvZK (H:HOracle.Oracle, O:GOracle.POracle) = {
  proc a1() : (pkey * pubBB * result) * (skey * (label * cipher) list) {H.init, H.o, O.o}
  proc a2(pi : prf option) : bool {H.o, O.o}
}.
 

module BZK(E:Scheme, P:Prover, C:ValidInd, Ve:Verifier, 
           A:DU_MB_BPRIV_adv, H:HOracle.Oracle, G:GOracle.POracle) = {

  module O  = DU_MB_BPRIV_oracles(MV(E,P,Ve,C), H, G, Left)
  module MV = MV(E,P,Ve,C,H,G) 

  proc a1() : (pkey * pubBB * result) * (skey * (label * cipher) list) = {
    
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
    BP.pc_to_id   <- empty;

    H.init();
    
    (BP.pk, BP.sk) <@ E(H).kgen();
    
    i <- 0;
    while (i < card BP.setidents) {
      id <- nth witness (elems BP.setidents) i;
      BP.secmap.[id] <- tt;
      BP.pubmap.[id] <- Flabel id;
      BP.pc_to_id.[Flabel id] <- id;
      if (id \in BP.setD) {
        BP.secmapD.[id] <- oget BP.secmap.[id];
      }
    i <- i + 1;
    }

    BP.bb <@ A(O).create_bb(BP.pk, BP.secmapD, BP.pubmap, BP.setHcheck);

    dbb <- [];
     j <- 0;
     while (j < size BP.bb) {
      (idl, b) <- nth witness BP.bb j;
         v     <@ E(H).dec(BP.sk, idl, b);
       dbb     <- dbb ++ [(idl, v)];
         j     <- j + 1;
      }
       BP.r <$ Rho dbb;
    
    return ((BP.pk, Publish BP.bb, BP.r), (BP.sk, BP.bb));

  }
 
  proc a2(pi:prf option) : bool = {
    var valid, valid', d;

    valid <@ MV.validboard(BP.bb, BP.pk);
    
    if (!(BP.setHcheck \subset fdom BP.vmap)) {
      BP.d <$ {0,1};
    } elif (!valid) {
      BP.d <$ {0,1};
    } else {
         d       <@ A(O).initial_guess();
      BP.bbstar  <@ A(O).get_tally(BP.r, oget pi);
      valid'     <@ MV.verifytally((BP.pk, Publish BP.bb, BP.bbstar.`1), BP.bbstar.`2);
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

    return BP.d;
  }
}. 

(************* Construct VFR adversary from du-mb-bpriv adversary **************)

module BVFR(V:VotingSystem, A:DU_MB_BPRIV_adv, H:HOracle.POracle, G:GOracle.POracle) = {
  
  module L = DU_MB_BPRIV_oracles(V,H,G,Left)

  proc main(pk:pkey) : (label * cipher) list = {
    
    var i, id;
    
    BP.vmap    <- empty;
    BP.pubmap  <- empty;
    BP.secmap  <- empty;
    BP.secmapD <- empty;
    BP.pc_to_id<- empty;
    BP.bb0     <- [];
    BP.bb1     <- [];
    BP.pk      <- pk;

    i <- 0;
    while (i < card BP.setidents) {
      id <- nth witness (elems BP.setidents) i;
      BP.secmap.[id] <- tt;
      BP.pubmap.[id] <- Flabel id;
      BP.pc_to_id.[Flabel id] <- id;
      if (id \in BP.setD) {
        BP.secmapD.[id] <- oget BP.secmap.[id];
      }
    i <- i + 1;
    }
   BP.bb <@ A(L).create_bb(BP.pk, BP.secmapD, BP.pubmap, BP.setHcheck);
   return BP.bb; 
  }
}.

(*************** Construct CCA adversary from du-mb-bpriv adversary **********)

module BCCA(V:VotingSystem, A:DU_MB_BPRIV_adv, S:Simulator, IO:Ind1CCA_Oracles) = {

  module V = V(HRO.ERO, S)

  module O = {

    proc h = IO.o
    proc g = S.o
    
    proc vote(id:ident, v0 v1: vote) = {
      var b;
      
      if ((id \in BP.setH)) {
        b <@ IO.enc(Flabel id, v0, v1);
        BP.vmap.[id] <- (b, b, b, v0) :: (odflt [] BP.vmap.[id]);
        BP.bb' <- (Flabel id, b) :: BP.bb';
      }

    }

    proc verify(id:ident) = {
      var ok, sv;
      if (id \in BP.setidents){
        BP.setchecked <- BP.setchecked `|` (fset1 id);

        sv <- odflt [] (BP.vmap.[id]);
        ok <@ V.verifyvote(id, (oget (ohead sv)).`2, 
                         (oget (ohead sv)).`3, BP.bb, BP.bbstar, Flabel id, tt);
        if (ok) {
          BP.sethappy <- BP.sethappy `|` (fset1 id);
        }
      }
      return BP.sethappy;
    }

   proc board() : pubBB = {
      return Publish(BP.bb');
   }
  }

  module A = A(O)

  proc main(pk:pkey) : bool = {
    var i, id, d;
    var valid, valid';
    var dbb, j, idl, b, v;
    var mL;
    
    BP.vmap       <- empty;
    BP.pubmap     <- empty;
    BP.secmap     <- empty;
    BP.secmapD    <- empty;
    BP.pc_to_id   <- empty;
    BP.setchecked <- fset0;
    BP.sethappy   <- fset0;

    BP.bb' <- [];

    S.init();

    BP.pk <- pk;

    (* register *)
    i <- 0;
    while (i < card BP.setidents) {
      id <- nth witness (elems BP.setidents) i;
      BP.secmap.[id] <- tt;
      BP.pubmap.[id] <- Flabel id;
      BP.pc_to_id.[Flabel id] <- id;
      if (id \in BP.setD) {
        BP.secmapD.[id] <- oget BP.secmap.[id];
      }
    i <- i + 1;
    }

    (* adversary creates bulletin board *)
    BP.bb <@ A.create_bb(BP.pk, BP.secmapD, BP.pubmap, BP.setHcheck);

    (* check if adversary board is valid *)
    valid <@ V.validboard(BP.bb, BP.pk);

    (* tally *)
    mL <@ IO.dec(flip (BP.bb));
    dbb <- [];
      j <- 0;
    while (j < size BP.bb) {
      (idl, b) <- nth witness BP.bb j;
         if ( (idl, b) \in BP.bb') {
           (* get the vote from vmap *)
           v <- Some (oget (onth (odflt [] BP.vmap.[ idl]) 
                              (find (fun (x : cipher*cipher*cipher*vote) => x.`1 = b) 
                              (odflt [] BP.vmap.[idl])))).`4;
         } else {
           v <- nth witness mL j;
         }
      dbb <- dbb ++ [(idl, v)];
       j  <- j + 1;
    }

    BP.r <$ Rho dbb;

    if (!BP.setHcheck \subset fdom BP.vmap) {
      BP.d <$ {0,1};
    } elif (!valid) {
      BP.d <$ {0,1}; 
    } else {
        BP.pi <@ S.prove(BP.pk, Publish BP.bb, BP.r);
          d   <@ A.initial_guess();
        BP.bbstar   <@ A.get_tally(BP.r, BP.pi);
          valid'   <@ V.verifytally((BP.pk,Publish BP.bb, BP.bbstar.`1), BP.bbstar.`2);
      if (!valid') {
        BP.d <$ {0,1};
      } else {
        BP.d <@ A.final_guess();
        if (!(BP.setHcheck \subset BP.sethappy)) {
          BP.d <- d; 
        } 
        if (!(BP.setHcheck \subset BP.setchecked)) {
          BP.d <$ {0,1};
        }
      }
    }
    return BP.d; 
  }

}. 

(****************************************************************************************************)
(****************************************************************************************************)
(****************************************************************************************************)

(**************************************************************************************************)
(********* Proof that MiniVoting satisfies DU-MB-BPRIV structured as a sequence of games. *********)
(*********   We start by modyfing the left hand side.                                     *********)
(**************************************************************************************************)

(*** We start with a game that simply unpacks some of the procs in the security definitions ***)

local module G0L' (E:Scheme, P:Prover, Ve:Verifier, C:ValidInd, 
                   A:DU_MB_BPRIV_adv, H:HOracle.Oracle, G:GOracle.Oracle)  = {

  module O  = DU_MB_BPRIV_oracles(MV(E, P, Ve, C), H, G, Left)
  module A  = A(O)
  module MV = MV(E,P,Ve,C,H,G)
 
  proc main() : bool = {
    var i, id;
    var valid, valid';
    var dbb, j, idl, b, v, d;
    
    BP.vmap    <- empty;
    BP.pubmap  <- empty;
    BP.secmap  <- empty;
    BP.secmapD <- empty;
    BP.pc_to_id<- empty;
    BP.bb0     <- [];
    BP.bb1     <- [];
    BP.setchecked <- fset0;
    BP.sethappy   <- fset0;

    H.init();
    G.init();

    (* setup: key generation *)
    (BP.pk, BP.sk) <@ MV.setup();

    (* registration *)
    i <- 0;
    while (i < card BP.setidents) {
      id <- nth witness (elems BP.setidents) i;
      BP.secmap.[id]          <- tt;
      BP.pubmap.[id]          <- Flabel id;
      BP.pc_to_id.[Flabel id] <- id;
      if (id \in BP.setD) {
        BP.secmapD.[id] <- oget BP.secmap.[id];
      }
    i <- i + 1;
    }

    (* adversary creates first bulletin board *)
    BP.bb <@ A.create_bb(BP.pk, BP.secmapD, BP.pubmap, BP.setHcheck);
    
    if (!(BP.setHcheck \subset fdom BP.vmap)) {
      BP.d <$ {0,1};
    } else {
      valid <@ MV.validboard(BP.bb, BP.pk);
      if (!valid) {
        BP.d <$ {0,1}; 
      } else {
             dbb     <- [];
              j      <- 0;
          while (j < size BP.bb) {
            (idl, b) <- nth witness BP.bb j;
               v     <@ E(H).dec(BP.sk, idl, b);
               dbb   <- dbb ++ [(idl, v)];
                j    <- j + 1;
          }
          BP.r   <$ Rho dbb;
          BP.pk  <- getPK BP.sk;
          BP.pi  <@ P(G).prove((BP.pk, Publish BP.bb, BP.r), (BP.sk, BP.bb));
             d   <@ A.initial_guess();
         BP.bbstar   <@ A.get_tally(BP.r, BP.pi);
            valid'   <@ MV.verifytally((BP.pk, Publish BP.bb, BP.bbstar.`1), BP.bbstar.`2);
        if (!valid') {
          BP.d <$ {0,1};
        } else {
           BP.d <@ A.final_guess();
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

(*** Lemma proving that G0L' is perfectly equivalent to the original definition ***)
local lemma DU_MB_BPRIV_L_G0L'_equiv &m (H <: HOracle.Oracle{ -E, -BP, -G, -A, -C, -Ve, -P}) : 
  Pr[DU_MB_BPRIV_L(MV(E, P, Ve, C), A, H, G).main() @ &m : res] =
  Pr[G0L'(E,P,Ve,C,A,H,G).main() @ &m : res].
proof. 
byequiv => //; proc; inline*; sim. 
while ( ={i, BP.setidents, BP.secmap, BP.pubmap, BP.setD, BP.secmapD}).
+ by sim; auto=>/>.    
by wp; do 3!call(: true); auto.
qed.

(*** We now move the tally and the check that BP.bb is valid outside of         ***)
(*** the if statements and prove that the resulting game is equivalent to G0_L' ***) 
local module G0L (E:Scheme, P:Prover, Ve:Verifier, C:ValidInd, 
                  A:DU_MB_BPRIV_adv, H:HOracle.Oracle, G:GOracle.Oracle)  = {

  module O  = DU_MB_BPRIV_oracles(MV(E, P, Ve, C), H, G, Left)
  module A  = A(O)
  module MV = MV(E,P,Ve,C,H,G)
 
  proc main() : bool = {
    var i, id;
    var valid, valid';
    var dbb, j, idl, b, v, d;
    
    BP.vmap    <- empty;
    BP.pubmap  <- empty;
    BP.secmap  <- empty;
    BP.secmapD <- empty;
    BP.pc_to_id<- empty;
    BP.bb0     <- [];
    BP.bb1     <- [];
    BP.setchecked <- fset0;
    BP.sethappy   <- fset0;

    H.init();
    G.init();

    (* setup: key generation *)
    (BP.pk, BP.sk) <@ MV.setup();

    (* registration *)
    i <- 0;
    while (i < card BP.setidents) {
      id <- nth witness (elems BP.setidents) i;
      BP.secmap.[id] <- tt;
      BP.pubmap.[id] <- Flabel id;
      BP.pc_to_id.[Flabel id] <- id;
      if (id \in BP.setD) {
        BP.secmapD.[id] <- oget BP.secmap.[id];
      }
    i <- i + 1;
    }

    (* adversary creates first bulletin board *)
    BP.bb <@ A.create_bb(BP.pk, BP.secmapD, BP.pubmap, BP.setHcheck);

    (* is BP.bb valid? *)
    valid <@ MV.validboard(BP.bb, BP.pk);

    (* tally *)
    dbb <- [];
    j <- 0;
    while (j < size BP.bb) {
      (idl, b) <- nth witness BP.bb j;
        v      <@ E(H).dec(BP.sk, idl, b);
        dbb    <- dbb ++ [(idl, v)];
        j      <- j + 1;
    }
    BP.r  <$ Rho dbb;
    BP.pk <- getPK BP.sk;

    if (!BP.setHcheck \subset fdom BP.vmap) {
      BP.d <$ {0,1};
    } elif (!valid) {
      BP.d <$ {0,1};
    } else {
      BP.pi <@ P(G).prove((BP.pk,Publish BP.bb, BP.r), (BP.sk, BP.bb));
         d  <@ A.initial_guess();
      BP.bbstar  <@ A.get_tally(BP.r, BP.pi);
      valid'     <@ MV.verifytally((BP.pk,Publish BP.bb, BP.bbstar.`1), BP.bbstar.`2);
      if (!valid') {
        BP.d <$ {0,1};
      } else {
         BP.d <@ A.final_guess();
        if (!(BP.setHcheck \subset BP.sethappy)) {
          BP.d <- d; 
        } 
        if (!(BP.setHcheck \subset BP.setchecked)) {
          BP.d <$ {0,1};
        }
      }
    }
     
    return BP.d;
  }
}. 
 
(*** Lemma proving that G0L' and G0L are equivalent ***)

local lemma G0L'_G0L_equiv &m:
  Pr[G0L'(E,P,Ve,C,A,HRO.ERO,G).main() @ &m : res] =
  Pr[G0L(E,P,Ve,C,A,HRO.ERO,G).main() @ &m : res]. 
proof. 
byequiv => //; proc.
seq 15 15 : ( ={glob HRO.ERO, glob A, glob C, glob P, glob Ve, glob E, glob G, BP.bb, 
                BP.pk, BP.sk, BP.pubmap, BP.secmap, BP.vmap,BP.setchecked, BP.setHcheck, 
                BP.sethappy, BP.bb0, BP.bb1, BP.secmapD, BP.pc_to_id, BP.setidents}).
+ by sim.
if {1}.
+ rcondt {2} 7.
  + by auto; inline *; while (true); auto; while (true); auto.
  rnd=> //=.
  conseq _ _ (:_ ==> true: =1%r)=> //.
  auto; while (true) (size BP.bb - j).
  + by auto; call E_dec_ll'; auto=> /#.
  inline *; wp; while (true) (size bb - i0).
  + auto; sp; if; auto=> [|/#].
    by call (C_vi_ll HRO.ERO HRO.ERO_o_ll); auto=> /#.
  by auto; smt(Rho_weight).
seq 1 1 : (={valid, glob A, glob G, glob HRO.ERO, glob E, glob P, glob Ve, 
             BP.setHcheck, BP.sethappy, BP.sk, BP.setchecked, BP.pubmap, BP.secmap,
             BP.vmap, BP.bb, BP.bb0, BP.bb1, BP.setidents}
           /\ BP.setHcheck{1} \subset fdom BP.vmap{1}).
+ by conseq (: ={valid, glob A, glob G, glob HRO.ERO, glob E, glob P, glob Ve, 
             BP.setHcheck, BP.sethappy, BP.sk, BP.setchecked, BP.pubmap, BP.secmap,
             BP.vmap, BP.bb, BP.bb0, BP.bb1, BP.setidents})=> //; sim.
rcondf {2} 6; first by auto; conseq (: true).
if{1}.
+ rcondt {2} 6; first by auto; conseq (: true).
  rnd.
  conseq _ _ (: _ ==> true: =1%r).
  auto; while true (size BP.bb - j).
  + by auto; call E_dec_ll'; auto=> /#.
  by auto; smt (Rho_weight size_ge0).
rcondf {2} 6; first by auto; conseq (: true).
by sim.
qed. 

(*** Simulate the proof of correct tally, still in the left world ***)

local module G1L (E:Scheme, Ve:Verifier, C:ValidInd, 
                  A:DU_MB_BPRIV_adv, H:HOracle.Oracle, S:Simulator)  = {

  module O  = DU_MB_BPRIV_oracles(MV(E, P, Ve, C), H, S, Left)
  module A  = A(O)
  module MV = MV(E,P,Ve,C,H,S)
 
  proc main() : bool = {
    var i, id;
    var valid, valid';
    var dbb, j, idl, b, v, d;
    
    BP.vmap    <- empty;
    BP.pubmap  <- empty;
    BP.secmap  <- empty;
    BP.secmapD <- empty;
    BP.pc_to_id   <- empty;
    BP.bb0     <- [];
    BP.bb1     <- [];
    BP.setchecked <- fset0;
    BP.sethappy   <- fset0;

    H.init();
    S.init();

    (* setup: key generation *)
    (BP.pk, BP.sk) <@ MV.setup();

    (* registration *)
    i <- 0;
    while (i < card BP.setidents) {
      id <- nth witness (elems BP.setidents) i;
      BP.secmap.[id] <- tt;
      BP.pubmap.[id] <- Flabel id;
      BP.pc_to_id.[Flabel id] <- id;
      if (id \in BP.setD) {
        BP.secmapD.[id] <- oget BP.secmap.[id];
      }
    i <- i + 1;
    }

    (* adversary creates first bulletin board *)
    BP.bb <@ A.create_bb(BP.pk, BP.secmapD, BP.pubmap, BP.setHcheck);
    
    (* is BP.bb valid? *)
    valid <@ MV.validboard(BP.bb, BP.pk);

    (* tally *)
    dbb <- [];
    j <- 0;
    while (j < size BP.bb) {
      (idl, b) <- nth witness BP.bb j;
        v      <@ E(H).dec(BP.sk, idl, b);
        dbb    <- dbb ++ [(idl, v)];
        j      <- j + 1;
    }
    BP.r  <$ Rho dbb;
    BP.pk <- getPK BP.sk;

    if (!(BP.setHcheck \subset fdom BP.vmap)) {
      BP.d <$ {0,1};
    } elif (!valid) {
      BP.d <$ {0,1};
    } else {
          BP.pi  <@ S.prove((BP.pk, Publish BP.bb, BP.r));
           d     <@ A.initial_guess();
      BP.bbstar  <@ A.get_tally(BP.r, BP.pi);
      valid'     <@ MV.verifytally((BP.pk, Publish BP.bb, BP.bbstar.`1), BP.bbstar.`2);
      if (!valid') {
        BP.d <$ {0,1};
      } else {
         BP.d <@ A.final_guess();
        if (!(BP.setHcheck \subset BP.sethappy)) {
          BP.d <- d; 
        } 
        if (!(BP.setHcheck \subset BP.setchecked)) {
          BP.d <$ {0,1};
        }
      }
    }
     
    return BP.d;
    }
}. 

(*** Losslessness for BZK, useful in the ZK part a bit further down  ***)

local lemma BZK_a1_ll (H <: HOracle.Oracle { -E, -BP, -A }) (G <: GOracle.POracle { -A }) : 
  islossless H.init =>  
  islossless H.o => 
  islossless G.o => 
  islossless BZK(E, P, C, Ve, A, H, G).a1. 
proof. 
move => Hi_ll Ho_ll Go_ll.
proc; rnd; while true (size BP.bb - j).
+ by auto; call (E_dec_ll H Ho_ll); auto=> /#.
wp; call(A_a1_ll (<: BZK(E,P,C,Ve,A,H,G).O)).
+ proc; if=> //; inline *.
  auto; call (E_enc_ll H Ho_ll).
  auto; call (E_enc_ll H Ho_ll).
  by auto.
+ by proc; inline *; auto.
while true (card BP.setidents - i).
+ by auto; smt(fcard_ge0).
auto; call (E_kg_ll H Ho_ll).
auto; call Hi_ll.
by auto=> />; smt(Rho_weight).
qed.

lemma BZK_a2_ll' (H <: HOracle.Oracle { -C, -A }) 
                 (G <: GOracle.POracle { -Ve, -A })
                 (P <: Prover { -A }) :
  islossless H.o => 
  islossless G.o => 
  islossless P(G).prove =>
  islossless BZK(E,P,C,Ve,A,H,G).a2. 
proof. 
move=>  Ho_ll Go_ll Pp_ll.
proc.
seq  1: true=> //.
+ inline *; wp; while true (size bb - i); auto=> [|/#].
  sp; if; auto=> [|/#].
  by call (C_vi_ll H Ho_ll); auto=> /#.
if=> //; first by auto; smt(DBool.dbool_ll).
if=> //; first by auto; smt(DBool.dbool_ll).
seq  3: true=> //.
+ inline *; wp; call(PS_v_ll G Go_ll).
  wp; call(A_a2_ll (<: BZK(E,P,C,Ve,A,H,G).O)).
  + by islossless.
  by call(A_a4_ll (<: BZK(E,P,C,Ve,A,H,G).O)).
if=> //; first by auto; smt(DBool.dbool_ll).
seq  1: true=> //.
+ call(A_a3_ll (<: BZK(E,P,C,Ve,A,H,G).O))=> //.
  by islossless.
by sp; if=> //; auto; smt(DBool.dbool_ll).
qed.

lemma BZK_a2_ll (H <: HOracle.Oracle { -C, -A }) (G <: GOracle.POracle { -P, -Ve, -A }) : 
  islossless H.o =>
  islossless G.o => 
  islossless BZK(E,P,C,Ve,A,H,G).a2.
proof.
move=> Ho_ll Go_ll. 
exact: (BZK_a2_ll' H G P Ho_ll Go_ll (PS_p_ll G Go_ll)).
qed.

(****************************************************************************************************)
(***** Here starts the ZK part ending with a lemma proving that the advantage in distinguishing *****)
(***** between G0L and G1L is bounded by |ZK_L - ZK_R| + 2*VFR advantage.                       *****)
(****************************************************************************************************)

(************************* Left game for ZK without checking relation *************************)

local module ZKFL(E:Scheme, R:VotingRelation', P:Prover, 
                  A:VotingAdvZK, H:HOracle.Oracle, O:GOracle.Oracle) = {
  proc main() : bool = {
    var p;
    O.init();
    (BPS.s, BPS.w) <@ A(H,O).a1();
    BPS.rel        <@ R(E,H).main(BPS.s, BPS.w);
    p              <@ P(O).prove(BPS.s, BPS.w);
    BPS.p          <- Some p;
    BPS.b          <@ A(H,O).a2(BPS.p);
    return BPS.b;
  }
}.

(************************* Right game for ZK without checking relation *************************)

local module ZKFR(E:Scheme, R:VotingRelation', S:Simulator, 
                  A:VotingAdvZK, H:HOracle.Oracle) = {
  proc main() : bool = {
    var p;
    S.init();
    (BPS.s, BPS.w) <@ A(H,S).a1();
    BPS.rel        <@ R(E,H).main(BPS.s, BPS.w);
    p              <@ S.prove(BPS.s);
    BPS.p          <- Some p;
    BPS.b          <@ A(H,S).a2(BPS.p);
    return BPS.b;
  }
}.

(************************* Relate ZKFL to non local module ZK_L *************************)
local lemma ZKFL_ZKL &m :
  `|Pr[ZKFL(E,R,P,BZK(E,P,C,Ve,A),HRO.ERO,G).main() @ &m : res]
    - Pr[ZK_L(R(E,HRO.ERO),P,BZK(E,P,C,Ve,A,HRO.ERO),G).main() @ &m : res]|
   <=
     Pr[ZK_L(R(E,HRO.ERO),P,BZK(E,P,C,Ve,A,HRO.ERO),G).main() @ &m : !BPS.rel].
proof.
byequiv (: ={glob A, glob C, glob R, glob P, glob Ve, glob E, glob G, glob HRO.ERO,
             BP.setHcheck, BP.secmapD, BP.pubmap, BP.secmap, BP.setD,
             BP.setidents, BP.d, BP.setH, BP.bb1, BP.bb0, BP.r, BP.sethappy,
             BP.setchecked, BP.vmap, BP.pk, BP.bb}
           ==> ={BPS.rel} /\ (BPS.rel{2} => ={res})): (!BPS.rel)=> [|//|/#].
proc.
seq 3 3 : (={glob P, glob R, glob HRO.ERO, glob G, glob A, glob E, glob C, glob Ve, BPS.s, BPS.w, BPS.rel,
             BP.secmapD, BP.setD, BP.setidents, BP.setH, BP.bb1, BP.bb0, BP.setHcheck, BP.r, BP.d,
             BP.pubmap, BP.secmap, BP.sethappy, BP.setchecked, BP.vmap, BP.pk, BP.bb, BPS.rel, BPS.s, BPS.w}).
+ by sim.
if{2}; first by sim.
call{1} (BZK_a2_ll' HRO.ERO G P HRO.ERO_o_ll Go_ll (PS_p_ll G Go_ll)).
call{2} (BZK_a2_ll' HRO.ERO G P HRO.ERO_o_ll Go_ll (PS_p_ll G Go_ll)).
by wp; call{1} (PS_p_ll G Go_ll).
qed.

(******************* Relate ZKFR to non local module ZK_R *************************)

local lemma ZKFR_ZKR &m :
  `|Pr[ZKFR(E,R,S,BZK(E,P,C,Ve,A),HRO.ERO).main() @ &m : res]
    - Pr[ZK_R(R(E,HRO.ERO),S,BZK(E,P,C,Ve,A,HRO.ERO)).main() @ &m : res]|
    <=
      Pr[ZK_R(R(E,HRO.ERO),S,BZK(E,P,C,Ve,A,HRO.ERO)).main() @ &m : !BPS.rel].
proof.  
byequiv (: ={glob A, glob C, glob R, glob P, glob Ve, glob E, glob S, BP.setHcheck, BP.secmapD, BP.pubmap, BP.secmap,
             BP.setD, BP.setidents, BP.d, BP.setH, BP.bb1, BP.bb0, BP.r, BP.sethappy,  glob HRO.ERO,
             BP.setchecked, BP.vmap, BP.pk, BP.bb}
           ==> ={BPS.rel} /\ (BPS.rel{2} => ={res})): (!BPS.rel)=> [|//|/#].
proc.
seq 3 3 : (={glob P, glob R, glob HRO.ERO, glob S, glob A, glob E, glob C, glob Ve, BPS.s, BPS.w, BPS.rel,
             BP.secmapD, BP.setD, BP.setidents, BP.setH, BP.bb1, BP.bb0, BP.setHcheck, BP.r, BP.d, BP.pubmap,
             BP.secmap, BP.setHcheck, BP.sethappy, BP.setchecked, BP.vmap, BP.pk, BP.bb, BPS.rel, BPS.s, BPS.w}).
+ by sim.
if{2}; first by sim.
call{1} (BZK_a2_ll HRO.ERO S HRO.ERO_o_ll So_ll).
call{2} (BZK_a2_ll HRO.ERO S HRO.ERO_o_ll So_ll).
by wp; call{1} (Sp_ll).
qed.

(*************** Lemma bounding the probability that the relation does not hold in ZK_L by ***************)
(***************     the probability of returning true in the VFR game.                    ***************)

local lemma ZKL_rel &m (H <: HOracle.Oracle { -A, -BPS, -BP, -BS, -Ve, -E, -C, -R })
                       (G <: GOracle.Oracle { -A, -BPS, -BP, -BS, -Ve, -E, -H, -R, -C })
                       (P <: Prover { -E, -C, -Ve, -A, -R, -BPS, -BP, -BS, -H, -G }) :
  islossless H.o =>
  islossless G.o =>
  islossless P(G).prove =>
    Pr[ZK_L(R(E,H), P, BZK(E,P,C,Ve,A,H), G).main() @ &m : !BPS.rel]
  <= Pr[VFR(E, BVFR(MV(E,P,Ve,C), A), R(E), H, G).main() @ &m : res].
proof.
move=> Ho_ll Go_ll Pp_ll.
byequiv (:    ={glob A, glob E, glob P, glob Ve, glob C, glob H, glob G, glob R}
           /\ ={setidents, setD, secmapD, setH, bb0, bb1, setHcheck}(BP, BP)
           ==> _)=> //.
proc.
call {1} (BZK_a2_ll' H G P Ho_ll Go_ll Pp_ll).
seq  3 23: (BPS.rel{1} = rel{2}).
+ call (: ={glob H}); first by sim.
  inline *.
  swap{2} 1 16; swap{1} 10 -9; swap{2} [3..4] -2; swap{2} [5..6] 3.
  auto; while (   ={glob H, glob E}
               /\ j{1} = i{2}
               /\ BP.bb{1} = bb{2}
               /\ dbb{1} = ubb{2}
               /\ BP.sk{1} = BS.sk{2}).
  + by sim.
  auto.
  call (:    ={glob E, glob P, glob Ve, glob C, glob H, glob G}
          /\ ={pk, secmapD, pubmap, setH, secmap, bb0, bb1, setHcheck}(BP, BP)); first 4 by sim.
  auto; while(   i{1} = i0{2}
              /\ ={setidents, secmap, secmapD, pubmap, setD, pc_to_id}(BP, BP)).
  + by sim.
  wp; swap {2} 1 1.
  call (: ={glob H}).
  auto; call (:true).
  auto; call (:true).
  by auto.
by if{1}; auto; call {1} Pp_ll; auto.
qed.

(************************* Lemma bounding ZKFL - ZK_L by VFR advantage ******************************)

local lemma ZKFL_ZKL_VFR &m :
  `|Pr[ZKFL(E, R, P, BZK(E,P,C,Ve,A), HRO.ERO, G).main() @ &m : res]
    - Pr[ZK_L(R(E,HRO.ERO), P, BZK(E,P,C,Ve,A, HRO.ERO), G).main() @ &m : res]|
    <=
      Pr[VFR(E, BVFR(MV(E,P,Ve,C), A), R(E), HRO.ERO, G).main() @ &m : res].
proof.
have /StdOrder.RealOrder.ler_trans -> //:= ZKFL_ZKL &m.
exact: (ZKL_rel &m HRO.ERO G P HRO.ERO_o_ll Go_ll (PS_p_ll G Go_ll)).
qed.

(*************** Lemma proving that ZKFL and the original DU-MB-BPRIV game are equivalent **************)
 
local lemma G0_L_ZKFL_equiv &m :
  Pr[G0L(E, P, Ve, C, A, HRO.ERO, G).main() @ &m : res] 
  = Pr[ZKFL(E, R, P, BZK(E,P,C,Ve,A), HRO.ERO, G).main() @ &m : res]. 
proof.   
byequiv => //; proc.
inline {2} 2.
seq 15 15: (   ={glob HRO.ERO, glob A, glob C, glob P, glob Ve, glob E, glob G}
            /\ ={secmapD, setHcheck, secmapD, setD, setidents, setH, bb1, bb0, bb,
                 sethappy, vmap, pk, sk, setchecked, secmap, pubmap}(BP, BP)
            /\ BP.pk{2} = getPK BP.sk{2}).
+ conseq (:    ={glob HRO.ERO, glob A, glob C, glob P, glob Ve, glob E, glob G}
            /\ ={secmapD, setHcheck, secmapD, setD, setidents, setH, bb1, bb0, bb,
                 sethappy, vmap, pk, sk, setchecked, secmap, pubmap}(BP, BP))
         _
         (: _ ==> BP.pk = getPK BP.sk)=> //.
  + call (: true)=> //=.
    while true=> //=.
    wp; call (E_kgen_getPK_hr HRO.ERO)=> //=.
    call (: true)=> //=.
    by auto; call (: true).
  by inline *; swap {2} 1 12; sim.
inline *.
swap {2} [7..9] 7.
seq 12 13: (   ={glob HRO.ERO, glob A, glob C, glob P, glob Ve, glob E, glob G, valid}
            /\ ={setHcheck, secmapD, setD, setidents, setH, bb1, r, bb0, bb,
                 sethappy, vmap, pk, sk, setchecked, secmap, pubmap}(BP, BP)
            /\ BP.pk{2} = getPK BP.sk{2}
            /\ BPS.s{2} = (BP.pk{2}, Publish BP.bb{2}, BP.r{2})
            /\ BPS.w{2} = (BP.sk{2}, BP.bb{2})).
+ swap{1} [8..9] -7. swap{2} [7..8] -4. swap{2} [9..12] -4. swap{2} 13 -4.
  call{2} R_m_ll.
  auto; while(={glob E, glob HRO.ERO, j, BP.bb, BP.sk, dbb}).
  + by sim.
  auto; while(={glob C, glob HRO.ERO, bb, i0, e1, e2, pk}).
  + by sim.
  by auto.
if {1}.
+ rcondt {2} 4; first by auto; call (: true).
  by auto; call{2} (PS_p_ll G Go_ll).
rcondf {2} 4; first by auto; call (: true).
if {1}.
+ rcondt {2} 4; first by auto; call (: true).
  by auto; call {2} (PS_p_ll G Go_ll).
rcondf {2} 4; first by auto; call (: true).
sim.
call(: ={glob HRO.ERO, glob G, BP.bb0, BP.bb1}); first 3 by sim.
call(: ={glob HRO.ERO, glob G}); first 2 by sim.
auto; call(: ={glob G}); first by sim.
by auto.
qed. 

(************************* Lemma proving that G1L and ZKFR are equivalent *********************)

local lemma G1_L_ZKFR_equiv &m :
    Pr[G1L(E,Ve,C,A,HRO.ERO,S).main() @ &m : res]
  = Pr[ZKFR(E, R, S, BZK(E,P,C,Ve,A), HRO.ERO).main() @ &m : res].
proof.
byequiv=> //; proc.
inline {2} 2.
swap{2} 1 10.
seq 15 15: (   ={glob HRO.ERO, glob A, glob C, glob Ve, glob E, glob S}
            /\ ={setHcheck, secmapD, setD, setidents, setH, bb1, bb0, bb,
                 sethappy, vmap, pk, sk, setchecked, secmap, pubmap}(BP, BP)
            /\ BP.pk{2} = getPK BP.sk{2}).
+ conseq (:    ={glob HRO.ERO, glob A, glob C, glob Ve, glob E, glob S}
            /\ ={setHcheck, secmapD, setD, setidents, setH, bb1, bb0, bb,
                 sethappy, vmap, pk, sk, setchecked, secmap, pubmap}(BP, BP))
         _
         (: _ ==> BP.pk = getPK BP.sk)=> //=.
  + call (: true)=> //=.
    while true=> //=.
    wp; call (E_kgen_getPK_hr HRO.ERO).
    call (: true)=> //=.
    by inline *; auto; while true=> //=; auto.
  by inline {1} 12; sim.
inline *.
swap {2} [7..9] 7.
seq 12 13: (   ={glob HRO.ERO, glob A, glob C, glob Ve, glob E, glob S, valid}
            /\ ={setHcheck, secmapD, setD, setidents, setH, bb1, r, bb0, bb,
                 sethappy, vmap, pk, sk, setchecked, secmap, pubmap}(BP, BP)
            /\ BP.pk{2} = getPK BP.sk{2}
            /\ BPS.s{2} = (BP.pk, Publish BP.bb, BP.r){2}
            /\ BPS.w{2} = (BP.sk, BP.bb){2}).
+ swap{1} [8..9] -7. swap{2} [7..8] -4. swap{2} [9..12] -4. swap{2} 13 -4.
  call{2} R_m_ll.
  auto; while (={glob E, glob HRO.ERO, j, BP.bb, BP.sk, dbb}).
  + by sim.
  auto; while (={glob C, glob HRO.ERO, bb, i0, e1, e2} /\ pk{1} = pk{2}).
  + by sim.
  by auto.
if {1}.
+ rcondt {2} 4; first by auto; call (: true).
  by auto; call {2} Sp_ll.
rcondf {2} 4; first by auto; call (: true).
if {1}.
+ rcondt {2} 4; first by auto; call (: true).
  by auto; call {2} Sp_ll.
rcondf {2} 4; first by auto; call (: true).
sim.
call (: ={glob HRO.ERO, glob S, BP.bb0, BP.bb1}); first 3 by sim.
call (: ={glob HRO.ERO, glob S}); first 2 by sim.
by auto; call (: true).
qed.

(********** Lemma bounding the probability that the relation does not hold ************)
(********** in ZK_R by the probability of returning true in the VFR game.  ************)

local lemma ZKR_rel &m (H <: HOracle.Oracle { -A, -BPS, -BP, -BS, -Ve, -E, -C, -R })
                       (S <: Simulator { -E, -C, -P, -Ve, -A, -R, -BPS, -BP, -BS, -H }) :
     islossless H.o
  => islossless S.o
  => islossless S.prove
  =>     Pr[ZK_R(R(E,H), S, BZK(E,P,C,Ve,A,H)).main() @ &m : !BPS.rel]
      <= Pr[VFR(E, BVFR(MV(E,P,Ve,C), A), R(E), H, S).main() @ &m : res].
proof.
move=> Ho_ll So_ll Sp_ll.
byequiv (:    ={glob A, glob E, glob Ve, glob C, glob H, glob S, glob R}
           /\ ={setidents, setD, secmapD, setH, setHcheck, bb0, bb1}(BP, BP)
           ==> _)=> //. 
proc; call {1} (BZK_a2_ll H S Ho_ll So_ll).
seq  3  11: (BPS.rel{1} = rel{2})=> //.
+ call(: ={glob H})=> //=; first by sim.
  conseq />.
  inline {1} 2; inline {2} 7.
  swap {2} 1 17. swap {2} 1 17. swap {1} 11 -10. swap {1} 12 -9. swap {2} [2..4] -1.
  wp=> //=.
  by sim; wp; sim.
by if {1}; auto; call {1} Sp_ll.
qed. 

(************* Lemma bounding ZKFR - ZKR by advantage of VFR adversary ****************)

local lemma ZKFR_ZKR_VFR &m:
     `|  Pr[ZKFR(E, R, S, BZK(E,P,C,Ve,A), HRO.ERO).main() @ &m : res]
       - Pr[ZK_R(R(E,HRO.ERO), S, BZK(E,P,C,Ve,A, HRO.ERO)).main() @ &m : res]|
  <= Pr[VFR(E, BVFR(MV(E,P,Ve,C), A), R(E), HRO.ERO, S).main() @ &m : res].
proof. 
have /StdOrder.RealOrder.ler_trans -> //:= ZKFR_ZKR &m.
exact: (ZKR_rel &m HRO.ERO S HRO.ERO_o_ll So_ll Sp_ll).
qed.

(*************** Bounding the difference |G0_L - G1_L| by 2*VFR + |ZKL - ZKR| ***************)

local lemma G0L_G1L_zk_vfr &m : 
     `|  Pr[G0L(E,P,Ve,C,A,HRO.ERO,G).main() @ &m : res]
       - Pr[G1L(E,Ve,C,A,HRO.ERO,S).main() @ &m : res]|
  <=   Pr[VFR(E, BVFR(MV(E,P,Ve,C), A), R(E), HRO.ERO, G).main() @ &m : res]
     + Pr[VFR(E, BVFR(MV(E,P,Ve,C), A), R(E), HRO.ERO, S).main() @ &m : res]
     + `|  Pr[ZK_L(R(E,HRO.ERO), P, BZK(E,P,C,Ve,A,HRO.ERO), G).main() @ &m : res]
         - Pr[ZK_R(R(E,HRO.ERO), S, BZK(E,P,C,Ve,A,HRO.ERO)   ).main() @ &m : res]|.
proof. smt(G0_L_ZKFL_equiv G1_L_ZKFR_equiv ZKFL_ZKL_VFR ZKFR_ZKR_VFR). qed.

(****************************************************************************************************)
(************************************** End of ZK part **********************************************)
(****************************************************************************************************)

(****************************************************************************************************)
(***** Stop decrypting honest ciphertexts, use v0 value from BP.vmap instead.                   *****)
(***** Decrypt ciphertexts created by adversary as usual. Also reduce to a single board.        *****)
(***** We remove one of the boards to make it ready for a reduction to IND1CCA security.        *****)
(****************************************************************************************************)

local module G2L (E  : Scheme)
                 (Ve : Verifier)
                 (C  : ValidInd)
                 (A  : DU_MB_BPRIV_adv)
                 (H  : HOracle.Oracle)
                 (S  : Simulator)      = {
  var bb   : (label * cipher) list

  module MV = MV(E,P,Ve,C,H,S)

  module O  = {
    proc h = H.o
    proc g = S.o

    proc vote_core(id, v, sl) = {
      var p, b, spr, spo;

      (p, b, spr, spo) <@ MV.vote(BP.pk, id, id, sl, v);
      return (p, b, spr, spo);
    }

    proc vote (id : ident, v0 v1 : vote) = {
      var p, b, spr, spo;

      if (id \in BP.setH) {
        (p, b, spr, spo) <@ vote_core(id, v0, oget BP.secmap.[id]);
        BP.vmap.[id] <- (b, spr, spo, v0) :: (odflt [] BP.vmap.[id]);
        bb <- (id, b) :: bb;
      }
    }

    proc verify(id:ident) : ident fset = {
      var ok, sv;

      if (id \in BP.setidents) {
        BP.setchecked <- BP.setchecked `|` (fset1 id);
        sv <- odflt [] (BP.vmap.[id]);
        ok <@ MV.verifyvote(id,(oget (ohead sv)).`2, (oget (ohead sv)).`3,
                            BP.bb, BP.bbstar, Flabel id, tt);
        if (ok) {
          BP.sethappy <- BP.sethappy `|` (fset1 id);
        }
      }
      return BP.sethappy;
    }

    proc board() : pubBB = {
      return Publish (bb);
    } 
  }

  module A  = A(O)

  proc main() : bool = {
    var i, id, sv;
    var valid, valid';
    var dbb, j, idl, b, v, k, d;

    BP.vmap       <- empty;
    BP.pubmap     <- empty;
    BP.secmap     <- empty;
    BP.secmapD    <- empty;
    BP.setchecked <- fset0;
    BP.sethappy   <- fset0;
    BP.pc_to_id   <- empty;
    bb   <- [];

    H.init();
    S.init();

    (* setup: key generation *)
    (BP.pk, BP.sk) <@ MV.setup();

    (* registration *)
    i <- 0;
    while (i < card BP.setidents) {
      id <- nth witness (elems BP.setidents) i;
      BP.secmap.[id] <- tt;
      BP.pubmap.[id] <- Flabel id;
      BP.pc_to_id.[Flabel id] <- id;
      if (id \in BP.setD) {
        BP.secmapD.[id] <- oget BP.secmap.[id];
      }
      i <- i + 1;
    }

    (* adversary creates first bulletin board *)
    BP.bb <@ A.create_bb(BP.pk, BP.secmapD, BP.pubmap, BP.setHcheck);
 
    valid <@ MV.validboard(BP.bb, BP.pk);

    dbb     <- [];
    j      <- 0;
    while (j < size BP.bb) {
      (idl, b) <- nth witness BP.bb j;
      if ( (idl, b) \in bb) {
        (* Get the vote from the vmap element which matches the ballot *)
        sv <- odflt [] BP.vmap.[idl]; (* the list for that voter *)
        k  <- find (fun (x:cipher*cipher*cipher*vote) => x.`1 = b) sv; (* The first index where b appears *)
        v <- Some (oget (onth sv k)).`4; (* the vote at that index *) 
      } else {
        v <@ E(H).dec(BP.sk, idl, b);
      }
      dbb <- dbb ++ [(idl, v)];
      j <- j + 1;
    }
    BP.r   <$ Rho dbb;
    BP.pk  <- getPK BP.sk;

    if (!BP.setHcheck \subset fdom BP.vmap) {
      BP.d <$ {0,1};
    } elif (!valid) {
      BP.d <$ {0,1};
    } else {
      BP.pi  <@ S.prove((BP.pk, Publish BP.bb, BP.r));
        d    <@ A.initial_guess();
      BP.bbstar   <@ A.get_tally(BP.r, BP.pi);
      valid'   <@ MV.verifytally((BP.pk, Publish BP.bb, BP.bbstar.`1), BP.bbstar.`2);
      if (!valid') {
        BP.d <$ {0,1};
      } else {
        BP.d <@ A.final_guess();
        if (!(BP.setHcheck \subset BP.sethappy)) {
          BP.d <- d;
        } 
        if (!(BP.setHcheck \subset BP.setchecked)) {
          BP.d <$ {0,1};
        }
      }
    }
    return BP.d;
  }
}.

local lemma odflt_notNone['a] (x1 x2:'a) (z: 'a option):
   z <> None => odflt x1 z = odflt x2 z.
proof. by case: z. qed.

(******************** Prove that G1L and G2L are equivalent *******************)
local lemma G1L_G2L_equiv &m :
     BP.setidents{m} = BP.setH{m} `|` BP.setD{m}
  =>   Pr[G1L(E,Ve,C,A,HRO.ERO,S).main() @ &m : res]
     = Pr[G2L(E,Ve,C,A,HRO.ERO,S).main() @ &m : res].
proof.   
move=> H_IHD.
byequiv=> //=; proc.

(************************************************************************************************)
(* First we prove that everything is more or less equal before the adversary creates the board  *)
(************************************************************************************************)
seq 15 14: (   ={glob A, glob C, glob Ve, glob S, glob E, glob HRO.ERO}
            /\ ={setHcheck, secmapD, setD, setidents, setH, vmap,
                 sk, pk, bb, pubmap, sethappy, setchecked}(BP, BP)
            /\ BP.setidents{2} = BP.setH{2} `|` BP.setD{2}
            /\ BP.pk{1} = getPK BP.sk{1}
            /\ (rem_ids BP.bb0{1} = G2L.bb{2}) 
            /\ (forall idl b,
                     (idl, b) \in G2L.bb{2}
                  =>   dec_cipher BP.sk idl b HRO.ERO.m
                     = Some (oget (onth (odflt [] BP.vmap.[idl]) 
                              (find (fun (x : _ * _ * _ * _)  => x.`1 = b)
                                    (odflt [] BP.vmap.[idl])))).`4){2}
            /\ (forall id id', BP.pubmap.[id] = Some id' => id =id'){2}
            /\ (forall id, id \in BP.setidents => id \in BP.pubmap){2}).
+ call (:   ={glob C, glob Ve, glob S, glob E, glob HRO.ERO}
         /\ ={setHcheck, secmapD, setD, setidents, setH, vmap,
              sk, pk, pubmap, sethappy, setchecked}(BP, BP)
         /\ BP.pk{1} = getPK BP.sk{1}
         /\ BP.setidents{2} = BP.setH{2} `|` BP.setD{2}
         /\ (rem_ids BP.bb0{1} = G2L.bb{2}) 
         /\ (forall idl b,
                  (idl, b) \in G2L.bb{2}
               =>   dec_cipher BP.sk idl b HRO.ERO.m
                  = Some (oget (onth (odflt [] BP.vmap.[idl]) 
                           (find (fun (x : _ * _ * _ * _)  => x.`1 = b)
                                 (odflt [] BP.vmap.[idl])))).`4){2}
         /\ (forall id id', BP.pubmap.[id] = Some id' => id = id'){2}
         /\ (forall id, id \in BP.setidents => id \in BP.pubmap){2}).
  + proc; if=> //.
    inline {1} 2; wp=> //=.
    conseq (:    ={glob E}
              /\ b0{1} = b{2}
              /\ s0_pre{1} = spr{2}
              /\ s0_post{1} = spo{2}
              /\ (dec_cipher BP.sk p0 b0 HRO.ERO.m = Some v0){1}
              /\ p0{1} = oget BP.pubmap.[id]{2})=> />.
    + move=> &1 &2 ih pubmapI setidents_sub_pubmap id_is_hon b spo spr.
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
    wp; call (:    ={glob HRO.ERO, glob E, arg}
               /\ arg{1} = (getPK sk1, pc1, v1)
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
  conseq />.
  while (   ={i, BP.setidents, BP.secmap, BP.pubmap, BP.secmapD, BP.setD, BP.pc_to_id}
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
  call (E_kgen_getPK HRO.ERO).
  call(: true).
  while (={w, HRO.ERO.m}); first by sim.
  auto=> /> [] pk sk />.
  split.
  + smt(emptyE fcard_ge0).
  move=> pmap i /lezNgt card_le_i pubmapI setidents_sub_pubmap ge0_i lei_card id ^ id_is_id.
  rewrite memE=> /(nth_index witness) <-.
  apply: setidents_sub_pubmap; rewrite index_ge0 /=.
  have /> {i card_le_i lei_card}: i = card BP.setidents{m}.
  + by rewrite eqz_leq lei_card card_le_i.
  by move: id_is_id; rewrite memE -index_mem /card.
(************************************************************************************************)
      (* We show that everything is equivalent upto the proof produced *)
(************************************************************************************************)
seq  6  6: (   ={glob A, glob C, glob Ve, glob S, glob E, glob HRO.ERO}
            /\ ={setHcheck, secmapD, setD, setidents, setH, vmap, sk, pk, bb, sethappy, setchecked, r, pubmap}(BP, BP)
            /\ ={valid}
            /\ BP.setidents{2} = BP.setH{2} `|` BP.setD{2}
            /\ rem_ids BP.bb0{1} = G2L.bb{2} 
            /\ (forall idl b, 
                   (idl, b) \in G2L.bb =>  
                       Some (oget (onth (odflt [] BP.vmap.[idl]) 
                                    (find (fun (x : cipher*cipher*cipher*vote)  => x.`1 =b)  
                                          (odflt [] BP.vmap.[idl])))).`4
                       = dec_cipher BP.sk idl b HRO.ERO.m){2}
            /\ (forall id id', BP.pubmap.[id] = Some id' => id = id'){2}
            /\ (forall id, id \in BP.setidents => id \in BP.pubmap){2}); last first.
+ if=> //; first by auto. 
  if=> //; first by auto.  

  (* up to valid is fine *)
  seq  4  4: (   ={glob A, glob C, glob Ve, glob S, glob E, glob HRO.ERO}
              /\ ={setHcheck, pi, secmapD, setD, setidents, setH, vmap, sk,
                   pubmap, pk, bb, sethappy, setchecked, r, pi}(BP, BP)
             /\ ={valid, valid', d}
             /\ BP.setidents{2} = BP.setH{2} `|` BP.setD{2}
             /\ rem_ids BP.bb0{1} = G2L.bb{2} 
             /\ (forall idl b, 
                  (idl, b) \in G2L.bb{2} =>  
                     Some (oget (onth (odflt [] BP.vmap{2}.[idl]) 
                                      (find (fun (x : cipher*cipher*cipher*vote)  => x.`1 =b)  
                                            (odflt [] BP.vmap{2}.[idl])))).`4
                     = dec_cipher BP.sk{2} idl b HRO.ERO.m{2})
             /\ (forall id id', BP.pubmap{2}.[id] = Some id' => id =id')
             /\ (forall id, id \in BP.setidents{2} => id \in BP.pubmap{2})).
  + inline *; wp; call (: ={glob S}); first by sim.
    wp; call (: ={glob S, glob HRO.ERO} /\ rem_ids BP.bb0{1} = G2L.bb{2}).
    + by proc; inline *; auto.
    + by proc; auto.
    + by conseq So_ll2.
    call (: ={glob HRO.ERO, glob S}); first 2 by sim.
    by call (: true); auto.
  if=> //; first by auto.
  sim.
  call (:    ={glob HRO.ERO, glob S}
          /\ ={setidents, setHcheck, setchecked, sethappy, bb, vmap, pubmap}(BP, BP)
          /\ BP.setidents{2} = BP.setH{2} `|` BP.setD{2}
          /\ (forall id id', BP.pubmap{1}.[id] = Some id' => id = id')
          /\ (forall id, id \in BP.setidents{2} => id \in BP.pubmap{1})).
  + proc; if=> //; inline *; auto=> /> &2 pubmapI setidents_sub_pubmap id_is_id.
    have:= setidents_sub_pubmap _ id_is_id; rewrite domE.
    by case: {-1}(BP.pubmap.[id]{2}) (eq_refl BP.pubmap.[id]{2})=> //= id' ^ /pubmapI />.
  + by proc; inline *; auto.
  + by conseq So_ll2.
  by auto.
auto.
while (   ={j, BP.bb, glob HRO.ERO, glob E, BP.sk, dbb}
       /\ (forall (idl : ident) (b : cipher),
              (idl, b) \in G2L.bb{2}  =>
                Some (oget (onth (odflt []  BP.vmap{2}.[idl])
                     (find (fun (x : _ * _ * _ * _)  => x.`1 = b)
                           (odflt [] BP.vmap{2}.[idl])))).`4
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
 

(*********** We start with a game where we just unpack some procs in the security definition ********)

local module G0R' (E  : Scheme)
                  (P  : Prover)
                  (Ve : Verifier)
                  (C  : ValidInd)
                  (A  : DU_MB_BPRIV_adv)
                  (H  : HOracle.Oracle)
                  (G  : GOracle.Oracle)
                  (S  : Simulator) = {
  module O  = DU_MB_BPRIV_oracles(MV(E, P, Ve, C), H, S, Right)
  module A  = A(O)
  module MV = MV(E,P,Ve,C,H,S)
 
  proc main() : bool = {
    var i, id;
    var valid, valid';
    var j, dbb, idl, b, v, d;
    
    BP.vmap    <- empty;
    BP.pubmap  <- empty;
    BP.secmap  <- empty;
    BP.secmapD <- empty;
    (* BP.pc_to_id<- empty; *)
    BP.bb0     <- [];
    BP.bb1     <- [];
    BP.setchecked <- fset0;
    BP.sethappy   <- fset0;

    H.init();
    G.init();
    S.init();

    (* setup: key generation *)
    (BP.pk, BP.sk) <@ MV.setup();

    (* registration *)
    i <- 0;
    while (i < card BP.setidents) {
      id <- nth witness (elems BP.setidents) i;
      BP.secmap.[id] <- tt;
      BP.pubmap.[id] <- Flabel id;
      (* BP.pc_to_id.[Flabel id] <- id;*)
      if (id \in BP.setD) {
        BP.secmapD.[id] <- oget BP.secmap.[id];
      }
    i <- i + 1;
    }

    (* adversary creates first bulletin board *)
    BP.bb <@ A.create_bb(BP.pk, BP.secmapD, BP.pubmap, BP.setHcheck);
    
    if (!BP.setHcheck \subset fdom BP.vmap) {
      BP.d <$ {0,1};
    } else {
      valid <@ MV.validboard(BP.bb, BP.pk);
      if (!valid) {
        BP.d <$ {0,1}; 
      } else {
            BP.bb'    <@ Recover'.rec(rem_ids BP.bb0, rem_ids BP.bb1, BP.bb);
             dbb      <- [];
              j       <- 0;
         while (j < size BP.bb') {
          (idl, b) <- nth witness BP.bb' j;
             v     <@ E(H).dec(BP.sk, idl, b);
           dbb     <- dbb ++ [(idl, v)];
            j      <- j + 1;
         }

         BP.r      <$ Rho dbb;
         BP.pk     <- getPK BP.sk;
         BP.pi     <@ P(G).prove((BP.pk, Publish BP.bb', BP.r), (BP.sk, BP.bb'));
         BP.pi'    <@ S.prove(BP.pk, Publish BP.bb, BP.r);
            d      <@ A.initial_guess();
         BP.bbstar <@ A.get_tally(BP.r, BP.pi');
          valid'   <@ MV.verifytally((BP.pk, Publish BP.bb, BP.bbstar.`1), BP.bbstar.`2);
        if (!valid') {
          BP.d <$ {0,1};
        } else {
         BP.d <@ A.final_guess();
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


(******** Lemma proving that the above game is equivalent to security definition *******)

local lemma DU_MB_BPRIV_R_G0'_R_equiv &m (H <: HOracle.Oracle { -E, -BP, -G, -A, -C, -Ve, -S, -R, -P }) : 
  Pr[DU_MB_BPRIV_R(MV(E, P, Ve, C), A, H, G, S, Recover').main() @ &m : res]
  = Pr[G0R'(E, P, Ve, C, A, H, G, S).main() @ &m : res].
proof.
  byequiv =>/>; proc.
  inline*; sim.
  while( ={BP.secmap, BP.pubmap, BP.setD, BP.secmapD, i, BP.setidents});
    first by auto.
  wp; call(: true); call(: true); call(: true); call(: true).  
  by auto. 
qed.

(********* We now move the tally and the valid check outside of the if-else statements **********)

local module G0R (E  : Scheme)
                 (P  : Prover)
                 (Ve : Verifier)
                 (C  : ValidInd)
                 (A  : DU_MB_BPRIV_adv)
                 (H  : HOracle.Oracle)
                 (S  : Simulator) = {
  module O  = DU_MB_BPRIV_oracles(MV(E, P, Ve, C), H, S, Right)
  module A  = A(O)
  module MV = MV(E,P,Ve,C,H,S)
 
  proc main() : bool = {
    var i, id;
    var valid, valid';
    var j, dbb, idl, b, v, d;
    
    BP.vmap    <- empty;
    BP.pubmap  <- empty;
    BP.secmap  <- empty;
    BP.secmapD <- empty;
    BP.bb0     <- [];
    BP.bb1     <- [];
    BP.setchecked <- fset0;
    BP.sethappy   <- fset0;

    H.init();
    S.init();

    (* setup: key generation *)
    (BP.pk, BP.sk) <@ MV.setup();

    (* registration *)
    i <- 0;
    while (i < card BP.setidents) {
      id <- nth witness (elems BP.setidents) i;
      BP.secmap.[id] <- tt;
      BP.pubmap.[id] <- id;
      if (id \in BP.setD) {
        BP.secmapD.[id] <- oget BP.secmap.[id];
      }
    i <- i + 1;
    }

   (* adversary creates first bulletin board *)
    BP.bb <@ A.create_bb(BP.pk, BP.secmapD, BP.pubmap, BP.setHcheck);

    valid <@ MV.validboard(BP.bb, BP.pk);

     BP.bb'    <@ Recover'.rec(rem_ids BP.bb0, rem_ids BP.bb1, BP.bb);
      dbb      <- [];
       j       <- 0;
      while (j < size BP.bb') {
        (idl, b) <- nth witness BP.bb' j;
           v     <@ E(H).dec(BP.sk, idl, b);
         dbb     <- dbb ++ [(idl, v)];
          j      <- j + 1;
      }

       BP.r      <$ Rho dbb;
       BP.pk     <- getPK BP.sk;
    
    if (!BP.setHcheck \subset fdom BP.vmap) {
      BP.d <$ {0,1};
    } else {
      if (!valid) {
        BP.d <$ {0,1}; 
      } else {
         BP.pi'    <@ S.prove(BP.pk, Publish BP.bb, BP.r);
            d      <@ A.initial_guess();
         BP.bbstar <@ A.get_tally(BP.r, BP.pi');
          valid'   <@ MV.verifytally((BP.pk, Publish BP.bb, BP.bbstar.`1), BP.bbstar.`2);
        if (!valid') {
          BP.d <$ {0,1};
        } else {
         BP.d <@ A.final_guess();
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

(**** Lemma proving that G0R' and G0R are equivalent ****)
local lemma G0R'_G0R_equiv &m : 
    Pr[G0R'(E,P,Ve,C,A,HRO.ERO,G,S).main() @ &m : res] 
  = Pr[G0R(E,P,Ve,C,A,HRO.ERO,S).main() @ &m : res]. 
proof. 
byequiv (:    ={glob A, glob C, glob Ve, glob S, glob E, glob P}
           /\ ={setHcheck, secmapD, setD, setidents, d, setH, bb'}(BP, BP) ==> _)=> //.
proc.
seq 15 14: (   ={glob HRO.ERO, glob A, glob C, glob Ve, glob E, glob S, glob P}
            /\ ={pk, sk, bb, bb', vmap, setchecked, setHcheck, sethappy, d,
                 bb0, bb1, pubmap, secmap, setH, secmap, secmapD, setidents}(BP, BP)).
+ sim.
  while (={i, BP.setidents, BP.secmap, BP.pubmap, BP.setD, BP.secmapD}); first by auto.
  inline *.
  wp; call (E_kgen_getPK HRO.ERO).
  call (: true).
  call {1} Gi_ll.
  while (={w, HRO.ERO.m}); first by sim.
  by auto.
if {1}.
(* First case: !setHcheck \subset fdom BP.vmap *)
(* In other words: some of the voters we expect will verify don't vote *)
+ inline *.
  rcondt{2} 20.
  + auto.
    while (0 <= j <= size BP.bb'); first by auto; call (: true); auto=> /#.
    wp; while (0 <= i1 <= size bb2); first by auto=> /#.
    wp; while (0 <= i0 <= size bb).
    + sp; if=> //; last by auto=> /#.
      by auto; call (: true); auto=> /#.
    by auto=> />; smt(size_ge0).
  rnd; wp; rnd {2}.
  while {2} (0 <= j{2} <= size BP.bb'{2}) (size BP.bb'{2} - j{2}).
  + by auto; call (E_dec_ll HRO.ERO HRO.ERO_o_ll); auto=> /#.
  wp; while {2} (0 <= i1{2} <= size bb2{2}) (size bb2{2} - i1{2}).
  + by auto=> /#.
  wp; while {2} (0 <= i0{2} <= size bb{2}) (size bb{2} - i0{2}).
  + auto; sp; if=> //; last by auto=> /#.
    by auto; call (C_vi_ll HRO.ERO HRO.ERO_o_ll); auto=> /#.
  by auto=> /> &0; smt(size_ge0 Rho_weight).
(* Second case: all voters we expect to check vote *)
inline *.
seq  7  7: (   ={glob HRO.ERO, glob A, glob C, glob Ve, glob E, glob S, glob P, valid}
            /\ ={pk, sk, bb, vmap, pubmap, setchecked, setHcheck, sethappy, d,
                 bb0, bb1, setH, secmap, bb', setidents}(BP, BP)
            /\ BP.setHcheck{1} \subset fdom BP.vmap{1}).
+ auto; while (={i0, bb, e1, e2, pk, glob HRO.ERO, glob C}); first by sim.
  by auto.
rcondf{2} 13.
+ auto; while (0 <= j <= size BP.bb').
  + by wp; call (: true); auto=> /#.
  wp; while (0 <= i1 <= size bb2); first by auto=> /#.
  by auto; smt(size_ge0).
(* Next branch: is the BP.bb valid? *)
if {1}.
(* First the case where BP.bb is invalid *)
+ rcondt{2} 13.
  + auto; while (0 <= j <= size BP.bb').
    + by wp; call (: true); auto=> /#.
    wp; while (0 <= i1 <= size bb2); first by auto=> /#.
    by auto; smt(size_ge0).
  rnd.
  auto; while {2} (0 <= j{2} <= size BP.bb'{2}) (size BP.bb'{2} - j{2}).
  + by auto; call (E_dec_ll HRO.ERO HRO.ERO_o_ll); auto=> /#.
  wp; while{2} (0 <= i1{2} <= size bb2{2}) (size bb2{2} - i1{2}).
  + by auto=> /#.
  by auto; smt(size_ge0 Rho_weight).
(* Then the case where BP.bb is valid *)
rcondf{2} 13.
+ auto; while (0 <= j <= size BP.bb'); first by wp; call (: true); auto=> /#.
  auto; while (0 <= i1 <= size bb2); first by auto=> /#.
  by auto; smt(size_ge0).
seq 20 19 : (   ={HRO.ERO.m, glob A, glob C, glob Ve, glob E, glob S, d, valid, valid'}
             /\ ={pk, setidents, sk, bb, vmap, setchecked, setHcheck, bb, pubmap, secmap,
                  sethappy, d, bb0, bb1, setH, secmap, bbstar, bb'}(BP, BP)
             /\ (BP.setHcheck \subset fdom BP.vmap){1}
             /\ valid{1}); last by sim.
wp; call (: ={glob S}); first by sim. 
wp; call (: ={BP.bb0, BP.bb1, HRO.ERO.m, glob S}); first 3 by sim.
call (: ={glob S, HRO.ERO.m}); first 2 by sim.
call (: true).
call {1} (PS_p_ll G Go_ll).
auto; while (={glob E, j,  HRO.ERO.m, dbb, BP.sk, BP.bb', BP.bb0, BP.bb1}); first by sim.
auto; while (={i1, bb0, bb1, bb2, BP.setH, bb', BP.secmap}); first by sim.
by auto.
qed. 

(******* We now stop decrypting honest ciphertexts and use plain votes from BP.vmap instead. *********)
(******* Ballots added by the adversary is decrypted as usual.                               *********)

local module G1R (E  : Scheme)
                 (P  : Prover)
                 (Ve : Verifier)
                 (C  : ValidInd)
                 (A  : DU_MB_BPRIV_adv)
                 (H  : HOracle.Oracle)
                 (S  : Simulator) = {

  module MV = MV(E,P,Ve,C, H, S)

  module O  = {
    proc h = H.o
    proc g = S.o

    proc vote_core(id, v, sl) = {
      var p, b, spr, spo;
      
      (p, b, spr, spo) <@ MV.vote(BP.pk, id, id, sl, v);

      return (p, b, spr, spo);
    }

    proc vote (id : ident, v0 v1 : vote) = {
      var p0, b0, s0pr, s0po;
      var p1, b1, s1pr, s1po;

      if ((id \in BP.setH)) {
        (s0pr, s0po, b0, p0)  <@ vote_core(id, v0, oget BP.secmap.[id]);
        (s1pr, s1po, b1, p1)  <@ vote_core(id, v1, oget BP.secmap.[id]);

        BP.vmap.[id] <- (b0, b1, b0, v0) ::  (odflt [] BP.vmap.[id]);
        BP.bb0 <- (id, id, b0) :: BP.bb0;
        BP.bb1 <- (id, id, b1) :: BP.bb1;
      }
    }
  

    proc verify(id:ident) : ident fset = {
      var ok, sv; 

      if (id \in BP.setidents){
        BP.setchecked <- BP.setchecked `|` (fset1 id);
        sv <- odflt [] (BP.vmap.[id]);
        ok <@ MV.verifyvote(id,(oget (ohead sv)).`2, (oget (ohead sv)).`3, 
                        BP.bb, BP.bbstar, id, tt); 
        if (ok) {
          BP.sethappy <- BP.sethappy `|` (fset1 id);
        }
      }
      return BP.sethappy;
    }

    proc board() : pubBB = {
      return Publish(rem_ids BP.bb1);
    }
  }


  module A  = A(O)
 
  proc main() : bool = {
    var i, id;
    var valid, valid', sv, k;
    var j, dbb, idl, b, v, d;
    
    BP.vmap    <- empty;
    BP.pubmap  <- empty;
    BP.secmap  <- empty;
    BP.secmapD <- empty;
    BP.bb0     <- [];
    BP.bb1     <- [];
    BP.setchecked <- fset0;
    BP.sethappy   <- fset0;

    H.init();
    S.init();

    (* setup: key generation *)
    (BP.pk, BP.sk) <@ MV.setup();

    (* registration *)
    i <- 0;
    while (i < card BP.setidents) {
      id <- nth witness (elems BP.setidents) i;
      BP.secmap.[id] <- tt;
      BP.pubmap.[id] <- id;
      if (id \in BP.setD) {
        BP.secmapD.[id] <- oget BP.secmap.[id];
      }
    i <- i + 1;
    }

    (* adversary creates first bulletin board *)
    BP.bb <@ A.create_bb(BP.pk, BP.secmapD, BP.pubmap, BP.setHcheck);

    valid <@ MV.validboard(BP.bb, BP.pk);

    BP.bb'    <@ Recover'.rec(rem_ids BP.bb0, rem_ids BP.bb1, BP.bb);
     dbb      <- [];
      j       <- 0;
     while (j < size BP.bb') {
      (idl, b) <- nth witness BP.bb' j;
       if ( (idl, b) \in rem_ids BP.bb0) {
          (* Get the vote from the vmap element which matches the ballot *)
          sv <- odflt [] BP.vmap.[idl]; (* the list for that voter *)
          k <- find (fun (x:cipher*cipher*cipher*vote) => x.`1 = b) sv; (* The first index where b appears *)
          v <- Some (oget (onth sv k)).`4; (* the vote at that index *) 
       } else {
           v <@ E(H).dec(BP.sk, idl, b);
       }
       dbb   <- dbb ++ [(idl, v)];
        j    <- j + 1;
     }
     
      BP.r      <$ Rho dbb;
      BP.pk     <- getPK BP.sk;
    
    if (!(BP.setHcheck \subset fdom BP.vmap)) {
      BP.d <$ {0,1};
    } else {
      if (!valid) {
        BP.d <$ {0,1}; 
      } else {
         BP.pi'    <@ S.prove(BP.pk, Publish BP.bb, BP.r);
           d       <@ A.initial_guess();
         BP.bbstar <@ A.get_tally(BP.r, BP.pi');
          valid'   <@ MV.verifytally((BP.pk, Publish BP.bb, BP.bbstar.`1), BP.bbstar.`2);
        if (!valid') {
          BP.d <$ {0,1};
        } else {
         BP.d <@ A.final_guess();
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

local lemma odflt_is_some['a] (x1 x2:'a) (z: 'a option):
   is_some z => odflt x1 z = odflt x2 z.
proof. by case: z. qed.

(************ Prove that G0R and G1R are equivalent **********)
local lemma G0R_G1R_equiv &m : 
  BP.setidents{m} = BP.setH{m} `|` BP.setD{m}
  =>   Pr[G0R(E,P,Ve,C,A,HRO.ERO,S).main() @ &m : res]
     = Pr[G1R(E,P,Ve,C,A,HRO.ERO,S).main() @ &m : res].
proof.
move => H_IHD.
byequiv=> />; proc.
(************************************************************************************************)
(* First we prove that everything is more or less equal before the adversary creates the board  *)
(************************************************************************************************)
seq 14 14: (   ={glob C, glob Ve, glob S, glob E, glob A, glob HRO.ERO}
            /\ ={setHcheck, secmapD, setD, setidents, setH, sk, pk, bb,
                 sethappy, setchecked, bb0, bb1, pubmap}(BP, BP)
             /\ fdom BP.vmap{1} = fdom BP.vmap{2}
             /\ (forall idl j,
                     rem_fst4 (nth witness (odflt [] BP.vmap{1}.[idl]) j)
                   = rem_fst4 (nth witness (odflt [] BP.vmap{2}.[idl]) j))
             /\ (forall idl b,
                      (idl, b) \in rem_ids BP.bb0{2}
                   => Some (nth witness (odflt [] BP.vmap{2}.[idl])
                                (find (fun (x : _ * _ * _ * _)=> x.`1 = b)
                                        (odflt [] BP.vmap{2}.[idl]))).`4
                        = dec_cipher BP.sk{2} idl b HRO.ERO.m{2})
            /\ (forall id id', BP.pubmap{2}.[id] = Some id' => id = id')
            /\ (forall id, id \in BP.setidents{2} => id \in BP.pubmap{2})).
+ call (:    ={ glob HRO.ERO,  glob S, glob C, glob E}
          /\ ={pk, secmapD, pubmap, sk, pk, secmap, setH, setidents, bb0, bb1}(BP, BP)
          /\ fdom BP.vmap{1} = fdom BP.vmap{2}
          /\ (forall idl j,
                  rem_fst4 (nth witness (odflt [] BP.vmap{1}.[idl]) j)
                = rem_fst4 (nth witness (odflt [] BP.vmap{2}.[idl]) j))
          /\ BP.pk{1} = getPK BP.sk{1}
          /\ (forall idl b,
                   (idl, b) \in rem_ids BP.bb0{2}
                => Some (nth witness (odflt [] BP.vmap{2}.[idl])
                             (find (fun (x : _ * _ * _ * _)=> x.`1 = b)
                                   (odflt [] BP.vmap{2}.[idl]))).`4
                  = dec_cipher BP.sk{2} idl b HRO.ERO.m{2})
          /\ (forall idl b, (idl, b) \in rem_ids BP.bb0{2} => is_some BP.vmap{2}.[idl])
          /\ (forall id id', BP.pubmap{2}.[id] = Some id' => id = id')
          /\ (forall id, id \in BP.setH{2} => id \in BP.pubmap{2})).
  + proc; if=> //.
    inline *; wp.
    seq 13  9: (   ={id, v0, v1,  HRO.ERO.m, glob S, glob C, glob E}
                /\ ={pk, secmapD, pubmap, secmap, setH, setidents, sk, bb0, bb1}(BP, BP)
                /\ fdom BP.vmap{1} = fdom BP.vmap{2}
                /\ (forall idl j,
                        rem_fst4 (nth witness (odflt [] BP.vmap{1}.[idl]) j)
                      = rem_fst4 (nth witness (odflt [] BP.vmap{2}.[idl]) j))
                 /\ BP.pk{1} = getPK BP.sk{1}
                 /\ (forall idl b,  
                          (idl, b) \in rem_ids BP.bb0{2}
                       =>   Some (nth witness (odflt [] BP.vmap{2}.[idl]) 
                                      (find (fun (x : _ * _ * _ * _)  => x.`1 = b)
                                            (odflt [] BP.vmap{2}.[idl]))).`4
                          = dec_cipher BP.sk{2} idl b HRO.ERO.m{2})
                 /\ (forall idl b, (idl, b) \in rem_ids BP.bb0{2} => is_some BP.vmap{2}.[idl])
                 /\ (forall id id', BP.pubmap{2}.[id] = Some id' => id = id')
                 /\ (forall id, id \in BP.setH{2} => id \in BP.pubmap{2})
                 /\ BP.pk{1} = getPK BP.sk{1}
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
    + inline *; wp; sp.  
      exists * BP.sk{1}, BP.pk{1}, v{1}, id1{1}; elim *=> sk1 pk1 v1 id1.
      move: (orbN (pk1 = getPK sk1))=> /= [] />.
      + auto; call (Eenc_dec sk1 id1 v1); auto=> />.
        move=> &1 &2 vmap_domeq rm_fset4_eq enc_correct is_some pubmap_id id_inpubmap.
        move=> /id_inpubmap /domE; move: (pubmap_id id1).
        by case: (BP.pubmap{2}.[id1])=> /#.
      move=> h; conseq (: !(BP.pk{1} = getPK BP.sk{1}))=> //.
      call {1} (E_enc_ll HRO.ERO HRO.ERO_o_ll).
      call {2} (E_enc_ll HRO.ERO HRO.ERO_o_ll).
      by auto.
    call (: ={glob HRO.ERO, BP.pk, glob S}); first by sim. 
    auto=> /> &1 &2 fdom_eq rm_fst4_eq enc_correct inv_cast pubmap_id honest_exists.
    move=> dec_cipher_eq_v0 ^ id_is_honest /honest_exists /domE; move: (pubmap_id id{2}).
    case: {-1}(BP.pubmap.[id]{2}) (eq_refl BP.pubmap.[id]{2})=> /> l2 pubmap_id2.
    move=> /(_ l2 _) // <<- //=.
    move=> r; rewrite !fdom_set fdom_eq //=.
    split=> [idl j|].
    + rewrite !get_setE; case: (idl = id{2})=> /> => [|_].
      + by case: (j = 0)=> /> _; exact: rm_fst4_eq.
      exact: rm_fst4_eq.
    split=> idl b5.
    + rewrite !get_setE; case: (idl = id{2})=> />.
      + case: (b3{2} = b5)=> />.
        rewrite /rem_ids map_cons -/(rem_ids BP.bb0{2}) /rem_id /= eq_sym=> -> /=.
        have -> /=: find (fun (x : _ * _ * _ * _)=> x.`1 = b5) (odflt [] BP.vmap.[id]{2}) + 1 <> 0.
        + smt(find_ge0).
        exact: enc_correct.
      rewrite /rem_ids map_cons -/(rem_ids BP.bb0{2}) /rem_id /=.
      by rewrite eq_sym=> -> /=; exact: enc_correct.
    rewrite get_setE /rem_ids map_cons -/(rem_ids BP.bb0{2}) /rem_id /=.
    by case: (idl = id{2})=> /> _; exact: inv_cast.
  + by proc; inline *; auto.
  + by proc; auto.
  + by conseq So_ll2. 
  (* Registration procedures are equivalent *)   
  while (   ={i, BP.setidents, BP.secmap, BP.pubmap, BP.secmapD, BP.setD}
         /\ (forall id id', BP.pubmap{2}.[id] = Some id' => id =id')
         /\ (forall j, 0<= j < i{2} => 
                (nth witness (elems BP.setidents{2}) j) \in BP.pubmap{2})
         /\ 0 <= i{2} <= card BP.setidents{2}).
  + auto=> /> &2 pubmap_id dom_pubmapP ge0_i _ i_lt_card_idents.
    case: (nth witness (elems BP.setidents{2}) i{2} \in BP.setD{2})=> /> _.
    + do !split=> [id0 id'|j|/#|/#]; rewrite ?domE get_setE.
      + by case: (id0 = nth witness (elems BP.setidents{2}) i{2})=> /#.
      by case: (j = i{2})=> /> /#.
    do !split=> [id0 id'|j|/#|/#]; rewrite ?domE get_setE.
    + by case: (id0 = nth witness (elems BP.setidents{2}) i{2})=> /#.
    by case: (j = i{2})=> /> /#.
  (* Initializing the different sets and maps and random oracles *)
  inline *; auto.
  call (E_kgen_getPK HRO.ERO).
  call (: true).
  while (={w, HRO.ERO.m, glob S}); first by sim.  
  auto=> /> Hm [] /> sk; split.
  + smt(emptyE fcard_ge0).
  move=> pm i h + + _ h'; have {h h'} ->>: i = card BP.setidents{m} by smt().
  move=> pubmap_id in_pm.
  split.
  + move=> id0 id0_honest; move: H_IHD=> /(congr1 (fun (X : ident fset)=> id0 \in X)) /=.
    rewrite in_fsetU id0_honest eqT=> id0_valid.
    move: (nth_index witness id0 (elems BP.setidents{m}) _).
    + by rewrite -memE.
    move=> <-; apply: in_pm; split=> [|_].
    + exact: index_ge0.
    by rewrite /card index_mem -memE.
  move=> _ _ _ _ _ _ _ _ _ _ id0 id0_valid.
  move: (nth_index witness id0 (elems BP.setidents{m}) _).
  + by rewrite -memE.
  move=> <-; apply@ in_pm; split=> [|_].
  + exact: index_ge0.
  by rewrite /card index_mem -memE.
(************************************************************************************************)
(**************** We show that everything is equivalent upto the proof produced *****************)
(************************************************************************************************)
seq  7  7: (   ={glob A, glob C, glob Ve, glob S, glob E, glob HRO.ERO, valid, dbb}
            /\ ={setHcheck, secmapD, setD, setidents, setH, sk, pk, bb, bb',
                 sethappy, setchecked, bb0, bb1, pubmap, r}(BP, BP)
            /\ fdom BP.vmap{1} = fdom BP.vmap{2}
            /\ (forall idl j, 
                     rem_fst4 (nth witness (odflt [] BP.vmap{1}.[idl]) j)
                   = rem_fst4 (nth witness (odflt [] BP.vmap{2}.[idl]) j))
            /\ (forall (idl : ident) (b : cipher),  (idl, b) \in rem_ids BP.bb0{2} =>  
                     Some (nth witness (odflt [] BP.vmap{2}.[idl]) 
                               (find (fun (x : _ * _ * _ * _)=> x.`1 = b)  
                                     (odflt [] BP.vmap{2}.[idl]))).`4
                   = dec_cipher BP.sk{2} idl b HRO.ERO.m{2})
            /\ (forall id id', BP.pubmap{2}.[id] = Some id' => id = id')
            /\ (forall id, id \in BP.setidents{2} => id \in BP.pubmap{2})); last first. 
+ if=> //; auto=> [/#|].
  if=> //; auto.
  seq  4  4: (   ={glob A, glob C, glob Ve, glob S, glob E, glob HRO.ERO, valid, valid', d}
              /\ ={setHcheck, secmapD, setD, setidents, setH, sk, pubmap, pk, bb, bb',
                   sethappy, setchecked, r, pi'}(BP, BP)
              /\ fdom BP.vmap{1} = fdom BP.vmap{2}
              /\ (forall idl j, 
                      rem_fst4 (nth witness (odflt [] BP.vmap{1}.[idl]) j)
                    = rem_fst4 (nth witness (odflt [] BP.vmap{2}.[idl]) j))
              /\ (forall (idl : ident) (b : cipher),  (idl, b) \in rem_ids BP.bb0{2} =>  
                      Some (nth witness (odflt [] BP.vmap{2}.[idl]) 
                                (find (fun (x : _ * _ * _ * _)=> x.`1 = b)  
                                      (odflt [] BP.vmap{2}.[idl]))).`4
                    = dec_cipher BP.sk{2} idl b HRO.ERO.m{2})
              /\ (forall id id', BP.pubmap{2}.[id] = Some id' => id = id')
              /\ (forall id, id \in BP.setidents{2} => id \in BP.pubmap{2})).
  + inline*; auto; call (: ={glob S, glob HRO.ERO, BP.bb1}); first by sim.
    auto; call (: ={BP.r, BP.pi', BP.bb1, glob HRO.ERO, glob S, glob E}).
    + by proc; inline *; auto.
    + by proc.
    + by sim.
    call (: ={glob HRO.ERO, glob S}); first 2 by sim.
    call (: true).
    by auto.
  if=> //; auto.
  sim.
  call (:    ={glob HRO.ERO, glob S}
          /\ ={setidents, setHcheck, setchecked, sethappy, bb, pubmap}(BP, BP)
          /\ fdom BP.vmap{1} = fdom BP.vmap{2}
          /\ (forall idl0 j0,
                  rem_fst4 (nth witness (odflt [] BP.vmap{1}.[idl0]) j0)
                = rem_fst4 (nth witness (odflt [] BP.vmap{2}.[idl0]) j0))
          /\ (forall id id', BP.pubmap{1}.[id] = Some id' => id = id')
          /\ (forall id, id \in BP.setidents{2} => id \in BP.pubmap{1})).
  + proc; inline *; if =>//. 
    auto=> /> &1 &2 fdom_eq eq_rem_fst4 pubmap_id valid_in_pubmap id_valid.
    move: (valid_in_pubmap _ id_valid) (pubmap_id id{2}); rewrite domE.
    case: (BP.pubmap.[id]{2})=> /> id' /(_ id') /= <<- //=.
    have -> //:   (oget (ohead (odflt [] BP.vmap.[id]))).`2{2}
                = (oget (ohead (odflt [] BP.vmap{1}.[id]))).`2{2}.
    move: (eq_rem_fst4 id{2} 0).
    by rewrite !nth0_head !(head_ohead witness) /oget /rem_fst4=> /= - [] ->.
  + by proc; inline *; auto.
  + by conseq So_ll2.
  by auto.
(***********************************)
(************* Clean up ************)
(***********************************)
seq  7  7: (   ={glob A, glob C, glob Ve, glob S, glob E, glob HRO.ERO, valid, dbb}
            /\ ={setHcheck, secmapD, setD, setidents, setH, sk, pk, bb, bb',
                 sethappy, setchecked, bb0, bb1, pubmap, r}(BP, BP)
            /\ fdom BP.vmap{1} = fdom BP.vmap{2}
            /\ (forall (idl0 : ident) (j0 : int),
                    rem_fst4 (nth witness (odflt [] BP.vmap{1}.[idl0]) j0)
                  = rem_fst4 (nth witness (odflt [] BP.vmap{2}.[idl0]) j0))
            /\ (forall (idl : ident) (b : cipher),
                     (idl, b) \in rem_ids BP.bb0{2}
                  =>   Some (nth witness (odflt [] BP.vmap{2}.[idl]) (find (fun (x : _ * _ * _ * _)=> x.`1 = b) (odflt [] BP.vmap{2}.[idl]))).`4
                     = dec_cipher BP.sk{2} idl b HRO.ERO.m{2})
            /\ (forall id id', BP.pubmap{2}.[id] = Some id' => id = id')
            /\ (forall id, id \in BP.setidents{2} => id \in BP.pubmap{2}) ).
+ seq  2  2: (   ={glob A, glob C, glob Ve, glob S, glob E, glob HRO.ERO, valid}
              /\ ={setHcheck, secmapD, setD, setidents, setH, sk, pk, bb, bb',
                   sethappy, setchecked, bb0, bb1, pubmap}(BP, BP)
              /\ fdom BP.vmap{1} = fdom BP.vmap{2}
              /\ (forall (idl0 : ident) (j0 : int),
                      rem_fst4 (nth witness (odflt [] BP.vmap{1}.[idl0]) j0)
                    = rem_fst4 (nth witness (odflt [] BP.vmap{2}.[idl0]) j0))
              /\ (forall (idl : ident) (b : cipher),
                       (idl, b) \in rem_ids BP.bb0{2}
                    => Some (nth witness (odflt [] BP.vmap{2}.[idl]) (find (fun (x : _ * _ * _ * _)=> x.`1 = b)
                                         (odflt [] BP.vmap{2}.[idl]))).`4
                       = dec_cipher BP.sk{2} idl b HRO.ERO.m{2})
              /\ (forall id id', BP.pubmap{2}.[id] = Some id' => id = id')
              /\ (forall id, id \in BP.setidents{2} => id \in BP.pubmap{2}) ).
  + inline *.
    auto; while (={i1, bb0, bb1, bb2, bb'}); first by sim.
    auto; while (={i0, e1, e2, pk, bb, glob HRO.ERO, glob C, glob A}); first by sim.
    by auto.
  seq  3  3: (   ={glob A, glob C, glob Ve, glob S,  glob E, glob HRO.ERO, valid, dbb, j}
              /\ ={setHcheck, secmapD, setD, setidents, setH, sk, pk, bb, bb',
                   sethappy, setchecked, bb0, bb1, pubmap}(BP, BP)
              /\ fdom BP.vmap{1} = fdom BP.vmap{2}
              /\ (forall (idl0 : ident) (j0 : int),
                      rem_fst4 (nth witness (odflt [] BP.vmap{1}.[idl0]) j0)
                    = rem_fst4 (nth witness (odflt [] BP.vmap{2}.[idl0]) j0))
              /\ (forall (idl : ident) (b : cipher),
                       (idl, b) \in rem_ids BP.bb0{2}
                    => Some (nth witness (odflt [] BP.vmap{2}.[idl]) (find (fun (x : _ * _ * _ * _)=> x.`1 = b)
                                         (odflt [] BP.vmap{2}.[idl]))).`4
                       = dec_cipher BP.sk{2} idl b HRO.ERO.m{2})
              /\ (forall id id', BP.pubmap{2}.[id] = Some id' => id = id')
              /\ (forall id, id \in BP.setidents{2} => id \in BP.pubmap{2})).
  + sp; while (   ={j, BP.bb', glob HRO.ERO, glob E, BP.sk, dbb}
               /\ (forall (idl : ident) (b : cipher),
                        (idl, b) \in rem_ids BP.bb0{2}
                     => Some (nth witness (odflt [] BP.vmap{2}.[idl]) (find (fun (x : _ * _ * _ * _)=> x.`1 = b)
                                          (odflt [] BP.vmap{2}.[idl]))).`4
                        = dec_cipher BP.sk{2} idl b HRO.ERO.m{2})).
    + inline *; sp.
      if{2}=> //; auto.
      + exists* (glob E){1}, BP.sk{1}, idl{1}, b{1}; elim * => ee sk1 idl1 b1.
        call {1} (Edec_Odec ee sk1 idl1 b1).
        auto=> /> &2 <- /> enc_correct _ /enc_correct <-.
        by rewrite nth_onth.
      exists* (glob E){1}, BP.sk{1}, idl{1}, b{1}; elim *=> ee sk1 idl1 b1.
      call (Edec_Odec_eq sk1 idl1 b1).
      by auto=> /> /#.
    by auto.
  by auto.
by auto.
qed.

(***************** Stop recovering and set BP.bb' to be BP.bb *******************)
local module G2R (E  : Scheme)
                 (P  : Prover)
                 (Ve : Verifier)
                 (C  : ValidInd)
                 (A  : DU_MB_BPRIV_adv)
                 (H  : HOracle.Oracle)
                 (S  : Simulator) = {

  module MV = MV(E,P,Ve,C, H, S)

  module O  = {
    proc h = H.o
    proc g = S.o

    proc vote_core(id, v, sl) = {
      var p, b, spr, spo;
      
      (p, b, spr, spo) <@ MV.vote(BP.pk, id, id, sl, v);

      return (p, b, spr, spo);
    }

    proc vote (id : ident, v0 v1 : vote) = {
      var p0, b0, s0pr, s0po;
      var p1, b1, s1pr, s1po;

      if ((id \in BP.setH)) {
        (s0pr, s0po, b0, p0)  <@ vote_core(id, v0, oget BP.secmap.[id]);
        (s1pr, s1po, b1, p1)  <@ vote_core(id, v1, oget BP.secmap.[id]);

        (* We now store b1, b1, v0 instead of b0, b1, v0, as we did in G1R *)
        BP.vmap.[id] <- (b1, b1, b1, v0) :: (odflt [] BP.vmap.[id]);
        BP.bb0 <- (id, id, b0) :: BP.bb0;
        BP.bb1 <- (id, id, b1) :: BP.bb1;
      }
    }

    proc verify(id:ident) : ident fset = {
      var ok, sv;
      if (id \in BP.setidents){
        BP.setchecked <- BP.setchecked `|` (fset1 id);
        sv <- odflt [] (BP.vmap.[id]);
        ok <@ MV.verifyvote(id,(head witness sv).`2, (head witness sv).`3, 
                            BP.bb, BP.bbstar, id, tt); 
        if (ok) {
          BP.sethappy <- BP.sethappy `|` (fset1 id);
        }
      }
      return BP.sethappy;
    }
  
    proc board() : pubBB = {
      return Publish(rem_ids BP.bb1);
    }
  }


  module A  = A(O)
 
  proc main() : bool = {
    var i, id, sv, k;
    var valid, valid';
    var j, dbb, idl, b, v, d;
    
    BP.vmap    <- empty;
    BP.pubmap  <- empty;
    BP.secmap  <- empty;
    BP.secmapD <- empty;
    BP.bb0     <- [];
    BP.bb1     <- [];
    BP.setchecked <- fset0;
    BP.sethappy   <- fset0;

    H.init();
    S.init();

    (* setup: key generation *)
    (BP.pk, BP.sk) <@ MV.setup();

    (* registration *)
    i <- 0;
    while (i < card BP.setidents) {
      id <- nth witness (elems BP.setidents) i;
      BP.secmap.[id] <- tt;
      BP.pubmap.[id] <- id;
      if (id \in BP.setD) {
        BP.secmapD.[id] <- oget BP.secmap.[id];
      }
    i <- i + 1;
    }

    (* adversary creates first bulletin board *)
    BP.bb <@ A.create_bb(BP.pk, BP.secmapD, BP.pubmap, BP.setHcheck);

    valid <@ MV.validboard(BP.bb, BP.pk);

     dbb      <- [];
      j       <- 0;
     while (j < size BP.bb) {
      (idl, b) <- nth witness BP.bb j;
       if ( (idl, b) \in rem_ids BP.bb1) {
        (* Get the vote from the vmap element which matches the ballot *)
        sv <- odflt [] BP.vmap.[idl];
        k  <- find (fun (x : cipher*cipher*cipher*vote)  => x.`1 = b) sv;
        v  <- Some (oget (onth sv k) ).`4;
       } else {
           v <@ E(H).dec(BP.sk, idl, b);
       }
       dbb   <- dbb ++ [(idl, v)];
        j    <- j + 1;
     }
     
      BP.r      <$ Rho dbb;
      BP.pk     <- getPK BP.sk;
    
    if (!(BP.setHcheck \subset fdom BP.vmap)) {
      BP.d <$ {0,1};
    } else {
      if (!valid) {
        BP.d <$ {0,1}; 
      } else {
         BP.pi'    <@ S.prove(BP.pk, Publish BP.bb, BP.r);
             d     <@ A.initial_guess();
         BP.bbstar <@ A.get_tally(BP.r, BP.pi');
          valid'   <@ MV.verifytally((BP.pk, Publish BP.bb, BP.bbstar.`1), BP.bbstar.`2);
        if (!valid') {
          BP.d <$ {0,1};
        } else {
         BP.d <@ A.final_guess();
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

(*** Proof that G1R and G2R are equivalent ***) 
local lemma G1R_G2R_equiv &m : 
    Pr[G1R(E,P,Ve,C,A,HRO.ERO,S).main() @ &m : res]
  = Pr[G2R(E,P,Ve,C,A,HRO.ERO,S).main() @ &m : res].
proof. 
byequiv (: ={glob A, glob C, glob Ve, glob S, glob E, glob P}
           /\ ={setHcheck, secmapD, setD, setidents, setH, d}(BP, BP)  ==> _)=> //.
proc.
(* 1/3 The first part (up until create_bb) should be exactly indentical *)
seq 13 13: (   ={glob A, glob S, glob C, glob E,  glob HRO.ERO, glob P, glob Ve}
            /\ ={pk, sk, setidents, bb0, bb1, sethappy, setchecked, secmap, secmapD,
                 pubmap, setH, setHcheck, vmap}(BP, BP)
            /\ BP.bb0{1} = BP.bb1{1} /\ BP.bb0{1} = []
            /\ BP.pk{1} = getPK BP.sk{1}).
+ while (   ={i, glob P}
         /\ ={setidents, secmapD, secmap, setidents, setD, pubmap}(BP, BP)); first by sim.
  inline *; auto; call (E_kgen_getPK HRO.ERO).
  call (: true); while (={w, glob HRO.ERO}); first by sim.
  by auto.
(* 2/3 As should the last *)
seq  6  5: (   ={glob A, glob S, glob C, glob E, glob HRO.ERO, glob P, glob Ve, dbb, valid}
            /\ ={sk, setHcheck, bb0, bb1, bb, sethappy, setchecked, setidents}(BP, BP)
            /\ fdom BP.vmap{1} = fdom BP.vmap{2}
            /\ (forall id, (head witness (odflt [] BP.vmap{1}.[id])).`2 = 
                           (head witness (odflt [] BP.vmap{2}.[id])).`2)); last first.
+ seq  2  2: (#pre /\ ={BP.r, BP.pk}); first by auto.
  (* Beginning ifs *) 
  if; auto=> [/#|].
  if; auto.
  seq  4  4: (#pre /\ ={d, valid', BP.pi', BP.bbstar}).
  + inline *; auto; call (: ={glob S}); first by sim.
    auto; call (: ={BP.bb0, BP.bb1, glob S, glob HRO.ERO}); first 3 by sim.
    call (: ={glob HRO.ERO, glob S}); first 2 by sim.
    by call (: true); auto.
  if=> //; auto.
  sim; call (:    ={BP.bbstar, BP.bb, glob HRO.ERO, glob S, BP.setchecked, BP.sethappy, BP.setidents}
               /\ (forall id,   (head witness (odflt [] BP.vmap{1}.[id])).`2
                              = (head witness (odflt [] BP.vmap{2}.[id])).`2)).
  + proc; inline *; if=> //.
    by auto=> /> /#.
  + by proc.
  + by conseq So_ll2.
  by auto.
(*****************************)
(* 3/3 Now for the hard part *)
(*****************************)
(* We start by taking the board created by the adversary and prove the folllowing facts         *)
(*                                                                                                *)
(* 1. The domain of vmap is the same in both games                                                *)
(* 2. The ballot to be counted is the same in both vmaps : vmap is a tuple (cast, counted, vote)  *)
(* 3. The standard fact needed to see that recovery works in the left game                        *)
(* 4. bb0 and bb1 agree on labels                                                                 *)
(* 5. The size of the two boards is the same                                                      *)
(* 6. The recovery and vmap in left is equivalent to vmap in right                                 *)
(*                                                                                                *)
seq  1  1: (   ={glob A, glob S, glob C, glob E, glob HRO.ERO, glob P, glob Ve}
            /\ ={sk, pk, setHcheck, bb0, bb1, bb, sethappy, setchecked, setH, secmap, secmapD, setidents}(BP, BP)
    (* 1 *) /\ fdom BP.vmap{1} = fdom BP.vmap{2}
    (* 2 *) /\ (forall id,   (head witness (odflt [] BP.vmap{1}.[id])).`2
                           = (head witness (odflt [] BP.vmap{2}.[id])).`2)
    (* 3 *) /\ (forall (idl : ident) (b : cipher), (idl, b) \in rem_ids BP.bb0{1}  =>  
                    Some (nth witness (odflt [] BP.vmap{1}.[idl]) 
                              (find (fun (x : _ * _ * _ * _)=> x.`1 = b)  
                                    (odflt [] BP.vmap{1}.[idl]))).`4
                  = dec_cipher BP.sk{2} idl b HRO.ERO.m{2})
    (* 4 *) /\ (forall j, (nth witness (rem_ids BP.bb0{2}) j).`1 = (nth witness (rem_ids BP.bb1{2}) j).`1)
    (* 5 *) /\ size BP.bb0{1} = size BP.bb1{1}
    (* 6 *) /\ (forall idl b2, (idl, b2) \in rem_ids BP.bb1{2} =>
                    Some (nth witness (odflt [] BP.vmap{1}.[idl])
                              (find (fun (x : _ * _ * _ * _)=>
                              x.`1 = (nth witness (rem_ids BP.bb0{2}) (index (idl, b2) (rem_ids BP.bb1{2}))).`2)
                                    (odflt [] BP.vmap{1}.[idl]))).`4 
                  = Some (nth witness (odflt [] BP.vmap{2}.[idl])
                              (find (fun (x : _ * _ * _ * _)=> x.`1 = b2)
                                    (odflt [] BP.vmap{2}.[idl]))).`4)).
+ call (:    ={glob S, glob C, glob E, glob HRO.ERO, glob P, glob Ve}
          /\ ={sk, pk, setHcheck, bb0, bb1, sethappy, setchecked, setH, secmap, secmapD}(BP, BP)
          /\ fdom BP.vmap{1} = fdom BP.vmap{2} 
          /\ size BP.bb0{1} =  size BP.bb1{1}
          /\ (forall id, 
                  (head witness (odflt [] BP.vmap{1}.[id])).`2 
                = (head witness (odflt [] BP.vmap{2}.[id])).`2)
          /\ (forall (idl : ident) (b : cipher), (idl, b) \in rem_ids BP.bb0{1} =>
                  Some (nth witness (odflt [] BP.vmap{1}.[idl])
                            (find (fun (x : _ * _ * _ * _)=> x.`1 = b)
                                  (odflt [] BP.vmap{1}.[idl]))).`4
                = dec_cipher BP.sk{2} idl b HRO.ERO.m{2})
          /\ (forall j,   (nth witness (rem_ids BP.bb0{2}) j).`1 
                        = (nth witness (rem_ids BP.bb1{2}) j).`1)
          /\ (forall (idl : ident) (b : cipher), 
                   (idl, b) \in rem_ids BP.bb0{1} \/ (idl, b) \in rem_ids BP.bb1{2}
                => is_some BP.vmap{1}.[idl] /\ is_some BP.vmap{2}.[idl])
          /\ (forall idl b2, (idl, b2) \in rem_ids BP.bb1{2} =>
                  Some (nth witness (odflt [] BP.vmap{1}.[idl])
                            (find (fun (x : _ * _ * _ * _)=>
                             x.`1 = (nth witness (rem_ids BP.bb0{2}) (index (idl, b2) (rem_ids BP.bb1{2}))).`2)
                                  (odflt [] BP.vmap{1}.[idl]))).`4 
                = Some (nth witness (odflt [] BP.vmap{2}.[idl])
                            (find (fun (x : _ * _ * _ * _)=> x.`1 = b2)
                                  (odflt [] BP.vmap{2}.[idl]))).`4)
          /\ BP.pk{1} = getPK BP.sk{1}).
  + proc; if=> //=.
    wp; conseq />.
    inline *.
    exists * BP.sk{1}, v0{1}, v1{1}, id{1}; elim *=> sk1 v0 v1 id1.
    wp; call (Eenc_dec sk1 id1 v1).
    wp; call (Eenc_dec sk1 id1 v0).
    auto=> /> &1 &2 eq_fdom eq_size eq_headvote enc_correct eq_rem_ids in_rem_ids_has_vote eq_getvote.
    move=> id_honest b0 v0_correct b1 v1_correct.
    split; first by rewrite !fdom_set eq_fdom.
    split; first by rewrite eq_size.
    split=> [id|].
    + by rewrite !get_setE; case: (id = id1)=> /> _; exact: eq_headvote.
    split=> [id b|].
    + rewrite /rem_ids map_cons -/(rem_ids BP.bb0{2}) /rem_id /=.
      rewrite !get_setE; case: (id = id1)=> /> => [|_ /enc_correct] //.
      by rewrite eq_sym; case: (b0 = b)=> /> _ /enc_correct; smt(find_ge0).
    split=> [j|].
    + by rewrite /rem_ids /=; case: (j = 0)=> // j_neq_0; exact: eq_rem_ids.
    split=> [id b|].
    + rewrite /rem_ids /= -!/(rem_ids _) /rem_id /=.
      by rewrite !get_setE; case: (id = id1)=> /> _ /in_rem_ids_has_vote.
    move=> id b.
    rewrite /rem_ids /= -!/(rem_ids _) /rem_id /=.
    rewrite !get_setE; case: (id = id1)=> />.
    + move=> @/index; rewrite pred1E /=; case: (b = b1)=> /> ^ b_neq_b1.
      rewrite eq_sym=> -> id1b_in_bb /=.
      move: (in_rem_ids_has_vote id1 b); rewrite id1b_in_bb /=.
      case: {-1}(BP.vmap.[id1]{1}) (eq_refl BP.vmap.[id1]{1})=> /> vsid1 vmap1_id1.
      case: {-1}(BP.vmap.[id1]{2}) (eq_refl BP.vmap.[id1]{2})=> /> vsid2 vmap2_id1.
      have !-> /=: forall (p : (label * cipher) -> bool) xs, find p xs + 1 <> 0 by smt(find_ge0).
      case: (b0 = (nth witness (rem_ids BP.bb0{2}) (find ((=) (id1, b)) (rem_ids BP.bb1{2}))).`2)
             => />; last first.
      + have !-> /=: forall (p : (cipher * cipher * cipher * vote) -> bool) xs, find p xs + 1 <> 0 
               by smt(find_ge0).
        have !-> /=: forall (p : (cipher * cipher * cipher * vote) -> bool) xs, find p xs + 1 <> 0 
               by smt(find_ge0).
        move: (eq_getvote _ _ id1b_in_bb); rewrite vmap1_id1 vmap2_id1=> //= <-.
        have -> //: find ((=) (id1, b)) (rem_ids BP.bb1{2}) = index (id1, b) (rem_ids BP.bb1{2}).
        by rewrite /index; congr; apply: fun_ext=> x @/pred1; rewrite (eq_sym x).
      have -> /=: forall p (xs : (cipher * cipher * cipher * vote) list), find p xs + 1 <> 0 by smt(find_ge0).
      move: (eq_getvote _ _ id1b_in_bb); rewrite vmap1_id1 vmap2_id1=> /= <-.
      apply: someI; rewrite v0_correct eq_sym=> />.
      move: (enc_correct id1); rewrite vmap1_id1=> /= ->.
      + have {1}->: id1 = (nth witness (rem_ids BP.bb0{2}) (index (id1, b) (rem_ids BP.bb1{2}))).`1.
        + by rewrite eq_rem_ids nth_index.
        have /#: nth witness (rem_ids BP.bb0{2}) (index (id1, b) (rem_ids BP.bb1{2})) \in rem_ids BP.bb0{2}.
        apply: mem_nth.
        have ->: size (rem_ids BP.bb0{2}) = size (rem_ids BP.bb1{2}).
        + by rewrite !size_map eq_size.
        by rewrite index_ge0 index_mem.
      have -> //: find ((=) (id1, b)) = index (id1, b).
      by have ->: ((=) (id1, b)) = pred1 (id1, b) by apply: fun_ext=> x; rewrite -(eq_sym x).
    rewrite /index /= {1 3}pred1E=> /= -> /=.
    have -> /=: find (pred1 (id, b)) (rem_ids BP.bb1{2}) + 1 <> 0 by smt(find_ge0).
    exact: eq_getvote.
  + by proc.
  + by proc.
  + by conseq So_ll2.
  by auto=> />.
(* Validity is easy *)
seq  1  1: (#pre /\ ={valid}).
+ call (: ={glob HRO.ERO, glob C, glob A, BP.bb0}).
  + while (={pk, bb, i, e1, e2, glob HRO.ERO, glob C}); first by sim.
    by auto.
  by auto.
(* We have now shown the that boards and both are valid produced by the adversary are the same in both games *)
(* We are now going to prove some facts about recovery *)
(*   1. For a given position j, if bb{j} is not in bb1, then bb' and bb agree at that position      *)
(*   2. bb' and bb agree on id at all positions                                                     *)
(*   3. If in right than in left                                                                    *)
(*   4. If in left and right then right is left                                                     *)
(*                                                                                                  *)
seq  3  2: (   ={glob A, glob S, glob C, glob E, glob HRO.ERO, glob P, glob Ve, dbb, valid, j}
            /\ ={sk, setHcheck, bb0, bb1, bb, sethappy, setchecked, bb, setidents}(BP, BP)
            /\ fdom BP.vmap{1} = fdom BP.vmap{2}
            /\ size BP.bb'{1} = size BP.bb{2}
            /\ j{1} = 0
            /\ (forall id,   (head witness (odflt [] BP.vmap{1}.[id])).`2
                           = (head witness (odflt [] BP.vmap{2}.[id])).`2)
            /\ (forall (idl : ident) (b : cipher), (idl, b) \in rem_ids BP.bb0{1} =>
                    Some (nth witness (odflt [] BP.vmap{1}.[idl])
                              (find (fun (x : _ * _ * _ * _)=> x.`1 = b)
                              (odflt [] BP.vmap{1}.[idl]))).`4
                  = dec_cipher BP.sk{2} idl b HRO.ERO.m{2})
            /\ (forall j,    !nth witness BP.bb{2} j \in rem_ids BP.bb1{1}
                          => nth witness BP.bb'{1} j = nth witness BP.bb{2} j)
            /\ (forall j, (nth witness BP.bb'{1} j).`1 = (nth witness BP.bb{2} j).`1)
            /\ (forall j, (nth witness (rem_ids BP.bb0{1}) j).`1 = (nth witness (rem_ids BP.bb1{1}) j).`1)
            /\ size BP.bb0{1} = size BP.bb1{1}
            /\ (forall (idl0 : ident) (b2 : cipher), (idl0, b2) \in rem_ids BP.bb1{2} =>
                    Some (nth witness (odflt [] BP.vmap{1}.[idl0])
                              (find (fun (x : _ * _ * _ * _) =>
                                         x.`1
                                       = (nth witness (rem_ids BP.bb0{2})
                                              (index (idl0, b2) (rem_ids BP.bb1{2}))).`2)
                                                     (odflt [] BP.vmap{1}.[idl0]))).`4
                  = Some (nth witness (odflt [] BP.vmap{2}.[idl0])
                              (find (fun (x : _ * _ * _ * _) => x.`1 = b2)
                              (odflt [] BP.vmap{2}.[idl0]))).`4)
            /\ (forall j, 0 <= j < size BP.bb'{1} => (nth witness BP.bb{2} j) \in rem_ids BP.bb1{1} =>
                  (nth witness BP.bb'{1} j \in rem_ids BP.bb0{1}))
            /\ (forall j, 0 <= j < size BP.bb'{1} => (nth witness BP.bb{2} j) \in rem_ids BP.bb1{2} =>
                    (nth witness BP.bb'{1} j)
                  = nth witness (rem_ids BP.bb0{1}) (index (nth witness BP.bb{2} j) (rem_ids BP.bb1{2})))).
+ inline *; auto.
  while {1} (   ={BP.bb, BP.bb0, BP.bb1}
             /\ 0 <= i0{1} <= size bb{1} 
             /\ size bb'{1} = i0{1}
             /\ size BP.bb0{1} = size BP.bb1{1}
             /\ (forall j, 
                   0 <= j < size bb'{1} => 
                   ! nth witness BP.bb{2} j \in rem_ids BP.bb1{1} =>
                         nth witness bb'{1} j = nth witness BP.bb{2} j) 
             /\ bb0{1} = rem_ids BP.bb0{1} 
             /\ bb{1} = BP.bb{1} 
             /\ bb1{1} = rem_ids BP.bb1{1} 
             /\ (forall j, 
                   (nth witness (rem_ids BP.bb0{1}) j).`1 = 
                   (nth witness (rem_ids BP.bb1{1}) j).`1) 
             /\ (forall j, 
                   0 <= j < size bb'{1} => 
                      (nth witness bb'{1} j).`1 = (nth witness BP.bb{2} j).`1) 
             /\ (forall j, 
                   0 <= j < size bb'{1} => 
                      (nth witness BP.bb{2} j) \in rem_ids BP.bb1{1} =>
                           (nth witness bb'{1} j \in rem_ids BP.bb0{1}))  
             /\ (forall j, 
                   0 <= j < size bb'{1} => 
                      (nth witness BP.bb{2} j)  \in rem_ids BP.bb1{2} =>
                          (nth witness bb'{1} j)
                           = nth witness (rem_ids BP.bb0{1}) 
                               (index (nth witness BP.bb{2} j) (rem_ids BP.bb1{2})))) 
          (size bb{1} - i0{1}).
   + move=> &0 z; sp 1; if=> //.
     + auto=> /> &1 pb0P _ _ bb0_eq_bb1 h1 h2 h3 h4 h5 bb'_lt_bb.
       move=> pb0_in_bb1; split.
       + split; 1:smt(size_ge0).
         split; 1:smt(size_cat).
         split; 1:smt(size_cat nth_cat).
         split.
         + move=> j ge0_j; rewrite size_cat nth_cat /=.
           move=> /ltzS /lez_eqVlt [->>|^ j_lt_bb'] />.
           + by rewrite h2 nth_index // pb0P.
           by move=> _; exact: h3.
         split.
         + move=> j ge0_j; rewrite size_cat nth_cat /=.
           move=> /ltzS /lez_eqVlt [->> _|/> j_lt_sizebb'] />.
           + apply mem_nth; rewrite index_ge0.
             have ->: size (rem_ids BP.bb0{0}) = size (rem_ids BP.bb1{0}).
             + by rewrite !size_map bb0_eq_bb1.
             by rewrite index_mem.
           exact: h4.
         move=> j ge0_j; rewrite size_cat nth_cat /=.
         move=> /ltzS /lez_eqVlt [->> _|/> j_lt_sizebb'] />.
         + by rewrite pb0P.
         exact: h5.
       smt().
     auto=> /> &1 pb0P _ _ bb0_eq_bb1 h1 h2 h3 h4 h5 bb'_lt_bb.
     move=> pb0_notin_bb1; split.
     + split; 1:smt(size_ge0).
       split; 1:smt(size_cat).
       split.
       + move=> j ge0_j; rewrite size_cat nth_cat /=.
         move=> /ltzS /lez_eqVlt [->>|^ j_lt_bb'] />.
         by move=> _; exact: h1.
       split.
       + move=> j ge0_j; rewrite size_cat nth_cat /=.
         move=> /ltzS /lez_eqVlt [->>|^ j_lt_sizebb'] />.
         + by rewrite -pb0P.
         by move=> _; exact: h3.
       split.
       + move=> j ge0_j; rewrite size_cat nth_cat /=.
         move=> /ltzS /lez_eqVlt [->>|/> j_lt_sizebb'] />.
         + by rewrite -pb0P pb0_notin_bb1.
         exact: h4.
       move=> j ge0_j; rewrite size_cat nth_cat /=.
       move=> /ltzS /lez_eqVlt [->>|/> j_lt_sizebb'] />.
       + by rewrite -pb0P pb0_notin_bb1.
       exact: h5.
     smt().
   auto=> /> &1 &2 eq_fdom eq_head_vote enc_correct eq_rem_ids1 eq_size correct_lkup.
   split; 1:smt(nth_neg size_ge0).
   move=> bb'; split=> [/#|].
   move=> h _ h'; have {h h'} eq_size': size bb' = size BP.bb{2} by smt().
   move=> eq_rngF eq_fstF rem_idsF eq_dec_lkupF.
   rewrite eq_size' /=; split.
   + move=> j; case: (0 <= j < size bb').
     + exact: eq_rngF.
     case: (0 <= j)=> /> => [_|].
     + move=> ^ /lezNgt /nth_default ->.
       by rewrite eq_size'=> /lezNgt /nth_default ->.
     by move=> /ltzNge /(nth_neg<:label * cipher>) ^ -> ->.
   move=> j; case: (0 <= j < size bb').
   + exact: eq_fstF.
   case: (0 <= j)=> /> => [_|].
   + move=> ^ /lezNgt /nth_default ->.
     by rewrite eq_size'=> /lezNgt /nth_default ->.
   by move=> /ltzNge /(nth_neg<:label * cipher>) ^ -> ->.
(*** FIXME: THe following remains to clean up!!! **)
(* We are ready to enter the while loop and prove dbb eq *)
while (={j, glob HRO.ERO, glob E, dbb, BP.sk, BP.bb0, BP.bb1, BP.sk, dbb}  /\ size BP.bb'{1} = size BP.bb{2}
    /\ (forall (idl : ident) (b : cipher) (v : vote), (idl, b) \in rem_ids BP.bb0{1}  =>  
    Some (oget (onth (odflt [] BP.vmap{1}.[idl]) (find (fun (x : cipher*cipher*cipher*vote) 
              => x.`1 =b)(odflt [] BP.vmap{1}.[idl])))).`4
      = dec_cipher BP.sk{2} idl b HRO.ERO.m{2}) /\ 0  <= j{1}
      /\ (forall j,  ! nth witness BP.bb{2} j \in rem_ids BP.bb1{1} => nth witness BP.bb'{1} j = 
                                                                       nth witness BP.bb{2} j)
        /\ (forall j, (nth witness BP.bb'{1} j).`1 = (nth witness BP.bb{2} j).`1)
        /\ (forall (idl0 : ident) (b2 : cipher), (idl0, b2) \in rem_ids BP.bb1{2} => Some (oget
         (onth (odflt [] BP.vmap{1}.[idl0])  (find (fun (x : cipher * cipher * cipher * vote) =>  x.`1 =
         (nth witness (rem_ids BP.bb0{2}) (index (idl0, b2) (rem_ids BP.bb1{2}))).`2) 
         (odflt [] BP.vmap{1}.[idl0])))).`4 =
           Some (oget (onth (odflt [] BP.vmap{2}.[idl0]) (find (fun (x : cipher * cipher * cipher * vote) => 
           x.`1 = b2)
               (odflt [] BP.vmap{2}.[idl0])))).`4)
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
  (* This bit is if central *)
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
+ by rewrite -H2 // nth_onth.
+ move: (H7 idl0 b2 _)=> //; rewrite nth_onth=> ->.
  by rewrite nth_onth.
+ smt().
smt().
qed.

(****************************************************************************************************)
(** Modify G2R to a game where we use a single board rather than BP.bb0 and BP.bb1 similar to G2L. **)
(** We add b1 to the board, but we pick v0 from vmap and use this in the tally.                    **)
(****************************************************************************************************)

local module G3R (E:Scheme, P:Prover, Ve:Verifier, C:ValidInd, 
                  A:DU_MB_BPRIV_adv, H:HOracle.Oracle, S:Simulator)  = {

  var bb : (ident * cipher) list

  module MV = MV(E,P,Ve,C, H, S)

  module O  = {
    proc h = H.o
    proc g = S.o

    proc vote_core(id, v, sl) = {
      var p, b, spr, spo;
      
      (p, b, spr, spo) <@ MV.vote(BP.pk, id, id, sl, v);

      return (p, b, spr, spo);
    }

    proc vote (id : ident, v0 v1 : vote) = {
      var p1, b1, s1pr, s1po;

      if ((id \in BP.setH)) {
        (s1pr, s1po, b1, p1)  <@ vote_core(id, v1, oget BP.secmap.[id]);

        (* ballot cast, ballot counted, vote *)
        BP.vmap.[id] <- (b1, b1, s1po, v0) :: (odflt [] BP.vmap.[id]);
        bb <- (id, b1) :: bb;
      }
    }
   

    proc verify(id:ident) : ident fset = {
      var ok, sv;
      if (id \in BP.setidents){
        BP.setchecked <- BP.setchecked `|` (fset1 id);
        sv <- odflt [] (BP.vmap.[id]);
        ok <@ MV.verifyvote(id,(oget (ohead sv)).`2, (oget (ohead sv)).`2, 
                          BP.bb, BP.bbstar, id, tt); 
        if (ok) {
          BP.sethappy <- BP.sethappy `|` (fset1 id);
        }
      }
      return BP.sethappy;
    }

    proc board() : pubBB = {
      return Publish(bb);
    }
  }


  module A  = A(O)
 
  proc main() : bool = {
    var i, id;
    var valid, valid';
    var j, dbb, idl, b, v, d;
    
    BP.vmap       <- empty;
    BP.pubmap     <- empty;
    BP.secmap     <- empty;
    BP.secmapD    <- empty;
    BP.setchecked <- fset0;
    BP.sethappy   <- fset0;

    bb <- [];

    H.init();
    S.init();

    (* setup: key generation *)
    (BP.pk, BP.sk) <@ MV.setup();

    (* registration *)
    i <- 0;
    while (i < card BP.setidents) {
      id <- nth witness (elems BP.setidents) i;
      BP.secmap.[id] <- tt;
      BP.pubmap.[id] <- id;
      if (id \in BP.setD) {
        BP.secmapD.[id] <- oget BP.secmap.[id];
      }
    i <- i + 1;
    }

    (* adversary creates first bulletin board *)
    BP.bb <@ A.create_bb(BP.pk, BP.secmapD, BP.pubmap, BP.setHcheck);

    valid <@ MV.validboard(BP.bb, BP.pk);

     dbb      <- [];
      j       <- 0;
     while (j < size BP.bb) {
      (idl, b) <- nth witness BP.bb j;
       if ( (idl, b) \in bb) {
          (* Get the vote from the vmap element which matches the ballot *)
          v <- Some (oget (onth (odflt [] BP.vmap.[idl]) 
               (find (fun (x : cipher*cipher*cipher*vote) => x.`1 =b)  (odflt [] BP.vmap.[idl])))).`4;
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
        BP.d <$ {0,1}; 
      } else {
         BP.pi'    <@ S.prove(BP.pk, Publish BP.bb, BP.r);
            d      <@ A.initial_guess();
         BP.bbstar <@ A.get_tally(BP.r, BP.pi');
          valid'   <@ MV.verifytally((BP.pk, Publish BP.bb, BP.bbstar.`1), BP.bbstar.`2);
        if (!valid') {
          BP.d <$ {0,1};
        } else {
          BP.d <@ A.final_guess();
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

(************* Prove that G2R and G3R are equivalent ****************)
local lemma G2R_G3R_equiv &m :
    Pr[G2R(E,P,Ve,C,A,HRO.ERO,S).main() @ &m : res] = Pr[G3R(E,P,Ve,C,A,HRO.ERO,S).main() @ &m : res]. 
proof. 
byequiv (_: ={glob A, glob C, glob Ve, glob S, glob E, BP.setHcheck, BP.secmapD, 
              BP.setD, BP.setidents, BP.setH, BP.bbstar} ==> _) => //. 
proc. swap{2} 6 -2. 
 
(**** Everything up until the adversary creates BP.bb should be equivalent ****)
seq 13 12 : (={glob A, glob HRO.ERO, glob C, glob Ve, glob S, glob E, BP.setHcheck, 
               BP.secmapD, BP.setD, BP.setidents, BP.setH,
               BP.pk, BP.sk, BP.vmap, BP.pubmap, BP.secmap, BP.setchecked, BP.sethappy, BP.bbstar}
  /\ (rem_ids BP.bb1{1} = G3R.bb{2})
  /\ (BP.pk{1} = getPK BP.sk{1})
).
while (={i, BP.setidents, BP.secmap, BP.pubmap, BP.setD, BP.secmapD}); first by sim. 
wp. 
inline*. 
wp; call (E_kgen_getPK HRO.ERO); call(_:true).  
while (={w, HRO.ERO.m}); first by sim. auto;progress. 


(**** We now do the if sentences, which should be more or less equal on the two sides ****)
seq 7 6 : (={BP.setHcheck, valid, BP.vmap, BP.bbstar, BP.r, BP.pk, BP.sk, 
             BP.setchecked, BP.sethappy, BP.bb, BP.bbstar,
             glob HRO.ERO, glob C, glob S, glob Ve, glob E, glob A, BP.setidents} 
           /\ rem_ids BP.bb1{1} = G3R.bb{2}); last first.
if => //; first by rnd. 
if => //; first by rnd.
seq 4 4 : ((={BP.setHcheck, valid, BP.vmap, BP.bbstar, BP.r, BP.pk, BP.sk, BP.pi', valid', d,
       BP.setchecked, BP.sethappy, BP.setidents, BP.bb, glob HRO.ERO, glob C, glob S,
       glob Ve, glob E, glob A} /\ rem_ids BP.bb1{1} = G3R.bb{2} /\
   ! ! (BP.setHcheck{1} \subset fdom BP.vmap{1})) /\
  ! !valid{1}). 
inline*.
wp. 
call(_: ={glob S}); first by conseq So_ll2. wp. 
call(_: ={glob S, glob HRO.ERO} /\ rem_ids BP.bb1{1} = G3R.bb{2}). proc;inline*;auto. proc;inline*;auto. 
 conseq So_ll2;smt().
call(_: ={glob HRO.ERO, glob S}); [1..2: by sim]. 
call(_:true).    auto;progress. 
if => //. rnd;skip;progress. 

seq 1 1 : (
  ((={BP.setHcheck, valid, BP.vmap, BP.bbstar, BP.r, BP.pk, BP.sk, BP.pi', BP.d, d,
        valid', BP.setchecked, BP.sethappy, BP.bb, glob HRO.ERO, glob C,
        glob S, glob Ve, glob E, glob A, BP.setidents} /\
    rem_ids BP.bb1{1} = G3R.bb{2} /\
    ! ! (BP.setHcheck{1} \subset fdom BP.vmap{1})) /\
   ! !valid{1}) /\
  ! !valid'{1}
).
call(_: ={glob HRO.ERO, glob S, BP.setchecked, BP.setidents, BP.sethappy, BP.vmap, BP.bb}). 
  proc;inline*;auto. progress;smt(). sim. sim. auto;progress. 
sim. 

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
while ( ={i0, bb, e1, e2, glob C, pk, HRO.ERO.m}); first by sim.  
wp. 

(*** We now create BP.bb, where the only difference in the games is      ***)
(*** that on the left side there are two boards, while on the right side ***)
(*** there is only one. The board on the right side should be equal to   ***)
(*** bb1 on the left side.                                               ***)

call(_: ={glob E, glob HRO.ERO, glob S, BP.setidents, BP.setH, BP.pk, BP.sk, BP.secmap, BP.vmap} 
  /\ (rem_ids BP.bb1{1} = G3R.bb{2})
  /\ (BP.pk{1} = getPK BP.sk{1})
).

(*** Vote oracle ***)
proc. 
if => //.  
inline*;wp. 

seq 9 0 : (
  ={id, v0, v1, glob E, glob HRO.ERO, glob S, BP.setidents, BP.setH, BP.pk, BP.sk, BP.secmap, BP.vmap}
  /\ (rem_ids BP.bb1{1} = G3R.bb{2}) /\ (BP.pk{1} = getPK BP.sk{1}) /\ (id{1} \in BP.setH{1})
  /\ id0{1} = id{1} /\ v3{1} = v0{1} /\ id2{1} = id{1}
).

exists* (glob E){1}; elim* => ge. 
call{1} (Ee_eq ge);auto;progress.

seq 11 8 : (
  ={id, v0, v1, glob E, glob HRO.ERO, glob S, BP.setidents, BP.setH, BP.pk, BP.sk, BP.secmap, BP.vmap}
  /\ (rem_ids BP.bb1{1} = G3R.bb{2}) /\ (BP.pk{1} = getPK BP.sk{1}) /\ (id{1} \in BP.setH{1})
  /\ id0{1} = id{1} /\ v3{1} = v0{1} /\ id2{1} = id{1}
  /\ v4{1} = v1{1} /\ v2{2} = v1{2} /\ id3{1} = id{1} /\ id1{2} = id{2} /\ pk0{1} = BP.pk{1} /\ pk{2} = BP.pk{2}
  /\ pc0{1} = pc{2} /\ pc{2} = id{2}
). 

auto;progress. 

exists* BP.sk{1}, pk0{1}, id3{1}, v4{1}. elim* => sk pk id v.  
pose kp := pk = getPK sk. 
have em_kp : kp \/ !kp by exact/orbN. 
elim em_kp. 
move => h. 
call{1} (Eenc_dec sk id v). auto;progress.

move => h.
conseq (_: _ ==> !(BP.pk{1} = getPK BP.sk{1}));first progress. 
call{1} (E_enc_ll HRO.ERO HRO.ERO_o_ll); call{2} (E_enc_ll HRO.ERO HRO.ERO_o_ll). 
auto;progress;smt(). 
proc;inline*;auto. 
proc;inline*;auto.  
conseq So_ll2;progress. 
auto;progress. 
qed.  


(** Proof that the left side IND1CCA experiment using BCCA as adversary is equivalent to G2L **)

local lemma G2L_CCA_left_equiv &m : 
    Pr[G2L(E,Ve,C,A,HRO.ERO,S).main() @ &m : res] = 
    Pr[Ind1CCA(E,BCCA(MV(E,P,Ve,C), A, S), HRO.ERO, Left).main() @ &m : res].
proof. 
byequiv(_: ={glob A, glob C, glob E, glob Ve, glob S, glob G, BP.setidents,
             BP.setHcheck, BP.setH, BP.secmapD, BP.setD}  ==> _) => //. 
proc. 
inline Ind1CCA(E, BCCA(MV(E,P,Ve,C), A,S),HRO.ERO,Left).A.main.
swap{2} [6..11] -5. swap{2} 12 -2. swap{2} [9..10] -2. 
swap{2} 13 -2. swap{2} [8..10] -1. 

(** Up to the point where adversary creates BP.bb, everything is more or less equivalent **)
seq 13 17 : (
    ={glob HRO.ERO, glob S, glob C, glob E, glob Ve, glob A, glob G, BP.pk, 
      BP.setidents, BP.setHcheck, BP.setH, BP.secmapD, BP.setD, BP.sethappy,
      BP.setchecked, BP.vmap, BP.pubmap}
    /\ (G2L.bb{1} = BP.bb'{2})
    /\ (BP.sk{1} = BS.sk{2})
    /\ (BP.pk{2} = BS.pk{2})
    /\ (size BP.bb'{2} = size BS.encL{2})
    /\ (!BS.decQueried{2})
    /\ (forall (id : ident) (b : cipher), (id, b) \in BP.bb'{2} <=> (b, id) \in BS.encL{2})
    /\ (BP.pk{1} = getPK BP.sk{1})
). 
inline*.  
while ( ={i, BP.setidents, BP.secmap, BP.secmapD, BP.setD, BP.setidents, BP.pubmap} ); first by sim. wp. 
swap{2} 16 -2. wp; call (E_kgen_getPK HRO.ERO). call(_:true).  
wp; while (={w, HRO.ERO.m}); first by sim. 
by auto;progress.  

(** The if sentences at the end should also be equivalent **)
seq 7 7 : (
    ={glob HRO.ERO, glob A, glob S, glob G, glob Ve, valid, BP.setidents, 
      BP.setHcheck, BP.vmap, BP.r,  BP.bb, BP.setchecked, BP.sethappy, BP.pk}
    /\ (G2L.bb{1} = BP.bb'{2})
    /\ (BP.sk{1} = BS.sk{2})
); last first. 
wp. 
if => //; first by rnd. 
if => //; first by rnd. 

seq 4 4 : ((={glob HRO.ERO,  glob A, glob S, glob G, glob Ve, valid, valid', BP.setHcheck, BP.bbstar, BP.pk,
       BP.vmap, BP.r, BP.pi, BP.bb, BP.setchecked, BP.sethappy, BP.setidents, d} /\
   ! ! (BP.setHcheck{1} \subset fdom BP.vmap{1})) /\
  ! !valid{1}
  /\ (G2L.bb{1} = BP.bb'{2})
).
inline*. 
wp. 
call(_: ={glob S});first by conseq So_ll2. 
wp. 
call(_: ={glob HRO.ERO, glob S} /\ G2L.bb{1} = BP.bb'{2}); [proc;inline*;auto | sim | sim | progress]. 
call(_: ={glob S, glob HRO.ERO}); [1..2: by sim]. 
call(_:true).  auto;progress. 
by sim. 
(* end of if sentences *)


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
call(_: ={glob C, glob E, glob HRO.ERO, glob S, BP.pk, BP.setH, BP.vmap} 
        /\ (!BS.decQueried{2})
        /\ (G2L.bb{1} = BP.bb'{2}) 
        /\ (BP.pk{1} = BS.pk{2})
        /\ (BP.sk{1} = BS.sk{2})
        /\ (size G2L.bb{1} = size BS.encL{2})
        /\ (forall id b, (id, b) \in BP.bb'{2} <=> (b, id) \in BS.encL{2})
        /\ (BP.pk{1} = getPK BP.sk{1})).
proc. 
if => //. 
inline*.  

seq 9 6 : (
     ={id, v0, v1, glob C, glob E, glob HRO.ERO, glob S, BP.pk, BP.setH, BP.vmap}
     /\ !BS.decQueried{2}
     /\ G2L.bb{1} = BP.bb'{2} 
     /\ BP.pk{1} = BS.pk{2} /\ BP.sk{1} = BS.sk{2}
     /\ (id{1} \in BP.setH{1})
     /\ v0{1} = v{1} /\ p{2} = v0{2} /\ l{2} = id{2} /\ id1{1} = id{1} /\ p{2} = v2{1} /\ id1{1} = l{2}
     /\ c{2} = b1{1}
     /\ (size G2L.bb{1} = size BS.encL{2})
     /\ (forall (id : ident) (b : cipher), (id, b) \in BP.bb'{2} <=> (b, id) \in BS.encL{2})
     /\ (BP.pk{1} = getPK BP.sk{1})
     
).


call(_: ={glob HRO.ERO}); first sim. 
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
byequiv(_: ={glob A, glob C, glob E, glob Ve, glob S,  BP.setidents, 
             BP.setHcheck, BP.setH, BP.secmapD, BP.setD}  ==> _) => //. 
proc. 
inline Ind1CCA(E, BCCA(MV(E,P,Ve,C), A,S),HRO.ERO,Right).A.main.
swap{2} [6..11] -5; swap{2} 12 -2; swap{2} [9..10] -2. 

 
(** Up to the point where adversary creates BP.bb, everything is more or less equivalent **)
seq 12 17 : (
    ={glob HRO.ERO, glob S, glob C, glob E, glob Ve, glob A, BP.pk, 
      BP.setidents, BP.setHcheck, BP.setH, BP.secmapD, BP.setD, BP.sethappy, BP.vmap,
      BP.setchecked, BP.pubmap}
    /\ (G3R.bb{1} = BP.bb'{2})
    /\ (BP.sk{1} = BS.sk{2})
    /\ (BP.pk{2} = BS.pk{2})
    /\ (size BP.bb'{2} = size BS.encL{2})
    /\ (!BS.decQueried{2})
    /\ (forall (id : ident) (b : cipher), (id, b) \in BP.bb'{2} <=> (b, id) \in BS.encL{2})
    /\ (BP.pk{1} = getPK BP.sk{1})
). 
inline*.  
while ( ={i, BP.setidents, BP.secmap, BP.secmapD, BP.setD, BP.pubmap} ).
  by auto.  
wp. 
swap{1} 11 1. 
call(_:true). wp. 
call (E_kgen_getPK HRO.ERO). wp.  
while (={w, HRO.ERO.m}); first by sim. 
auto;progress. 

(** The if sentences at the end should also be equivalent **)
seq 6 7 : (
    ={glob HRO.ERO, glob A, glob S,  glob Ve, valid, BP.setHcheck, 
      BP.r, BP.bb, BP.setchecked, BP.sethappy, BP.pk, BP.vmap, BP.setidents}
    /\ (fdom BP.vmap{1} = fdom BP.vmap{2})
    /\ (G3R.bb{1} = BP.bb'{2})
    /\ (BP.sk{1} = BS.sk{2})
); last first. 

if => //;progress. wp;by rnd. 
if => //. wp; by rnd.  

seq 4 4 : (((={HRO.ERO.m, glob A, glob S, glob Ve, valid, BP.setHcheck, BP.r, BP.vmap,
        BP.bb, BP.setchecked, BP.sethappy, BP.pk, valid', BP.bbstar, d, BP.setidents} /\
    fdom BP.vmap{1} = fdom BP.vmap{2} /\
    G3R.bb{1} = BP.bb'{2} /\ BP.sk{1} = BS.sk{2} /\ BP.pi'{1} = BP.pi{2}) /\
   (BP.setHcheck{1} \subset fdom BP.vmap{1})) /\
  ! !valid{1}
). 
inline*. 
wp. 
call(_: ={glob S});first by conseq So_ll2. 
wp. 
call(_: ={glob HRO.ERO, glob S} /\ G3R.bb{1} = BP.bb'{2}); [proc;inline*;auto | sim | sim | progress].
call(_: ={glob S, glob HRO.ERO}); [1..2: by sim]. 
call(_:true). auto;progress. 

if => //.  wp;rnd. auto;progress. 

seq 1 1 : ((((={HRO.ERO.m, glob A, glob S,  glob Ve, valid, BP.setHcheck, BP.r, BP.vmap, d,
         BP.bb, BP.setchecked, BP.sethappy, BP.pk, valid', BP.bbstar, BP.d, BP.setidents} /\
     fdom BP.vmap{1} = fdom BP.vmap{2} /\
     G3R.bb{1} = BP.bb'{2} /\ BP.sk{1} = BS.sk{2} /\ BP.pi'{1} = BP.pi{2}) /\
    (BP.setHcheck{1} \subset fdom BP.vmap{1})) /\
   ! !valid{1}) /\
  ! !valid'{1}).

call(_: ={glob HRO.ERO, glob S, BP.setchecked, BP.sethappy, BP.bb, BP.vmap, BP.bbstar, BP.setidents}).   
+ proc;inline*;auto. progress. 
  + by rewrite /Flabel /idfun in H0.  
  + by rewrite/Flabel /idfun in H0.
  + by rewrite /Flabel /idfun in H0.
  + by rewrite /Flabel /idfun in H0.
+ sim. sim. auto;progress.  
wp. sim.  

(* end of if sentences *)


wp;rnd. 
inline*. 
(** tally while loop **) 
 
while ( ={j, BP.bb, dbb, BP.vmap, glob HRO.ERO} /\ (0 <= j{2})
     /\ (BP.sk{1} = BS.sk{2})
     /\ (BP.pk{1} = BS.pk{2})
     /\ (G3R.bb{1} = BP.bb'{2})
     /\ (mL{2} = map (fun (ci : cipher * ident) => 
                 if !( (ci.`2, ci.`1) \in BP.bb'{2} ) 
                then dec_cipher BS.sk{2} ci.`2 ci.`1 HRO.ERO.m{2}
                else None) (flip BP.bb{2}))). 

wp;sp. if{1}. wp;skip;progress. rewrite -H. smt(). smt(). rewrite -H. smt(). smt().
exists* (glob E){1}, BP.sk{1}, idl{1}, b{1}. elim* => ge sk idl b. 
call{1} (Edec_Odec ge sk idl b). auto;progress. smt(). smt(). 
      do 3! congr. smt(). rewrite (nth_map witness witness _ j{2} _) . smt(@List).
      have ? : (b{1}, idl{1}) = nth witness (flip BP.bb{2}) j{2}. smt(@List). smt(). smt(). 

swap{2} [14..15] -5. 
rcondt{2} 14;progress. 
wp;while (0 <= i0 <= size bb);wp;sp. 
if => //. 
call(_:true); first by auto. 
auto;progress;smt(). 
auto;progress;smt(). 
wp;call(_:true);auto. 
progress.
wp. 

while{2} (0 <= i1{2} <= size cL{2} 
         /\ mL0{2} = map (fun (ci : cipher * ident) =>
            if !(ci \in BS.encL{2})
            then dec_cipher BS.sk{2} ci.`2 ci.`1 HRO.ERO.m{2} 
            else None) (take i1{2} cL{2})) 
(size cL{2} - i1{2}).

progress. wp;sp. 
exists* (glob E), c0, l, BS.sk{hr}. elim* => ge c l sk.  
call{1} (Edec_Odec ge sk l c).  
auto =>/>; progress.
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
call(_: ={glob C, glob E, glob HRO.ERO, glob S, BP.pk, BP.setH, BP.vmap} /\ (!BS.decQueried{2})
          /\ (G3R.bb{1} = BP.bb'{2}) 
          /\ (BP.pk{1} = BS.pk{2})
          /\ (BP.sk{1} = BS.sk{2})
          /\ (size G3R.bb{1} = size BS.encL{2})
          /\ (forall (id : ident) (b : cipher), (id, b) \in BP.bb'{2} <=> (b, id) \in BS.encL{2})
          /\ (BP.pk{1} = getPK BP.sk{1})
).
proc. 
if => //. 
inline*.  
wp.    
seq 9 6 : ( ={ id, v0, v1, glob C, glob E, glob HRO.ERO, glob S, BP.pk, BP.setH, BP.vmap}
            /\ !BS.decQueried{2}
            /\ G3R.bb{1} = BP.bb'{2} 
            /\ BP.pk{1} = BS.pk{2} /\ BP.sk{1} = BS.sk{2}
            /\ (id{1} \in BP.setH{1})
            /\ v1{1} = v{1} /\ p{2} = v1{2} /\ l{2} = id{2} 
            /\ id1{1} = id{1} /\ p{2} = v2{1} /\ id1{1} = l{2}
            /\ c{2} = b0{1}
            /\ (size G3R.bb{1} = size BS.encL{2})
            /\ (forall id b, (id, b) \in BP.bb'{2} <=> (b, id) \in BS.encL{2})
            /\ (BP.pk{1} = getPK BP.sk{1})).
  + call(_: ={glob HRO.ERO}); first sim. 
    by auto. 
  auto =>/>;progress. 
  + smt(size_cat).
  + smt(mem_cat).  
  + smt(mem_cat).

+ by proc. 
+ by proc.
+ by conseq So_ll2. 

auto=>/>;progress.  
+ by rewrite size_ge0. 
+ by rewrite take0 //=. 
+ smt(). 
+ do 1! congr. 
  + rewrite fun_ext /(==); move => x. 
    by rewrite (H3 x.`2 x.`1) //=; smt().
  have ->: i1_R = size (flip result_R) by smt(). 
  by rewrite take_size. 
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
local lemma DU_MB_BPRIV_R_G3R_equiv  &m : 
  BP.setidents{m} = BP.setH{m} `|` BP.setD{m} =>
    Pr[DU_MB_BPRIV_R(MV(E,P,Ve,C),A,HRO.ERO,G,S,Recover').main() @ &m : res] 
     = Pr[G3R(E,P,Ve,C,A,HRO.ERO,S).main() @ &m : res]. 
proof.
move => IHD.  
by rewrite -G2R_G3R_equiv -G1R_G2R_equiv  -(G0R_G1R_equiv &m IHD) 
           -G0R'_G0R_equiv (DU_MB_BPRIV_R_G0'_R_equiv &m HRO.ERO).  
qed.  

local lemma MB_BPRIV_L_G1L_equiv &m : 
    Pr[DU_MB_BPRIV_L(MV(E,P,Ve,C),A,HRO.ERO,G).main() @ &m : res] = 
    Pr[G0L(E,P,Ve,C,A,HRO.ERO,G).main() @ &m : res]. 
proof. 
by rewrite (DU_MB_BPRIV_L_G0L'_equiv &m HRO.ERO) G0L'_G0L_equiv. 
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
lemma du_mb_bpriv &m :
  BP.setidents{m} = BP.setH{m} `|` BP.setD{m} => 
 `|Pr[DU_MB_BPRIV_L(MV(E,P,Ve,C),A,HRO.ERO,G).main() @ &m : res] 
   - Pr[DU_MB_BPRIV_R(MV(E,P,Ve,C),A,HRO.ERO,G,S,Recover').main() @ &m : res]|
   <=  
     Pr[VFR(E, BVFR(MV(E,P,Ve,C), A), R(E), HRO.ERO, G).main() @ &m : res] 
   + Pr[VFR(E, BVFR(MV(E,P,Ve,C), A), R(E), HRO.ERO, S).main() @ &m : res] 
   + `|Pr[ZK_L(R(E,HRO.ERO), P, BZK(E,P,C,Ve,A,HRO.ERO), G).main() @ &m : res] 
       -  Pr[ZK_R(R(E,HRO.ERO), S, BZK(E,P,C,Ve,A,HRO.ERO)   ).main() @ &m : res]|
   + `|Pr[Ind1CCA(E,BCCA(MV(E,P,Ve,C),A,S),HRO.ERO,Left).main() @ &m : res] 
       -  Pr[Ind1CCA(E,BCCA(MV(E,P,Ve,C),A,S),HRO.ERO,Right).main() @ &m : res]|.
proof. 

(* add and subtract G1L to first abs value *)
have -> :  `|Pr[DU_MB_BPRIV_L(MV(E,P,Ve,C),A,HRO.ERO,G).main() @ &m : res] - 
             Pr[DU_MB_BPRIV_R(MV(E,P,Ve,C),A,HRO.ERO,G,S,Recover').main() @ &m : res]| = 
             `|Pr[DU_MB_BPRIV_L(MV(E,P,Ve,C),A,HRO.ERO,G).main() @ &m : res] - 
               Pr[G1L(E,Ve,C,A,HRO.ERO,S).main() @ &m : res] +
            Pr[G1L(E,Ve,C,A,HRO.ERO,S).main() @ &m : res] - 
            Pr[DU_MB_BPRIV_R(MV(E,P,Ve,C),A,HRO.ERO,G,S,Recover').main() @ &m : res]| by smt(@Real). 
(* triangle inequality *)
have ? : `|Pr[DU_MB_BPRIV_L(MV(E, P, Ve, C), A, HRO.ERO, G).main() @ &m : res] - 
           Pr[G1L(E, Ve, C, A, HRO.ERO, S).main() @ &m : res] +
           Pr[G1L(E, Ve, C, A, HRO.ERO, S).main() @ &m : res] - 
           Pr[DU_MB_BPRIV_R(MV(E, P, Ve, C), A, HRO.ERO, G, S, Recover').main() @ &m : res]| <=
         `|Pr[DU_MB_BPRIV_L(MV(E, P, Ve, C), A, HRO.ERO, G).main() @ &m : res] - 
           Pr[G1L(E, Ve, C, A, HRO.ERO, S).main() @ &m : res]| +
         `|Pr[G1L(E, Ve, C, A, HRO.ERO, S).main() @ &m : res] - 
           Pr[DU_MB_BPRIV_R(MV(E, P, Ve, C), A, HRO.ERO, G, S, Recover').main() @ &m : res]| by smt(@Real). 
by smt.
qed.

end section DU_MB_BPRIV. 
