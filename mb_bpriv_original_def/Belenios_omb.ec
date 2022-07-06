require import Int Bool Real SmtMap FSet Distr Core. 
require import List LeftOrRight Finite. 
require (*  *) DiffieHellman MiniVotingSecurity_omb.


(* get group and field elements *)
clone import DiffieHellman as DH.


(*** Labelled Public-Key Encryption Scheme
     = abstract encryption scheme + abstract proof system ***)

 
  (* ** abstract  encryption scheme *)
  (* Types and operators *)
  type skey = F.t.
  type pkey = group.
  type ctxt.
  type ptxt = group.

  (* abstract encryption scheme algorithms *)
  op getPK   : skey -> pkey.
  op decrypt : skey -> ctxt -> ptxt option.
  op encrypt : pkey -> ptxt -> F.t -> ctxt.

  axiom correctness (sk: skey) (p: ptxt) (r: F.t):
    decrypt sk (encrypt (getPK sk) p r) = Some p.

  (* ** abstract proof system *)
  (* this is why we need type label = unit. *)
  type ident.
  type label = ident.
  type h_stm, h_wit, h_prf, h_in, h_out.
  type cipher = ctxt * h_prf.
  
  op dh_out: h_out distr.
  axiom dh_out_ll  : is_lossless dh_out. 
  axiom h_in_finite: is_finite predT<: h_in>. 

  (* abstract operators *)
  op verify : h_stm -> h_prf -> (h_in, h_out) fmap -> bool.
  op to_stm : pkey  -> label -> ctxt -> h_stm.
  op to_wit : ptxt  -> t     -> h_wit.

  clone export ProofSystem as PSpke with
    type stm   <- h_stm,
    type wit   <- h_wit,
    type prf   <- h_prf,
    type g_in  <- h_in,
    type g_out <- h_out,
    op dout    <- dh_out
    proof *.


(* ---------------------------------------------------------------------- *)
(* Belenios from Minivoting *)

op n : { int | 0 < n } as n_pos.

(* decryption operator *)
op dec_cipher (sk: skey, lbl: label, c: cipher, ro: (h_in, h_out) fmap)
   = let s = to_stm (getPK sk) lbl c.`1 in 
     if(verify s c.`2 ro) 
       then (decrypt sk c.`1)
       else None.

(* lexicographic count function *)

 (* def some order *)
 op (<=): ptxt -> ptxt -> bool.

 (* the policy is laready defined in MiniVotingDefinition *)
 op Count (x: ptxt list): (ptxt list) distr
   = MUnit.dunit (sort (<=) x). 

 op Publish (x: (ident* cipher) list) = x.

(* last vote policy : keep vote option*)
op Policy['a] (L: (ident * 'a) list): 'a list =
    with L = "[]"          => []
    with L = (::) idv L => if has ((\o) (pred1 idv.`1) fst) L
                               then Policy L
                               else idv.`2 :: Policy L.

(* remove invalid votes *) 
op valid['a] (x: ('a option) list): 'a list
   = pmap idfun x. 

(* Rho operator *)
op Rho (L : (ident * ptxt option) list): (ptxt list) distr
   = Count (valid  (Policy L)).

clone export MiniVotingSecurity_omb as MV2 with
  type ident         <- ident,  
  type vote          <- ptxt,  
  type pubcred       <- ident,
  type ballot        <- cipher,
  (* use LPKE types *)
  type cipher        <- cipher, 
  type pkey          <- pkey,   
  type skey          <- skey,   
  type h_in          <- h_in,   
  type h_out         <- h_out,
  type result        <- ptxt list,
  type pubBB         <- (ident * cipher) list,
  op dh_out          <- dh_out,        
  op dec_cipher      <- dec_cipher,        
  op extractPk       <- getPK,
  op Rho             <- Rho,
  op Publish         <- Publish
  proof is_finite_h_in, distr_h_out.
    realize is_finite_h_in by rewrite h_in_finite. 
    realize distr_h_out by rewrite dh_out_ll. 



(* Labelled Public-Key Encryption Scheme  *)
  module (IPKE(P: PSpke.Prover, Ve: PSpke.Verifier): Scheme) (O:HOracle.POracle) = {
    
    proc kgen(): pkey * skey ={
      var sk; 

      sk <$ FDistr.dt; 
      return (getPK sk, sk);
    }

    proc enc(pk: pkey, lbl: label, p: ptxt) : cipher ={
      var r, c, pi;

      r <$ FDistr.dt; 
      c <- encrypt pk p r;
      pi<@ P(O).prove((to_stm pk lbl c), (to_wit p r) );

      return (c, pi);
    }

    proc dec(sk: skey, lbl: label, c: cipher) : ptxt option = {
      var ev, m;

      m <- None; 
      ev <@ Ve(O).verify((to_stm (getPK sk) lbl c.`1), c.`2);
      if (ev){
        m <- decrypt sk c.`1;
      }
      return m;   
    }
    
  }.

 (* vadliInd checks the proof *)
 module (CV (Ve: PSpke.Verifier) :ValidInd) (O:HOracle.POracle) ={
   proc validInd (b: ident* label * cipher, pk: pkey): bool ={
   var ev;
   
   ev <@ Ve(O).verify((to_stm pk b.`2 b.`3.`1), b.`3.`2);
   return ev;
   }
 }.

(* Belenios wth mixnets *)
(* due to C and E not allowed to share state, we need to consider 2 diff Verifiers Ve and Vc *)
module (Belenios (Pe: PSpke.Prover, Ve: PSpke.Verifier, Vc: PSpke.Verifier, 
                Pz: Prover,  Vz: Verifier): VotingSystem)
               (H: HOracle.POracle,  G: GOracle.POracle) 
   = MV(IPKE(Pe,Ve), Pz, Vz, CV(Vc), H, G).

  


section MB_BPRIV. 

declare module Pe <: PSpke.Prover    { -BP, -HRO.ERO, -BPS, -BS, -PKEvf.H.Count, -PKEvf.H.HybOrcl, -WrapAdv }.
declare module Ve <: PSpke.Verifier  { -BP, -HRO.ERO, -BPS, -BS, -PKEvf.H.Count, -PKEvf.H.HybOrcl, -WrapAdv, -Pe }.
declare module Vc <: PSpke.Verifier  { -BP, -HRO.ERO, -BPS, -BS, -Pe, -Ve }.

declare module G  <: GOracle.Oracle  { -BP, -HRO.ERO, -BPS, -BS, -Pe, -Ve, -Vc }.
declare module S  <: Simulator       { -BP, -HRO.ERO, -BPS, -BS, -PKEvf.H.Count, -PKEvf.H.HybOrcl, -WrapAdv, 
                                       -Pe, -Ve, -Vc, -G }. 
declare module Vz <: Verifier        { -BP, -HRO.ERO, -BPS, -BS, -Pe, -Ve, -Vc, -G, -S }. 
declare module Pz <: Prover          { -BP, -HRO.ERO, -BPS, -BS, -Pe, -Ve, -Vc, -G, -S, -Vz }. 
declare module R  <: VotingRelation' { -BP, -HRO.ERO, -BPS, -BS, -Pe, -Ve, -Vc, -G, -S, -Vz, -Pz }. 
 
declare module A  <: OMB_BPRIV_adv   { -BP, -HRO.ERO, -BPS, -BS, -Pe, -Ve, -Vc, -G, -S, -Vz, -Pz, -R }. 

(**** Lossless assumptions ****)

(** Oracles **)
declare axiom Gi_ll : islossless G.init. 
declare axiom Go_ll : islossless G.o. 

(** MB-BPRIV adversary **)
declare axiom A_a1_ll (O <: MB_BPRIV_oracles { -A }):
  islossless O.vote => 
  islossless O.board => 
  islossless O.h => 
  islossless O.g => 
  islossless A(O).a1. 

declare axiom A_a2_ll (O <: MB_BPRIV_oracles { -A }): 
  islossless O.board => 
  islossless O.h => 
  islossless O.g => 
  islossless A(O).a2.
 
declare axiom A_a3_ll (O <: MB_BPRIV_oracles { -A }): 
  islossless O.verify => 
  islossless O.h => 
  islossless O.g => 
  islossless A(O).a3. 

declare axiom A_a4_ll (O <: MB_BPRIV_oracles { -A }): 
  islossless O.h => 
  islossless O.g => 
  islossless A(O).a4. 

declare axiom A_a5_ll (O <: MB_BPRIV_oracles { -A }):
  islossless O.board => 
  islossless O.h => 
  islossless O.g => 
  islossless A(O).a5. 

(** Main Proof system **)
declare axiom PS_p_ll (G <: GOracle.POracle { -Pz }) : 
  islossless G.o => islossless Pz(G).prove. 
declare axiom PS_v_ll (G <: GOracle.POracle { -Vz }) : 
  islossless G.o => islossless Vz(G).verify. 

(** Enc Proof system **)
declare axiom PE_p_ll (H <: HOracle.POracle { -Pe }) : 
  islossless H.o => islossless Pe(H).prove. 
declare axiom PE_v_ll (H <: HOracle.POracle { -Ve }) : 
  islossless H.o => islossless Ve(H).verify.
declare axiom PE_c_ll (H <: HOracle.POracle { -Vc }) : 
  islossless H.o => islossless Vc(H).verify.

(** ZK simulator **)
declare axiom Si_ll : islossless S.init. 
declare axiom So_ll : islossless S.o. 
declare axiom Sp_ll : islossless S.prove. 

(** VFR **)
declare axiom R_m_ll : islossless R(IPKE(Pe,Ve),HRO.ERO).main. 

(*** Voting relation does not change state of eager random oracle ***)
declare axiom relConstraint (gh : (glob HRO.ERO)):
    phoare[ R(IPKE(Pe,Ve),HRO.ERO).main : 
          (glob HRO.ERO) = gh ==> (glob HRO.ERO) = gh] = 1%r. 

(* axiom for keep same state of Ve in Ve.verify *)
declare axiom PS_v_verify2 (gv: (glob Ve)) (s: h_stm) (p: h_prf):
    hoare[Ve(HRO.ERO).verify: (glob Ve) = gv /\ arg = (s, p)
         ==>
         (glob Ve) = gv
         /\ res=verify s p HRO.ERO.m].
local lemma PS_v_verify (gv: (glob Ve)) (s: h_stm) (p: h_prf):
    phoare[Ve(HRO.ERO).verify: (glob Ve) = gv /\ arg = (s, p)
         ==>
         (glob Ve) = gv
         /\ res=verify s p HRO.ERO.m] = 1%r.
proof.
   by conseq (PE_v_ll HRO.ERO HRO.ERO_o_ll) (PS_v_verify2 gv s p) => />. 
qed.

(* axiom for keep same state of Pe in Pe.prove *)
declare axiom PS_p_verify2 (gv: (glob Pe)) (s: h_stm) (w: h_wit):
  hoare[Pe(HRO.ERO).prove: 
    (glob Pe) = gv /\ arg = (s,w)
     ==>
     (glob Pe) = gv
     /\ verify s res HRO.ERO.m].

(* axiom for keep same state of Pe in Pe.prove *)
local lemma PS_p_verify (gv: (glob Pe)) (s: h_stm) (w: h_wit):
  phoare[Pe(HRO.ERO).prove: 
    (glob Pe) = gv /\ arg = (s,w)
     ==>
     (glob Pe) = gv
     /\ verify s res HRO.ERO.m] = 1%r.
proof.
 by conseq (PE_p_ll HRO.ERO HRO.ERO_o_ll) (PS_p_verify2 gv s w) => />. 
qed.


declare axiom PS_p_verify_both (s: h_stm) (w: h_wit):
  equiv[Pe(HRO.ERO).prove ~ Pe(HRO.ERO).prove: 
   ={glob HRO.ERO, glob Pe, arg} /\ arg{1} = (s, w)
   ==>
   ={glob HRO.ERO, glob Pe, res}
   /\ verify s res{1} HRO.ERO.m{1}].



(** Encryption **)
local lemma E_kg_ll  (H <: HOracle.POracle ) : 
  islossless H.o => islossless IPKE(Pe,Ve,H).kgen.
proof.
  move => Ho_ll. 
  proc.
  by auto=>/>; rewrite FDistr.dt_ll.
qed.

local lemma E_enc_ll (H <: HOracle.POracle { -Pe }) : 
  islossless H.o => islossless IPKE(Pe,Ve, H).enc. 
proof.
  move => Ho_ll.
  proc.  
  call (PE_p_ll H Ho_ll).
  by auto=>/>; rewrite FDistr.dt_ll.
qed.

local lemma E_dec_ll (H <: HOracle.POracle) : 
  islossless H.o => islossless IPKE(Pe,Ve,H).dec. 
proof.
  move => Ho_ll; proc.
  wp; call (PE_v_ll H Ho_ll).  
  by wp.
qed.
 

(** ValidInd operator **)
local lemma C_vi_ll (H <: HOracle.POracle { -Vc }) : 
  islossless H.o => islossless CV(Vc,H).validInd. 
proof.
  move => Ho_ll; proc. 
  by call (PE_c_ll H Ho_ll).
qed.
  

(*** result distribution ***)
local lemma Rho_weight (x: (ident * ptxt option) list):
  weight (Rho x) = 1%r
  by rewrite /Rho dunit_ll.

(*** linking key generation and extractPk operator ***)
local lemma E_kgen_extractpk (H <: HOracle.POracle ):
 equiv [IPKE(Pe,Ve,H).kgen ~ IPKE(Pe,Ve,H).kgen : ={glob H, glob IPKE(Pe,Ve)} 
        ==> ={glob H, glob  IPKE(Pe,Ve), res} /\ res{1}.`1 = getPK res{1}.`2] 
  by proc; auto.

(*  stating that the keys are generated *)
local lemma Ekgen_extractPk (H<: HOracle.POracle ):
  equiv [IPKE(Pe,Ve, H).kgen ~ IPKE(Pe,Ve,H).kgen:  
    ={glob H, glob IPKE(Pe,Ve)}
    ==>
      ={ glob H, glob IPKE(Pe,Ve),  res}  
      /\  res{1}.`1 = getPK res{1}.`2  
      /\  res{1}.`1 = getPK res{1}.`2 ]
  by proc; auto.

local lemma Ekgen_extractPk2  (H <: HOracle.POracle):
    hoare[ IPKE(Pe, Ve, H).kgen : true ==> res.`1 = getPK res.`2]
  by proc; auto. 

(* linking E.dec to dec_cipher operator *)   
local lemma Edec_Odec (ge: (glob IPKE(Pe,Ve))) (sk2: skey)(l2: ident) (c2: cipher):
  phoare [IPKE(Pe,Ve,HRO.ERO).dec:  
    (glob IPKE(Pe,Ve)) =ge /\ arg = (sk2, l2, c2)
     ==>   
      (glob IPKE(Pe,Ve)) =ge /\
       res = dec_cipher sk2 l2 c2 HRO.ERO.m ] = 1%r.
proof.
  proc.
  swap 2 -1.
  wp. 
  call (PS_v_verify ge.`1 (to_stm (getPK sk2) l2 c2.`1) c2.`2). 
  auto =>/> &hr.
  split.  
  + by move => Hv; rewrite /dec_cipher //= Hv. 
  by move => Hnv; rewrite /dec_cipher //= Hnv.
qed.

(* linking E.dec to dec_cipher operator *)   
local lemma Edec_Odec2 (ge: (glob IPKE(Pe,Ve))) (sk2: skey)(l2: ident) (c2: cipher):
  hoare [IPKE(Pe,Ve,HRO.ERO).dec:  
    (glob IPKE(Pe,Ve)) =ge /\ arg = (sk2, l2, c2)
     ==>   
      (glob IPKE(Pe,Ve)) =ge /\
       res = dec_cipher sk2 l2 c2 HRO.ERO.m ].
proof.
  proc. 
  swap 2 -1.
  wp. 
  call (PS_v_verify2 ge.`1 (to_stm (getPK sk2) l2 c2.`1) c2.`2). 
  auto =>/> &hr.
  split.  
  + by move => Hv; rewrite /dec_cipher //= Hv. 
  by move => Hnv; rewrite /dec_cipher //= Hnv.
qed.

(* state of the encryption scheme E *)
local lemma Ee_eq (ge: (glob IPKE(Pe,Ve))):
  phoare [IPKE(Pe,Ve, HRO.ERO).enc: 
    (glob IPKE(Pe,Ve)) = ge ==> (glob IPKE(Pe,Ve)) = ge] = 1%r.
proof. 
  proc.
  wp. 
  seq 2: (((glob Ve), (glob Pe)) = ge) =>//=.
  + by wp; rnd; skip; rewrite FDistr.dt_ll.
  + exists* pk, lbl, c, p, r; elim* => pk l c p r. 
    call (PS_p_verify ge.`2 (to_stm pk l c) (to_wit p r )). 
    by wp. 
  by hoare; auto =>/>; rewrite FDistr.dt_ll.
qed.

local lemma Ee_eq2 (ge: (glob IPKE(Pe,Ve))):
  hoare [IPKE(Pe,Ve, HRO.ERO).enc: 
    (glob IPKE(Pe,Ve)) = ge ==> (glob IPKE(Pe,Ve)) = ge].
proof. 
  proc.
  wp. 
  seq 2: (((glob Ve), (glob Pe)) = ge) =>//=.
  + by wp; rnd; skip; progress.
  + exists* pk, lbl, c, p, r; elim* => pk l c p r. 
    call (PS_p_verify2 ge.`2 (to_stm pk l c) (to_wit p r )). 
    by wp. 
qed.
    
(* transforming an encryption into decryption (one-sided) *)
local lemma Eenc_decL (ge: (glob IPKE(Pe,Ve))) (sk2: skey) 
                (pk2: pkey)(l2: ident) (p2: ptxt): 
  (pk2 = getPK sk2) =>
   phoare [IPKE(Pe,Ve,HRO.ERO).enc : 
     (glob IPKE(Pe,Ve)) = ge /\ arg=(pk2, l2, p2) 
      ==> 
       (glob IPKE(Pe,Ve))  = ge
       /\ Some p2 = dec_cipher sk2 l2 res HRO.ERO.m ]= 1%r. 
proof.
  move => Hk; proc.  
  wp. 
  seq 2: (((glob Ve), (glob Pe)) = ge
          /\ (pk, lbl, p) = (pk2, l2,p2)
          /\ c = encrypt pk2 p2 r) =>//=.
  + by auto=>/>; rewrite FDistr.dt_ll.
  + exists* r; elim* => r. 
    call (PS_p_verify ge.`2 (to_stm pk2 l2 (encrypt pk2 p2 r)) 
             (to_wit p2 r )). 
    auto=>/> &hr b Hv. 
    by rewrite /dec_cipher //= -Hk Hv //= Hk correctness. 
  by hoare; auto =>/>; rewrite FDistr.dt_ll.
qed.

local lemma Eenc_decL2 (ge : (glob IPKE(Pe, Ve))) (sk2 : skey) (l2 : label) (p2 : ptxt):
    hoare[ IPKE(Pe, Ve, HRO.ERO).enc :
            (glob IPKE(Pe, Ve)) = ge /\ arg = (getPK sk2, l2, p2) ==>
            (glob IPKE(Pe, Ve)) = ge /\
            Some p2 = dec_cipher sk2 l2 res HRO.ERO.m].
proof.
  proc.  
  wp. 
  seq 2: (((glob Ve), (glob Pe)) = ge
          /\ (pk, lbl, p) = (getPK sk2, l2,p2)
          /\ c = encrypt pk p2 r) =>//=.
  + by auto=>/>; rewrite FDistr.dt_ll.
  + exists* r; elim* => r. 
    call (PS_p_verify2 ge.`2 (to_stm  (getPK sk2) l2 (encrypt (getPK sk2) p2 r)) 
             (to_wit p2 r )). 
    auto=>/> &hr b Hv. 
    by rewrite /dec_cipher //=  Hv //= correctness. 
qed.

(* transforming an encryption into decryption (two-sided) *)
local lemma Eenc_dec (sk2: skey) (pk2: pkey) (l2: ident) (p2: ptxt): 
  (pk2 = getPK sk2) =>
  equiv [IPKE(Pe,Ve,HRO.ERO).enc ~ IPKE(Pe,Ve,HRO.ERO).enc : 
    ={glob HRO.ERO, glob IPKE(Pe,Ve), arg} /\ arg{1}=( pk2, l2, p2) 
    ==> 
      ={glob HRO.ERO, glob IPKE(Pe,Ve),  res}
      /\ Some p2 = dec_cipher sk2 l2 res{1} HRO.ERO.m{1}].   
proof.
  move => Hk; proc.
  seq 2 2: ( ={ glob Ve, glob Pe, HRO.ERO.m, pk, lbl, p, r, c}
            /\ (pk{1}, lbl{1}, p{1}) = (pk2,l2,p2)
            /\ c{1} = encrypt pk2 p2 r{1}) =>//=.
  + by auto. 
  exists* r{1}; elim* => r. 
  call (PS_p_verify_both (to_stm pk2 l2 (encrypt pk2 p2 r)) 
               (to_wit p2 r )). 
  auto=>/> &2 prf Hv. 
  by rewrite /dec_cipher //= -Hk Hv Hk correctness. 
qed. 

local lemma Eenc_dec2 (ge : (glob IPKE(Pe, Ve))) (sk2 : skey) (l2 : label) (p2 : ptxt):
  hoare[ IPKE(Pe, Ve, HRO.ERO).enc :
            (glob IPKE(Pe, Ve)) = ge /\ arg = (getPK sk2, l2, p2) ==>
            (glob IPKE(Pe, Ve)) = ge /\
            Some p2 = dec_cipher sk2 l2 res HRO.ERO.m].
proof.
  proc.
  wp. 
  seq 2: (((glob Ve), (glob Pe)) = ge
          /\ (pk, lbl, p) = (getPK sk2, l2,p2)
          /\ c = encrypt pk p2 r) =>//=.
  + by auto=>/>; rewrite FDistr.dt_ll.
  + exists* r; elim* => r. 
    call (PS_p_verify2 ge.`2 (to_stm  (getPK sk2) l2 (encrypt (getPK sk2) p2 r)) 
             (to_wit p2 r )). 
    auto=>/> &hr b Hv. 
    by rewrite /dec_cipher //=  Hv //= correctness. 
qed. 
  
lemma mb_bpriv &m :
  BP.setidents{m} = BP.setH{m} `|` BP.setD{m}
  => 
  `|Pr[OMB_BPRIV_L(Belenios (Pe,Ve,Vc,Pz,Vz),A,HRO.ERO,G).main() @ &m : res] 
    - Pr[OMB_BPRIV_R(Belenios (Pe,Ve,Vc,Pz,Vz),A,HRO.ERO,G,S,Recover').main() @ &m : res]|
   <=  
   Pr[VFR(IPKE(Pe,Ve), BVFR(MV(IPKE(Pe,Ve),Pz,Vz,CV(Vc)), A), 
          R(IPKE(Pe,Ve)), HRO.ERO, G).main() @ &m : res] 
 + Pr[VFR(IPKE(Pe,Ve), BVFR(MV(IPKE(Pe,Ve),Pz,Vz,CV(Vc)), A), 
          R(IPKE(Pe,Ve)), HRO.ERO, S).main() @ &m : res] 
 + `|Pr[ZK_L(R(IPKE(Pe,Ve),HRO.ERO), Pz, 
            BZK(IPKE(Pe,Ve),Pz,CV(Vc),Vz,A,HRO.ERO), G).main() @ &m : res] 
     - Pr[ZK_R(R(IPKE(Pe,Ve),HRO.ERO), S, 
               BZK(IPKE(Pe,Ve),Pz,CV(Vc),Vz,A,HRO.ERO)   ).main() @ &m : res]|
   + `|Pr[Ind1CCA(IPKE(Pe,Ve), BCCA(MV(IPKE(Pe,Ve),Pz,Vz,CV(Vc)),A,S),
                  HRO.ERO,Left).main() @ &m : res]  
       - Pr[Ind1CCA(IPKE(Pe,Ve),BCCA(MV(IPKE(Pe,Ve),Pz,Vz,CV(Vc)),A,S),
                  HRO.ERO,Right).main() @ &m : res]|.
proof. 
  move => IHD.
  have ->: Pr[OMB_BPRIV_L(Belenios (Pe,Ve,Vc,Pz,Vz),A,HRO.ERO,G).main() @ &m : res]
  = Pr[OMB_BPRIV_L(MV(IPKE(Pe, Ve),Pz,Vz,CV(Vc)), A, HRO.ERO, G).main() @ &m : res]
    by byequiv =>/>; sim.

  have->: Pr[OMB_BPRIV_R(Belenios (Pe,Ve,Vc,Pz,Vz),A,HRO.ERO,G,S,Recover').main() @ &m : res]
  = Pr[OMB_BPRIV_R(MV(IPKE(Pe, Ve), Pz, Vz, CV(Vc)), A, HRO.ERO, G, S, Recover').main() @ &m : res]
    by byequiv =>/>; sim.

  rewrite (mb_bpriv G (IPKE(Pe,Ve)) S Vz Pz R (CV(Vc)) A Gi_ll Go_ll A_a1_ll A_a2_ll 
               A_a3_ll A_a4_ll A_a5_ll PS_p_ll PS_v_ll _ _ _ Si_ll So_ll 
               Sp_ll R_m_ll C_vi_ll Rho_weight E_kgen_extractpk relConstraint 
               Ekgen_extractPk Edec_Odec Ee_eq Eenc_decL Eenc_dec2 Ee_eq2 &m IHD). 
  + by move=> H H_o_ll; exact: (E_kg_ll H).
  + by move=> H H_o_ll; exact: (E_enc_ll H).
  by move=> H H_o_ll; exact: (E_dec_ll H).
qed.

end section MB_BPRIV. 
