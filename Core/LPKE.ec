require import Int Bool Real.
require import Distr List.
require import LeftOrRight.
require (*  *) ROM.

(* * Preliminaries *)
(* ---------------------------------------------------------------------- *)

(* types *)
type label.       (* label *)
type plain.       (* plaintext *)
type cipher.      (* ciphertext *)
type pkey.        (* public key *)
type skey.        (* secret key *)
type h_in, h_out. (* input and output for random oracle *)

op dout: h_out distr. (* random oracle distribution *)

(* random oracle *)
clone include ROM with
  type in_t           <- h_in,
  type out_t          <- h_out,
  op   dout(x : h_in) <- dout. 

(* * Definitions *)
(* ---------------------------------------------------------------------- *)

(* encryption scheme *)
module type Scheme(O : POracle) = {
  proc kgen()                          : pkey * skey  {   } 
  proc enc(pk:pkey, l:label, p:plain)  : cipher       {O.o}
  proc dec(sk:skey, l:label, c:cipher) : plain option {O.o}
}.

(* * Correctnes *)
(* ---------------------------------------------------------------------- *)

(* Correctness experiment *)
module Correctness (S: Scheme, O: Oracle) = {
  module S = S(O)
  proc main(p : plain, l : label) : bool ={
    var pk, sk, c, p';
               O.init();
    (pk,sk) <@ S.kgen();
    c       <@ S.enc(pk,l,p);
    p'      <@ S.dec(sk,l,c);
    return (p' = Some p);
  }
}.

(* * Ind-1-CCA security definitions *)
(* ---------------------------------------------------------------------- *)

(* IND-1-CCA oracles type *)
module type Ind1CCA_Oracles = {
  proc o(x: h_in)                      : h_out 
  proc enc(l : label, p0 p1 : plain)   : cipher
  proc dec(cL : (cipher * label) list) : plain option list 
}.

(* IND-1-CCA adversary *)
module type Ind1CCA_Adv(IO : Ind1CCA_Oracles) = {
  proc main (pk : pkey) : bool {IO.enc, IO.dec, IO.o} 
}.

(* Global state shared between IND-1-CCA oracles and game *)
module BS = {
  var pk         : pkey
  var sk         : skey
  var encL       : (cipher * label) list
  var decQueried : bool
}.

(* IND-1-CCA oracles implementation *)
module Ind1CCA_Oracles (S : Scheme, O : POracle, LR : LorR) = {
  
  proc o    = O.o

  proc enc(l : label, p0 p1 : plain) : cipher = {
    var c, p, l_or_r;
    l_or_r  <@ LR.l_or_r();
    p  <- l_or_r?p0:p1; (* encrypt challenge according to b *)
    c  <@ S(O).enc(BS.pk, l, p);
    BS.encL <- BS.encL ++ [(c,l)];  
    return c;
  }
  
  proc dec(cL: (cipher * label) list): (plain option) list = {
    var mL, m, c, l, i;
    i  <- 0;
    mL <- [];
    if (!BS.decQueried) {
      while (i < size cL) {
        (c,l) <- nth witness cL i;
        m <@ S(O).dec(BS.sk, l, c);
        if (mem BS.encL (c,l)) {
          m <- None;
        }
        mL <- mL ++ [m];
        i <- i + 1;
      }
      BS.decQueried <- true;
    }
    return mL;
  }
}.

(* IND-1-CCA experiment *)
module Ind1CCA (S : Scheme, A : Ind1CCA_Adv, O : Oracle, LR : LorR) = {
  module IO = Ind1CCA_Oracles(S,O,LR)
  module S = S(O)
  module A = A(IO)
  proc main(): bool = {
    var b';
    BS.encL       <- [];
    BS.decQueried <- false;
    O.init();
    (BS.pk,BS.sk) <@ S.kgen();
    b' <@ A.main(BS.pk);
    return b';
  }
}.

(* Ind-1-CCA oracles lossless *)

lemma Ind1CCA_Oracles_enc_ll (O <: POracle) (S <: Scheme) (LR <: LorR):
  islossless LR.l_or_r =>
  islossless S(O).enc =>
  islossless Ind1CCA_Oracles(S,O,LR).enc.
proof.
  move=> H_b_ll H_enc_ll; proc.
  by wp; call H_enc_ll; wp; call H_b_ll; auto.
qed.

lemma Ind1CCA_Oracles_dec_ll (O <: POracle { -BS }) (S <: Scheme { -BS }) (LR <: LorR):
  islossless S(O).dec =>
  islossless Ind1CCA_Oracles(S,O,LR).dec.
proof.
  move=> H_dec_ll; proc.
  sp; if; [ wp | by auto ].
  while true (size cL  - i).
    by progress; sp; wp; call H_dec_ll; auto; progress; smt.
  by auto; progress; smt.
qed.


(* * Typecheck security definitions. *)
(* ---------------------------------------------------------------------- *)

section.
  declare module O <: Oracle.
  declare module S <: Scheme.
  declare module A <: Ind1CCA_Adv.
  
  local lemma corr(m : plain, l:label) &m:
    exists eps, 0%r < eps /\
      Pr[Correctness(S, O).main(m,l) @ &m: res] >= 1%r - eps by exists 1%r;smt.


  local lemma Ind1CCA_n_challenge &m (n : int):
    exists eps, 
      `| Pr[Ind1CCA(S,A,O,Left).main()  @ &m: res /\  size BS.encL <= n] -
         Pr[Ind1CCA(S,A,O,Right).main() @ &m: res /\  size BS.encL <= n] | <= eps by exists 1%r;smt.
end section.

(* * Single enc-challenge implies multi enc-challenge security. *)
(* ---------------------------------------------------------------------- *)

(* We must express Ind1CCA(S,A,O,_) as a hybrid adversary HA that can call
   a leaks oracle O.leaks and l_or_r/right oracles O.orclL/O.orclR.
   The hybrid adversary HA and O are not allowed to share state and we
   must therefore push all operations that share state with O.orclL/O.orclR
   into the oracle O.leaks. *)

(* Inputs leaks function *)

type in_leaks = [ 
  | Phase1_in
  | RO_in     of h_in 
  | Dec_in    of (cipher * label) list].

op destr_Phase1_in(x: in_leaks) =
   with x = Phase1_in => true
   with x = RO_in  xo => false
   with x = Dec_in xd => false.

op destr_RO_in(x: in_leaks) =
   with x = Phase1_in => None
   with x = RO_in  xo => Some xo
   with x = Dec_in xd => None.

op destr_Dec_in(x: in_leaks) =
   with x = Phase1_in => None
   with x = RO_in  xo => None
   with x = Dec_in xd => Some xd.

(* Outputs leaks function *)

type out_leaks = [ 
  | Phase1_out of (pkey * skey)
  | RO_out     of h_out
  | Dec_out    of (plain option) list ].

op destr_Phase1_out(y: out_leaks) =
   with y = Phase1_out yo => Some yo
   with y = RO_out     yo => None
   with y = Dec_out    yo => None.

op destr_RO_out(y: out_leaks) =
   with y = Phase1_out yo => None
   with y = RO_out     yo => Some yo
   with y = Dec_out    yo => None.

op destr_Dec_out(y: out_leaks) =
   with y = Phase1_out yo => None
   with y = RO_out     yo => None
   with y = Dec_out    yo => Some yo.

require HybridArg.

op n : { int | 0 < n } as n_pos.

clone import HybridArg as H with
  type input    <- label * plain * plain,
  type output   <- cipher,
  type inleaks  <- in_leaks,
  type outleaks <- out_leaks,
  type outputA  <- bool,
  op   q        <- n
  proof *.
  realize q_pos. by apply n_pos. qed.

module WrapAdv(A: Ind1CCA_Adv, S : Scheme, O : Oracle, IO : Ind1CCA_Oracles) = {
  var l0         : int
  var l          : int
  var encL       : (cipher * label) list
  var pk         : pkey
    
  module WIO = {
    proc o   = IO.o

    proc enc(lbl : label, p0 p1 : plain) : cipher = {
      var c;
      if (l0 < l) {
        c  <@ S(O).enc(pk, lbl, p0);
      } elif (l0 = l) {
        c <@ IO.enc(lbl, p0, p1);
      } else {
        c  <@ S(O).enc(pk, lbl, p1);
      }
      encL <- encL ++ [(c,lbl)];
      l <- l + 1;
      return c;
    }

    proc dec(cL : (cipher * label) list) : plain option list = {
      var mL0, i, mL, c, lbl, m;
      mL0 <@ IO.dec(cL);
      i  <- 0;
      mL <- [];
      if (mL0<>[]) {
        while (i < size cL) {
          (c,lbl) <- nth witness cL i;
          if (mem encL (c,lbl)) {
            m <- None;
          } else {
            m <- nth witness mL0 i;
          }
          mL <- mL ++ [m];
          i <- i + 1;
        }
      }
      return mL;
    }
  }
    
  module A = A(WIO)

  proc main (pk_ : pkey) : bool = {
    var r;
    pk <- pk_;
    encL <- [];
    l0 <$ [0..n - 1];
    l  <- 0;
    r <@ A.main(pk);
    return r;
  }
}.

(* ---------------------------------------------------------------------- *)
section HybridProof.
  declare module O <: Oracle { -Count, -BS, -HybOrcl, -WrapAdv }.
  declare module S <: Scheme { -Count, -BS, -HybOrcl, -WrapAdv, -O }.
  declare module A <: Ind1CCA_Adv { -Count, -BS, -HybOrcl, -WrapAdv, -S, -O }.

  declare axiom O_init_ll: islossless O.init.
  declare axiom O_o_ll   : islossless O.o.
  declare axiom S_kgen_ll: islossless O.o => islossless S(O).kgen.
  declare axiom S_enc_ll : islossless O.o => islossless S(O).enc.
  declare axiom S_dec_ll : islossless O.o => islossless S(O).dec.
  declare axiom A_main_ll (IO <: Ind1CCA_Oracles { -A }):
    islossless IO.enc => 
    islossless IO.dec => 
    islossless IO.o => 
    islossless A(IO).main.
 
  (* ---------------------------------------------------------------------- *)
  (* Apply Hybrid lemma *)

  (* Oracles for hybrid adversary *)
  local module OrclbImpl : Orclb = {

    module IOL = Ind1CCA_Oracles(S,O,Left)
    module IOR = Ind1CCA_Oracles(S,O,Right)
 
    proc orclL = IOL.enc
    proc orclR = IOR.enc

    proc leaks(x: in_leaks): out_leaks = {
      var ro_i, ro_o, cL, mL;
      var r <- witness;

      if (destr_Phase1_in x) {
        BS.encL       <- [];
        BS.decQueried <- false;
        O.init();
        (BS.pk,BS.sk) <@ S(O).kgen();
        r <- Phase1_out (BS.pk, BS.sk);
      }elif (destr_RO_in x<>None) {
        ro_i <- oget (destr_RO_in x);
        ro_o <@ O.o(ro_i);
        r <- RO_out ro_o;
      } elif (destr_Dec_in x<>None) {
        cL <- oget (destr_Dec_in x);
        mL <@ IOL.dec(cL);
        r <- Dec_out mL;
      }

      return r;
    }
  }.

  (* Hybrid adversary *)
  local module HA(Ob: Orclb, OLR: Orcl) = {

    module IO = {
      var l, l0: int
      var chL  : (cipher * label) list
      var sk   : skey
    
      proc o(inp: h_in): h_out = {
        var r;
        r  <@ Ob.leaks(RO_in inp);
        return (oget(destr_RO_out r));
      }
  
      proc dec(cL: (cipher * label) list): (plain option) list = {
        var r;
        r  <@ Ob.leaks(Dec_in cL);
        return (oget(destr_Dec_out r));
      }

      proc enc(lb: label, p0 p1: plain): cipher = {
        var r;
        r <@ OLR.orcl(lb,p0,p1);
        return r;
      }
    }

    module A = A(IO)

    proc main() : bool = {
      var r1, pk, sk, b;
      r1 <@ Ob.leaks(Phase1_in);
      (pk, sk) <- oget (destr_Phase1_out r1);
      b <@ A.main(pk);
      return b;
    } 
  }.

  local lemma leaks_ll: islossless OrclbImpl.leaks.
  proof.
    proc; sp.
    if; first by wp; call (S_kgen_ll _); [ apply O_o_ll | call O_init_ll; auto].
    if; first by wp; call O_o_ll; auto.
    if; last by auto.
    by wp; call (Ind1CCA_Oracles_dec_ll O S Left _); [ apply S_dec_ll; apply O_o_ll | auto].
  qed.

  local lemma orclL_ll : islossless OrclbImpl.orclL.
  proof. by proc; inline *; wp; call (S_enc_ll O_o_ll); auto. qed.

  local lemma orclR_ll : islossless OrclbImpl.orclR.
  proof. by proc; inline *; wp; call (S_enc_ll O_o_ll); auto. qed.

  local lemma hyb1 &m:
        Pr[Ln(OrclbImpl, HybGame(HA)).main() @ &m : (res /\ HybOrcl.l <= n) /\ Count.c <= 1]
      - Pr[Rn(OrclbImpl, HybGame(HA)).main() @ &m : (res /\ HybOrcl.l <= n) /\ Count.c <= 1] 
    = 1%r/n%r * (
          Pr[Ln(OrclbImpl,HA).main() @ &m : res /\ Count.c <= n ]
        - Pr[Rn(OrclbImpl,HA).main() @ &m : res /\ Count.c <= n ]).
  proof.
    apply (Hybrid OrclbImpl HA  _ _ _ _ &m (fun ga ge l r, r )).
    + apply leaks_ll.
    + apply orclL_ll.
    + apply orclR_ll.
    + move=> Ob LR LR_ll leaks_ll L_ll R_ll; proc.
      call (_: true); first apply A_main_ll.
      + by proc; call LR_ll; auto.
      + by proc; call leaks_ll; auto. 
      + by proc; call leaks_ll; auto. 
      by wp; call leaks_ll; auto.
  qed.

  (* ---------------------------------------------------------------------- *)
  (* Show equivalence between Hybrid adversary and Ind1CCA *)

  local module HA_O_L = HA(OrclbImpl, OrclCount(L(OrclbImpl))).
  local module HA_O_R = HA(OrclbImpl, OrclCount(R(OrclbImpl))).

  (* BS: For the constraints here on C, it would be nice to define and enforce
         non-memory modules. *)
  local lemma hyb_aux1 (C <: LorR { -BS, -O, -S, -A, -Count }) &m:
      Pr[Orcln(HA(OrclbImpl), LeftRight(C,OrclbImpl)).main() @ &m : res /\ Count.c <= n]
    = Pr[Ind1CCA(S,A,O,C).main()  @ &m: res /\ size BS.encL <= n].
  proof.
    byequiv (_:  ={glob A, glob O, glob S, glob BS}
             ==> _) => //. proc.
    inline Count.init HA(OrclbImpl, OrclCount(LeftRight(C, OrclbImpl))).main; wp.
    call (_: Count.c{1} = size BS.encL{2} /\ ={glob BS, glob O, glob S}).
    + proc. inline *. simplify.
      swap{1} 3 -2.
      seq 1 1:
        (lb{1} = l{2} /\ ={p0, p1,l_or_r, glob O, glob S} /\
         Count.c{1} = size BS.encL{2} /\ ={BS.sk, BS.decQueried, BS.encL, BS.pk}).
        by call (_: true); auto.
      wp; sp.
      by if{1}; wp; sp; call (_: ={glob O}); try (proc true); auto; progress; smt.
    + proc. inline *. sp.
      rcondf{1} 1; first by auto.
      rcondf{1} 1; first by auto.
      rcondt{1} 1; first by auto.
      sp. if.
      + by auto.
      + wp.
        conseq
          (_: ={i} /\ cL1{1} = cL{2} /\ mL0{1} = mL{2} /\ ={glob O, glob S, glob BS}
           ==> cL1{1} = cL{2} /\ mL0{1} = mL{2} /\ ={glob O, glob S, glob BS}) => //.
        by sim.
      + by auto. 
    + proc*. inline *. sp.
      rcondf{1} 1; first by auto.
      rcondt{1} 1; first by auto.
      by wp; call (_: true); auto.
    inline *. wp. sp.
    rcondt{1} 1; first by auto.
    by wp; call (_: true); call (_: true); by auto.
  qed.

  local lemma hyb2 &m:
      Pr[Ln(OrclbImpl, HA).main() @ &m : res /\ Count.c <= n]
    = Pr[Ind1CCA(S,A,O,Left).main()  @ &m: res /\ size BS.encL <= n].
  proof. by apply (hyb_aux1 Left &m). qed.

  local lemma hyb3 &m:
      Pr[Rn(OrclbImpl, HA).main() @ &m : res /\ Count.c <= n]
    = Pr[Ind1CCA(S,A,O,Right).main()  @ &m: res /\ size BS.encL <= n].
  proof. by apply (hyb_aux1 Right &m). qed.

  local lemma hyb4 &m:
      `|  Pr[Ln(OrclbImpl, HybGame(HA)).main() @ &m : (res /\ HybOrcl.l <= n) /\ Count.c <= 1]
        - Pr[Rn(OrclbImpl, HybGame(HA)).main() @ &m : (res /\ HybOrcl.l <= n) /\ Count.c <= 1]|
    = 1%r/n%r * (
       `|  Pr[Ind1CCA(S,A,O,Left).main()  @ &m:  res /\  size BS.encL <= n]
         - Pr[Ind1CCA(S,A,O,Right).main()  @ &m: res /\  size BS.encL <= n]|).
  proof.
search (`| _ |)%Real.
    rewrite -(hyb2 &m) -(hyb3 &m) (hyb1 &m) StdOrder.RealOrder.normrM.
    have H :  (0%r <= (1%r / n%r)) by smt.
    by rewrite {1}/("`|_|")%Real H.
  qed.

  local lemma hyb_aux2 (C <: LorR { -BS, -O, -S, -A, -Count, -WrapAdv, -HybOrcl }) &m:
      Pr[Orcln(HybGame(HA,OrclbImpl),LeftRight(C,OrclbImpl)).main() @ &m : (res /\ HybOrcl.l <= n) /\ Count.c <= 1]
    = Pr[Ind1CCA(S,WrapAdv(A,S,O),O,C).main()  @ &m: res /\ WrapAdv.l <= n /\ size BS.encL <= 1].
  proof.
    byequiv (_: ={glob O, glob S, glob BS, glob A}
             ==> ={res} /\ HybOrcl.l{1} = WrapAdv.l{2} /\ Count.c{1} = size BS.encL{2} /\ Count.c{1} <= 1) => //.
    proc. inline *. wp.
    rcondt{1} 6; first by auto.
    call(_:
         ={glob O, glob S} /\ ={l,l0}(HybOrcl,WrapAdv) /\ ={encL,pk}(BS,WrapAdv) /\
         ={BS.sk, BS.decQueried,BS.pk} /\
         (forall cl, mem BS.encL{2} cl => mem BS.encL{1} cl) /\
         Count.c{1} = size BS.encL{2} /\ Count.c{1} = if HybOrcl.l{1} <= HybOrcl.l0{1} then 0 else 1).
    + proc. inline *. wp. sp.
      if; first by auto.
      + wp. call (_: ={glob O}); first by (proc true); progress.
        by auto; progress; smt.
      + if; first by auto.
        + sp.
          (* BS: seq* (see issue tracker) would help here. *)
          seq 1 1:
              (l{2} = lbl{2} /\
               p00{2} = p0{2} /\
               p10{2} = p1{2} /\
               m0{1} = m{1} /\
               m1{1} = m0{1} /\
               ((m{1} = (lb{1}, p0{1}, p1{1}) /\
               (lb{1} = lbl{2} /\ ={p0, p1}) /\
               ={glob O, glob S} /\
               (HybOrcl.l{1} = WrapAdv.l{2} /\ HybOrcl.l0{1} = WrapAdv.l0{2}) /\
               (BS.encL{1} = WrapAdv.encL{2} /\ BS.pk{1} = WrapAdv.pk{2}) /\
               ={BS.sk, BS.decQueried, BS.pk} /\
               (forall (cl : cipher * label), mem BS.encL{2} cl => mem BS.encL{1} cl) /\
               Count.c{1} = size BS.encL{2} /\
               Count.c{1} = if HybOrcl.l{1} <= HybOrcl.l0{1} then 0 else 1) /\
               !HybOrcl.l0{1} < HybOrcl.l{1}) /\
               HybOrcl.l0{1} = HybOrcl.l{1} /\
               l_or_r1{1} = l_or_r{2}). (* this is new *)
            by call (_: true); auto.
          case (l_or_r1{1}).
          + rcondt{1} 1; first by auto.
            by wp; call (_: ={glob O}); try (proc true); auto; progress; smt.
          + rcondf{1} 1; first by auto.
            by wp; call (_: ={glob O}); try (proc true); auto; progress; smt.
        + wp. call (_: ={glob O}); first by (proc true); progress.
          by auto; progress; smt.
    + proc*. inline *. sp.
      rcondf{1} 1; first by auto.
      rcondf{1} 1; first by auto.
      rcondt{1} 1; first by auto.
      sp; if.
      + by auto.
      + swap{2} 2 4. wp.
        swap{2} 3 - 2. swap{2} 4 -2. sp.
        simplify.
        conseq (_:
           i{1} = 0 /\ i{2} = 0 /\ i0{2} = 0 /\
           mL{2} = [] /\ mL0{1} = [] /\ mL1{2} = [] /\
           ={i, cL, glob O, glob S, BS.decQueried, BS.sk} /\
           cL2{1} = cL0{2} /\ cL1{2} = cL0{2} /\
           BS.encL{1} = WrapAdv.encL{2} /\
           (forall (cl : cipher * label), mem BS.encL{2} cl=> mem BS.encL{1} cl)
           ==>
           ={glob O, glob S} /\ mL0{1} = mL{2}); [ 1..2: done].
        case (cL0{2} = []).
        + rcondf{1} 1; first by auto; progress; smt.
          rcondf{2} 1; first by auto; progress; smt.
          rcondf{2} 2; first by auto; progress; smt.
          by auto.
        - rcondt{2} 3. auto.
          while (0 < i0 => mL1 <> []).
            by wp; call (_: true); try proc true; auto; progress; smt.
          by auto; progress; smt.
        seq 1 1:
          (={glob O, glob S, BS.decQueried, BS.sk} /\
           i{1} = i0{2} /\ i{2} = 0 /\ mL{2} = [] /\
           cL2{1} = cL0{2} /\ cL1{2} = cL0{2} /\
           size mL0{1} = size cL2{1} /\ BS.encL{1} = WrapAdv.encL{2} /\
           (forall j, 0 <= j < size cL2{1}
            => (mem  BS.encL{1} (nth witness cL2{1} j)
                => nth witness mL0{1} j = None)
               /\
               (!mem BS.encL{1} (nth witness cL2{1} j)
                => nth witness mL0{1} j = nth witness mL1{2} j))).
          while (={glob O, glob S, BS.decQueried, BS.sk} /\
                 i{1} = i0{2} /\ i{2} = 0 /\ 0 <= i{1} /\ i{1} <= size cL2{1} /\
                 size mL0{1} = i{1} /\ size mL1{2} = i{1} /\ mL{2} = [] /\
                 cL2{1} = cL0{2} /\ cL1{2} = cL0{2} /\
                 (forall cl, mem BS.encL{2} cl => mem BS.encL{1} cl) /\
                 (forall j, 0 <= j /\ j < i{1}
                  => (mem BS.encL{1} (nth witness cL2{1} j)
                      => nth witness mL0{1} j = None)
                     /\
                     (!mem BS.encL{1} (nth witness cL2{1} j)
                      => nth witness mL0{1} j = nth witness mL1{2} j))).
            wp. call (_: ={glob O}); first by proc true; smt.
            auto. progress; expect 24.
            + smt. + smt. + smt. 
            + rewrite cats1. smt.  
            + case (j < size mL0{1}). 
              + smt. 
              + move => Hx. 
                rewrite -lezNgt in Hx.
                have ->: j = size mL0{1}.
                  have Hneed: forall (a b: int), a < b + 1 => a<= b by smt.    
                  rewrite eqz_leq. 
                  by rewrite (Hneed j (size mL0{1}) H9) Hx.
                smt. 
            + smt. + smt. + smt. + smt. + smt. 
            + smt. + smt. + smt. + smt. + smt.
            + rewrite size_cat; smt.
            + case (j < size mL0{1}).  
              + move => Hx. 
                rewrite nth_cat Hx //=.
                smt. 
              + move => Hx. 
                rewrite -lezNgt in Hx.
                have ->: j = size mL0{1}. 
                  have Hneed: forall (a b: int), a < b + 1 => a<= b by smt.    
                  rewrite eqz_leq. 
                  by rewrite (Hneed j (size mL0{1}) H9) Hx.
                smt.
            + rewrite nth_cat nth_cat. 
              smt.
            + smt. + smt. + smt. 
            + rewrite size_cat; smt. 
            + case (j < size mL0{1}).
              + smt. 
              + rewrite -lezNgt. 
                move => Hx. 
                have ->>: j = size mL0{1}. 
                  have Hneed: forall (a b: int), a < b + 1 => a<= b by smt.    
                  rewrite eqz_leq. 
                  by rewrite (Hneed j (size mL0{1}) H9) Hx.
                move: H7. 
                smt. 
            + smt.
          auto; progress; expect 5; smt. 
        sp.
        while{2}
        ( size mL{2} = i{2} /\ cL2{1} = cL0{2} /\ cL1{2} = cL0{2} /\
          size mL0{1} = size cL2{1} /\
          BS.encL{1} = WrapAdv.encL{2} /\ 0 <= i{2} <=  size cL0{2} /\
          (forall j, 0 <= j /\ j < size cL2{1}
           => (mem BS.encL{1} (nth witness cL2{1} j)
               => nth witness mL0{1} j = None)
              /\
              (!mem BS.encL{1} (nth witness cL2{1} j)
               => nth witness mL0{1} j = nth witness mL0{2} j)) /\
          (forall j, 0 <= j /\ j < i{2} => nth witness mL0{1} j = nth witness mL{2} j))
         (size cL0{2} - i{2}).
        progress.  
        auto; progress. 
        + smt. + smt. + smt. 
        + rewrite nth_cat; smt.
        + smt. + smt. + smt. + smt.  
        + rewrite nth_cat; smt.
        + smt.

        auto; progress. 
        + smt. + smt. + smt. + smt. + smt. 
        have Hx: size mL0{1} = size mL_R by smt.
        have Hx2: (forall (j : int), 0 <= j < size mL0{1} => 
                                     nth witness mL0{1} j = nth witness mL_R j) by smt.
        by rewrite (eq_from_nth witness mL0{1} mL_R Hx Hx2). 
      + sp. rcondf{2} 1; first by auto.
        by auto.
    + proc*. inline *. sp.
      rcondf{1} 1; first by auto.
      rcondt{1} 1; first by auto.
      by wp; call (_: true); auto.
    swap{1} 2 -1. swap{2} 8 -7. swap{1} 8 -6. swap{1} 9 -6.
    swap{2} 4 -2. swap{2} 5 -2.
    wp; call (_: true); call(_: true).
    by auto; progress; smt.
  qed.

  local lemma hyb5 &m:
      Pr[Ln(OrclbImpl, HybGame(HA)).main() @ &m : (res /\ HybOrcl.l <= n) /\ Count.c <= 1]
    = Pr[Ind1CCA(S,WrapAdv(A,S,O),O,Left).main()  @ &m: res /\ WrapAdv.l <= n /\ size BS.encL <= 1].
  proof. by apply (hyb_aux2 Left &m). qed.

  local lemma hyb6 &m:
      Pr[Rn(OrclbImpl, HybGame(HA)).main() @ &m : (res /\ HybOrcl.l <= n) /\ Count.c <= 1]
    = Pr[Ind1CCA(S,WrapAdv(A,S,O),O,Right).main()  @ &m:  res /\ WrapAdv.l <= n /\ size BS.encL <= 1].
  proof. by apply (hyb_aux2 Right &m). qed.

  lemma Ind1CCA_multi_enc &m:
      `|  Pr[Ind1CCA(S,WrapAdv(A,S,O),O,Left).main()  @ &m:   res /\ WrapAdv.l <= n /\ size BS.encL <= 1]
        - Pr[Ind1CCA(S,WrapAdv(A,S,O),O,Right).main()  @ &m:  res /\ WrapAdv.l <= n /\ size BS.encL <= 1] |
    = 1%r/n%r * (
       `|  Pr[Ind1CCA(S,A,O,Left).main()  @ &m:  res /\ size BS.encL <= n]
         - Pr[Ind1CCA(S,A,O,Right).main()  @ &m: res /\ size BS.encL <= n]|).
  proof.
    rewrite -(hyb5 &m) -(hyb6 &m).
    by apply (hyb4 &m).
  qed.

end section HybridProof.

