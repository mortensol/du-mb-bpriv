require import Int Real SmtMap.
require import List Distr Core.
require (*  *) LPKE ProofSystem.


(* ---------------------------------------------------------------------- *)
(* Preliminaries *)

(* types *)
type ident.   (* ident *)
type label.   (* label *)
type vote.    (* vote *)
type result.  (* result *)
type pubBB.   (* public bulletin box *)

type cipher.  (* chipertext *)
type pkey.    (* public key *)
type skey.    (* secret key *)

type prf.     (* proof *)

type h_in, h_out. (* input and output for encryption   random oracle H *)
type g_in, g_out. (* input and output for proof system random oracle G *)

(* operators *)
op dh_out : h_out distr.   (* distribution for random oracle H *)
op dg_out : g_out distr.   (* distribution for random oracle G *)

(* result function rho *)
op Rho    : (label * vote option) list -> result distr.
(* public algorithm Publish *)
op Publish: (label * cipher) list  -> pubBB.  
(* bound nr of challenge queries *)
op n : { int | 0 < n } as n_pos.   

(* import encryption scheme *) 
clone export LPKE as PKEvf with
  type label  <- label,
  type plain  <- vote,
  type cipher <- cipher,
  type pkey   <- pkey,
  type skey   <- skey,
  type h_in   <- h_in,
  type h_out  <- h_out,
  op   dout   <- dh_out,
  op   n      <- n
  proof *.
  realize n_pos. by apply n_pos. qed.

(* import proof system *)
clone export ProofSystem as PSvf with
  type stm   <- pkey * pubBB * result,
  type wit   <- skey * (label * cipher) list,
  type prf   <- prf,
  type g_in  <- g_in,
  type g_out <- g_out,
  op   dout  <- dg_out
  proof *. 


(* ---------------------------------------------------------------------- *)
(* Voting friendly relation security definitions *)

(* VFR adversary *)
module type VFR_Adv(H: PKEvf.POracle, G: PSvf.POracle) ={
  proc main(pk: pkey)  : ( label * cipher) list { H.o, G.o} 
}.

(*** Overwrite the Relation in Proof System to one of the following ***)

(* Voting relation that may query the random oracle 
   of the encryption scheme given as input *)
module type VotingRelation (H: PKEvf.POracle) = {
  proc main(w: (pkey * pubBB * result), 
            s: (skey * (label * cipher) list)): bool 
}.

module type VotingRelation' (E: Scheme, H: PKEvf.POracle) = {
  proc main(w: (pkey * pubBB * result), 
            s: (skey * (label * cipher) list)): bool 
}.

(* 1. VFR experiment *) 
module VFR(E:Scheme, A:VFR_Adv, R: VotingRelation, H: PKEvf.Oracle, G: PSvf.Oracle )={

  proc main():bool={
    var r, i, l, c, m, rel;
    var bb, ubb, pbb;

    i   <- 0;
    ubb <- [];
    bb  <- [];
    
    H.init();
    G.init();
    (BS.pk,BS.sk) <@ E(H).kgen();
    bb      <@ A(H,G).main(BS.pk); 
    
    while (i < size bb){
      (l,c)  <- nth witness bb i;
         m   <@ E(H).dec(BS.sk, l, c);
        ubb  <- ubb ++ [(l, m)];     
         i   <- i + 1;
    }

    r   <$ Rho ubb;                              
    pbb <- Publish bb;   
    rel <@ R(H).main((BS.pk, Publish bb, r), (BS.sk, bb));
    return !rel;
  }
}.

