(**** Load necessary theories ****)
require import Int Bool List Distr Core SmtMap. 
require import LeftOrRight. 
require (*  *) ROM. 

(**** Types and operators for voting systems ****)

type ident.      (* voter identifiers *)
type vote.       (* vote *)
type result.     (* election result *)
type ballot.     (* ballot *)
type pubBB.      (* public bulletin board *)
type pubcred.    (* public credential *)
type secretcred. (* secret credential *)
type state.      (* voter state before recovery *)
type pkey.       (* election public key *)
type skey.       (* election secret key *)
type prf.        (* proof *)

(* Result function *)
op Rho     : (ident * vote option) list -> result distr.

(* Publish algorithm, returning the public part of the bulletin board *)
op Publish : (pubcred * ballot) list    -> pubBB. 

(**** Random oracles for voting scheme ****)

type h_in, h_out. (* input and output for random oracle H used for ballot *)
type g_in, g_out. (* input and output for random oracle G used for proof  *)

op dh_out : h_out distr. 
op dg_out : g_out distr. 

(* Random oracle for ballot that cannot be simulated *)
clone ROM as HOracle with
  type in_t       <- h_in,
  type out_t      <- h_out,
  op dout(x:h_in) <- dh_out.

(* Random oracle for proof that can be simulated *)
clone ROM as GOracle with 
  type in_t       <- g_in,
  type out_t      <- g_out,
  op dout(x:g_in) <- dg_out. 


(**** Voting scheme syntax ****)
module type  VotingSystem(H:HOracle.POracle, G:GOracle.POracle) = {
  
  (* Setup algorithm *)
  proc setup()    : pkey * skey { H.o }

  (* Register algorithm that can capture a joint protocol between the authority and the user *)
  proc register(id:ident, pk:pkey, sk:skey) : pubcred * secretcred { H.o }

  (* Voting algorithm *)
  proc vote(pk:pkey, id:ident, pc:pubcred, sc:secretcred, v:vote) : pubcred * ballot * state { H.o }

  (* Check if the bulletin board is valid *)
  proc validboard(bb:(pubcred * ballot) list, pk:pkey) : bool { H.o }

  (* Tally algorithm *)
  proc tally(bb:(pubcred * ballot) list, pk:pkey, sk:skey) : result * prf { H.o, G.o }

  (* Verify vote algorithm that can capture checking encrypted ballots or plaintext results *)
  proc verifyvote(id:ident, 
                  s :state,
                  bb:(pubcred * ballot) list,
                  pc:pubcred,
                  sc:secretcred) : bool { H.o, G.o }

  (* Verify that the tally is correct *)
  proc verifytally(st : (pkey * pubBB * result), pi:prf) : bool { G.o }
 
}.
