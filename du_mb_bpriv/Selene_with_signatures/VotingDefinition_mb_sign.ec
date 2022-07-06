(**** Load necessary theories ****)
require import Int Bool List Distr Core SmtMap. 
require import LeftOrRight. 
require (*  *) ROM. 

(**** Types and operators for voting systems ****)

type ident.      (* voter identifiers *)
type vote.       (* vote *)
type aux_t.      (* auxiliary information that comes from the tally *)
type result.     (* election result *)
type ballot.     (* ballot *)
type pubBB.      (* public bulletin board *)
type pubcred.    (* public credential *)
type secretcred. (* secret credential *)
type state_pre.  (* voter state before recovery *)
type state_post. (* voter state after recovery *)
type pkey.       (* election public key *)
type skey.       (* election secret key *)
type prf.        (* tally proof *)
type stm.        (* statement for proof systems *)

type saux.  (* potential signature *)

op Rho     : (pubcred * vote option) list      -> result distr.
op Publish : (pubcred * ballot * saux) list -> pubBB. 

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
  
  (**** Setup, producing some public and secret data ****)
  proc setup()    : pkey * skey { H.o }

  (**** Register can capture a joint protocol between the authority and the user ****)
  proc register(id:ident, pk:pkey, sk:skey) : pubcred * secretcred { H.o }

  (**** Vote, resulting in a ballot and a state that the voter later can use for verification ****)
  (**** as well as a signature on the ballot                                                  ****)
  proc vote(pk:pkey, id:ident, pc:pubcred, sc:secretcred, v:vote) 
         : pubcred * ballot * saux * state_pre * state_post { H.o }

  (**** Check if a ballot box is valid, where "valid" is defined by each voting system ****)
  proc validboard(bb:(pubcred * ballot * saux) list, pk:pkey) : bool { H.o }

  (**** Tally, returing the result of the election along with a proof of correct tally ****)
  proc tally(bb:(pubcred * ballot * saux) list, pk:pkey, sk:skey) : result * prf { H.o, G.o }

  (**** Verify vote can capture checking encrypted ballots or plaintext results ****)
  proc verifyvote(id:ident, 
                  s_pre :state_pre,
                  s_post:state_post,
                  bb:(pubcred * ballot * saux) list, 
                  bbstar:result * prf,
                  pc:pubcred,
                  sc:secretcred) : bool { H.o, G.o }

  (**** Verify that the proof of correct tally is valid ****)
  proc verifytally(st : (pkey * pubBB * result), pf:prf) : bool { G.o }
 
}.
