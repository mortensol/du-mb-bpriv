(**** Load necessary theories ****)
require import Int Bool Real DInterval SmtMap. 
require import List Distr Core FSet. 
require import LeftOrRight DBool. 
require (*  *) VotingDefinition_omb.

 clone include VotingDefinition_omb. 

(**** mb-BPRIV security definition ****)


(* mb-BPRIV oracles *)
module type MB_BPRIV_oracles = {
  (* random oracles for encryption and proof system *)
  proc h(inp: h_in) : h_out
  proc g(inp: g_in) : g_out

  (* voting oracle *)
  proc vote(id:ident, v0 v1 : vote) : unit

  (* verification oracle *)
  proc verify(id:ident) : unit

  (* adversary view *)
  proc board() : pubBB 
}.

(* global state shared between MB-BPRIV oracles and game *)
module BP = {
  var pk         : pkey (* election public key used for voting *)
  var sk         : skey (* election secret key used in tally *)
  var r          : result (* election result *)
  var pi         : prf (* tally proof *)
  var pi'        : prf (* simulated tally proof *)
  var d          : bool (* adversary's guess *)
  var bb         : (pubcred * ballot) list (* first bb created by adversary *)
  var bbstar     : (result * prf) option (* second bb created by adversary *)
  var bb'        : (pubcred * ballot) list (* recovered board for tally when d = 1 *)
  var bb0        : (ident * pubcred * ballot) list (* left world extended bulletin board *)
  var bb1        : (ident * pubcred * ballot) list (* right world extended bulletin board *)
  var secmap     : (ident, secretcred) fmap (* secret credentials *)
  var pubmap     : (ident, pubcred) fmap (* public credentials *)
  var vmap       : (ident, (ballot * state * vote) list) fmap (* voter ballots and states *)
  var setidents  : ident fset (* set of all voter identities *)
  var setchecked : ident fset (* set of voters who check their vote *)
  var sethappy   : ident fset (* set of voters who check and are happy *)
  var setH       : ident fset (* set of honest voters *)
  var setD       : ident fset (* set of dishonest voters *)
  var secmapD    : (ident, secretcred) fmap (* secret credential for the dishonest users *)
  var setHcheck  : ident fset (* set of voters we assume will verify *)
  var valid      : bool (* recording whether or not the bulletin board is valid *)
}. 

op setidents : ident fset. (* set of voter identities *)
op setH : ident fset. (* honest voters *)
op setD : ident fset. (* dishonest voters *)
op setHcheck : ident fset. (* voters we assume will verify *)

axiom setid_union : setidents = setH `|` setD. 
axiom setHD_intersection : setH `&` setD = fset0. 
axiom setHcheck_sub : setHcheck \subset setH. 


(* Operator extracting identity given list of secret credentials and a public credential *)
op extract_id : (ident, secretcred) fmap -> pubcred -> ident. 

(* Operator removing identity from an element on an extended bulletin board *)
op rem_id (x : ident * pubcred * ballot) = (x.`2, x.`3). 

(* Operator removing identity from all elements of an extended bulletin board *)
op rem_ids (bb:(ident * pubcred * ballot) list) = map (fun b : (ident * pubcred * ballot) 
           => (b.`2, b.`3)) bb. 

(**** The recovery algorithm ****)

module type Recover' = {
  proc rec(bb0 : (pubcred * ballot) list, 
           bb1 : (pubcred * ballot) list, 
           bb  : (pubcred * ballot) list) 
               : (pubcred * ballot) list
}.


module Recover' = {
  proc rec( bb0 :  (pubcred * ballot) list, 
            bb1 :  (pubcred * ballot) list, 
            bb  :  (pubcred * ballot) list) 
                : (pubcred * ballot) list = {
    
    var bb', i, j, p, b;
      
    bb' <- [];
    i   <- 0;
    
    while (i < size bb) {          (* for (p, b) ∈ BB: *)
      (p,b) <- nth witness bb i;   (* for (p, b) ∈ BB: *)
      if ( (p,b) \in bb1 ) {       (* if ∃ j, id. BB1[j] = (id,(p, b)): *)
        j <- index (p,b) (bb1);    (* if ∃ j, id. BB1[j] = (id,(p, b)): *)
        bb' <- bb' ++ [(nth witness bb0 j)];
      } else {
        bb' <- bb' ++ [(p,b)];
      }
      i <- i + 1;
    }
    return bb';
  }
}.

(**** MB-BPRIV oracles ****)
module MB_BPRIV_oracles(V:VotingSystem, H:HOracle.POracle, 
                        G:GOracle.POracle, LR:LorR): MB_BPRIV_oracles = {

  (* Random oracles *)
  proc h = H.o
  proc g = G.o

  (* Vote oracle computing left and right side ballots and voter states *)
  proc vote_core(id, v0, v1, pb0, pb1, sl0, sl1) : 
                (state * ballot * pubcred * state * ballot * pubcred) = {

    var p0, b0, s0;
    var p1, b1, s1;

    (p0, b0, s0) <@ V(H, G).vote(BP.pk, id, pb0, sl0, v0);
    (p1, b1, s1) <@ V(H, G).vote(BP.pk, id, pb1, sl1, v1);

    return (s0, b0, p0, s1, b1, p1);
  }
  
  (* Oracle calling vote_core and adding resulting ballots and states to vmap and bulletin boards *)
  proc vote(id:ident, v0 v1 : vote) : unit = {
    var p0, b0, s0;
    var p1, b1, s1;
    var l_or_r;

    if ((id \in BP.setH)) {
      (s0, b0, p0, s1, b1, p1) <@ vote_core(id, v0, v1, 
                                            oget BP.pubmap.[id], oget BP.pubmap.[id], 
                                            oget BP.secmap.[id], oget BP.secmap.[id]);

      l_or_r <@ LR.l_or_r();
      BP.vmap.[id] <- (l_or_r?(b0, s0, v0):(b1, s1, v0)) :: (odflt [] BP.vmap.[id]);

      BP.bb0 <- (id, p0, b0) :: BP.bb0;
      BP.bb1 <- (id, p1, b1) :: BP.bb1;
    }
  }

  (* Verification oracle for individual verification *)
  proc verify(id:ident) : unit = {
    var ok, sv;

    BP.setchecked <- BP.setchecked `|` (fset1 id);
    sv <- odflt [] (BP.vmap.[id]);

    (* Verify on the adversary's board but the recovered result *)
    ok <@ V(H,G).verifyvote(id, (oget (ohead sv)).`2, BP.bb, oget BP.pubmap.[id], oget BP.secmap.[id]);
    if (ok) {
      BP.sethappy <- BP.sethappy `|` (fset1 id);
    }
  }

  (* Return public part of bb0 or bb1 depending on which world we are in *)
  proc board() : pubBB = {
    var l_or_r, bb;

    l_or_r <@ LR.l_or_r();
      bb   <- l_or_r?BP.bb0:BP.bb1;
    return Publish(rem_ids bb);
  } 
}. 

(** MB-BPRIV adversary type  **)
module type OMB_BPRIV_adv(O:MB_BPRIV_oracles) = {

  proc a1(pk:pkey, 
          cu:(ident, secretcred) fmap, 
          pu:(ident, pubcred) fmap ) : (pubcred * ballot) list 
                                       { O.vote, O.board, O.h, O.g }
                                       
  proc a2() : bool { }

  proc a3() : unit { O.verify, O.h, O.g }
  
  proc a4() : bool { }

  proc a5 (r:result, pi:prf) : bool { O.board, O.h, O.g }
                                      
}.

(**** OMB-BPRIV left side ****)
module OMB_BPRIV_L(V:VotingSystem, A:OMB_BPRIV_adv, H:HOracle.Oracle, G:GOracle.Oracle) = {
  
  module O = MB_BPRIV_oracles(V, H, G, Left)
  module A = A(O)
  module V = V(H,G)

  proc main() : bool = {
    var i, id,p, c, valid;

    (* initialize global variables and random oracles *)
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
    (BP.pk, BP.sk) <@ V.setup(); 
    
    (* registration *)
    i <- 0;
    while (i < card BP.setidents) {
      id <- nth witness (elems BP.setidents) i;
      (p,c)  <@ V.register(id,BP.pk,BP.sk);
      BP.secmap.[id] <- c;
      BP.pubmap.[id] <- p;
      if (id \in BP.setD) {
        BP.secmapD.[id] <- oget BP.secmap.[id];
      }
      i <- i + 1;
    }

    (* first bulletin board created by adversary *)
    BP.bb <@ A.a1(BP.pk, BP.secmapD, BP.pubmap); 

    (* the adversary is allowed to make a guess if everything looks fine *)
    (* (i.e. board is valid, voters are happy, voters actually verify)   *)
    if (!(BP.setHcheck \subset fdom BP.vmap)) {
      BP.d <$ {0,1};
    } else {
      valid <@ V.validboard(BP.bb, BP.pk);
      if (!valid) {
        BP.d <@ A.a2();
      } else { 
        A.a3();
        if (!BP.setHcheck \subset BP.setchecked) {
            BP.d <$ {0,1};
        } else { 
          if (!BP.setHcheck \subset BP.sethappy) {
             BP.d <@ A.a4();
          }
          if (BP.setHcheck \subset BP.sethappy) {
             (BP.r, BP.pi) <@ V.tally(BP.bb, BP.pk, BP.sk);
             BP.d <@ A.a5(BP.r, BP.pi);
          }
        }
      }
    }
    return BP.d;
  }  
}. 


(**** mb-BPRIV simulator type ****)
module type MB_BPRIV_simulator = {
  proc init()    : unit
  proc o(x:g_in) : g_out
  proc prove(st: (pkey * pubBB * result)) : prf
}.

 (**** MB-BPRIV right side ****)
module OMB_BPRIV_R(V:VotingSystem, A:OMB_BPRIV_adv, H:HOracle.Oracle,G: GOracle.Oracle,
                   S:MB_BPRIV_simulator, R:Recover') = {
  
  module O = MB_BPRIV_oracles(V, H, S, Right)
  module A = A(O)

  proc main() : bool = {
    var i, id, p, c, valid;

    (* Initialize global variables and random oracles *)
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
    G.init();

    (* Setup *)
    (BP.pk, BP.sk) <@ V(H,S).setup(); 
    
    (* registration *)
    i <- 0;
    while (i < card BP.setidents) {
      id <- nth witness (elems BP.setidents) i;
      (p,c)  <@ V(H,S).register(id,BP.pk,BP.sk);
      BP.secmap.[id] <- c;
      BP.pubmap.[id] <- p;
      if (id \in BP.setD) {
        BP.secmapD.[id] <- oget BP.secmap.[id];
      }
      i <- i + 1;
    }

    (* first bulletin board created by adversary *)
    BP.bb <@ A.a1(BP.pk, BP.secmapD, BP.pubmap); 

    (* the adversary is allowed to make a guess if everything looks fine *)
    (* (i.e. board is valid, voters are happy, voters actually verify)   *)
    if (!(BP.setHcheck \subset fdom BP.vmap)) {
      BP.d <$ {0,1};
    } else {
      valid <@ V(H,S).validboard(BP.bb, BP.pk);
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
            BP.bb'        <@ R.rec(rem_ids BP.bb0, rem_ids BP.bb1, BP.bb);
            (BP.r, BP.pi) <@ V(H,G).tally(BP.bb', BP.pk, BP.sk);
            BP.pi'        <@ S.prove(BP.pk, Publish BP.bb, BP.r);
            BP.d <@ A.a5(BP.r, BP.pi');
          }
        }
      }
    }
    return BP.d;
  }  
}. 

(** ValidInd algorithm that we keep abstract for now but use in the validboard proc in MiniVoting **)
module type ValidInd (H:HOracle.POracle) = {
  proc validInd(b : (ident * pubcred * ballot), pk:pkey) : bool { H.o }
}.

(* Typechecks *)
section.

require import Real. 

declare module H <: HOracle.Oracle.
declare module G <: GOracle.Oracle.
declare module V <: VotingSystem. 
declare module A <: OMB_BPRIV_adv.  
declare module S <: MB_BPRIV_simulator. 
declare module R <: Recover'. 

local lemma bpriv_typecheck &m : 
    exists eps, `| Pr[OMB_BPRIV_L(V,A,H,G).main() @ &m : res] - Pr[OMB_BPRIV_R(V,A,H,G,S,R).main() @ &m : res] | 
    <= eps by []. 

end section. 
