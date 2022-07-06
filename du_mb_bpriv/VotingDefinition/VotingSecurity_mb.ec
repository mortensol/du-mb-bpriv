(**** Load necessary theories ****)
require import Int Bool DInterval SmtMap. 
require import List Distr Core FSet. 
require import LeftOrRight DBool. 
require (*  *) VotingDefinition_mb.

clone include VotingDefinition_mb. 

(**** mb-BPRIV security definition ****)

(* mb-BPRIV oracles *)
module type DU_MB_BPRIV_oracles = {
  (* random oracles for encryption and proof system *)
  proc h(inp: h_in) : h_out
  proc g(inp: g_in) : g_out

  (* voting oracle *)
  proc vote(id:ident, v0 v1 : vote) : unit

  (* verification oracle *)
  proc verify(id:ident) : ident fset

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
  var d          : bool (* guess output by adversary *)
  var bb         : (pubcred * ballot) list (* first bb created by adversary *)
  var bbstar     : result * prf (* extra information produced by the adversary *)
  var bb'        : (pubcred * ballot) list (* recovered board for tally when d = 1 *)
  var bb0        : (ident * pubcred * ballot) list (* left world extended bulletin board *)
  var bb1        : (ident * pubcred * ballot) list (* right world extended bulletin board *)
  var secmap     : (ident, secretcred) fmap (* secret credentials *)
  var pubmap     : (ident, pubcred) fmap (* public credentials *)
  var vmap       : (ident, (ballot * state_pre * state_post * vote) list) fmap (* recorded voter states *)
  var pc_to_id   : (pubcred, ident) fmap (* finite map from public credential to identity *)
  var setidents  : ident fset (* set of all voter identities *)
  var setchecked : ident fset (* set of voters who check their vote *)
  var sethappy   : ident fset (* set of voters who check and are happy *)
  var setH       : ident fset (* set of honest voters *)
  var setD       : ident fset (* set of dishonest voters *)
  var secmapD    : (ident, secretcred) fmap (* secret credential for the dishonest users *)
  var setHcheck  : ident fset (* set of voters we assume will verify *)
}. 

(* Operator removing identity from an element on an extended bulletin board *)
op rem_id (x : ident * pubcred * ballot) = (x.`2, x.`3). 

(* Operator removing identity from all elements of an extended bulletin board *)
op rem_ids (bb:(ident * pubcred * ballot) list) 
   = map rem_id bb. 


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

      i <- 0;
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

(**** DU-MB-BPRIV oracles ****)
module DU_MB_BPRIV_oracles(V:VotingSystem, H: HOracle.POracle, 
                        G: GOracle.POracle, LR:LorR): DU_MB_BPRIV_oracles = {

  (* random oracles *)
  proc h = H.o
  proc g = G.o

  (* vote oracle constructing a ballot and a state that the voters use for verifiation *)
  proc vote_core(id, v0, v1, pb0, pb1, sl0, sl1) 
        : (state_pre * state_post * ballot * pubcred * 
           state_pre * state_post * ballot * pubcred) = {
    var p0, b0, s0_pre, s0_post;
    var p1, b1, s1_pre, s1_post;

    (p0, b0, s0_pre, s0_post) <@ V(H, G).vote(BP.pk, id, pb0, sl0, v0);
    (p1, b1, s1_pre, s1_post) <@ V(H, G).vote(BP.pk, id, pb1, sl1, v1);

    return (s0_pre, s0_post, b0, p0, s1_pre, s1_post, b1, p1);
  }
  
  (* vote oracle calling vote_core and stores that ballots and states *)
  proc vote(id:ident, v0 v1 : vote) : unit = {
    var p0, b0, s0_pre, s0_post;
    var p1, b1, s1_pre, s1_post;
    var l_or_r;

    if ((id \in BP.setH)) {
      (s0_pre, s0_post, b0, p0, s1_pre, s1_post, b1, p1) <@ 
      vote_core(id, v0, v1, oget BP.pubmap.[id], oget BP.pubmap.[id], 
                oget BP.secmap.[id], oget BP.secmap.[id]);

      l_or_r <@ LR.l_or_r();
      BP.vmap.[id] <- (l_or_r?(b0, s0_pre, s0_post, v0):
                              (b1, s1_pre, s0_post, v0)) :: (odflt [] BP.vmap.[id]);

      BP.bb0 <- (id, p0, b0) :: BP.bb0;
      BP.bb1 <- (id, p1, b1) :: BP.bb1;
    }
  }

  (* voter verification oracle *)
  proc verify(id:ident) : ident fset = {
    var ok, sv;

    if (id \in BP.setidents){
      BP.setchecked <- BP.setchecked `|` (fset1 id);
      sv            <- odflt [] (BP.vmap.[id]);

      (* Verify on the adversary's board but the recovered result *)
      ok <@ V(H,G).verifyvote(id, (oget (ohead sv)).`2, (oget (ohead sv)).`3, 
                              BP.bb, BP.bbstar,  oget BP.pubmap.[id], oget BP.secmap.[id]);
      if (ok) {
        BP.sethappy <- BP.sethappy `|` (fset1 id);
      }
    }
    return BP.sethappy;
  }

  (* display the public part of bb0 or bb1, depending on the hidden bit *)
  proc board() : pubBB = {
    var l_or_r, bb;

    l_or_r <@ LR.l_or_r();
      bb   <- l_or_r?BP.bb0:BP.bb1;
    return Publish(rem_ids bb);
  } 
}. 

(**** DU-MB-BPRIV adversary type ****)
module type DU_MB_BPRIV_adv(O:DU_MB_BPRIV_oracles) = {

  (* adversary gets access to public data, public credentials, and secret credentials 
     of corrupted users, and uses a vote oracle to create ballot box BP.bb *)
  proc create_bb(pk:pkey, 
                 cu:(ident, secretcred) fmap, 
                 pu:(ident, pubcred) fmap,
                 hc: ident fset ) 
                 : (pubcred * ballot) list { O.vote, O.board, O.h, O.g }

  (* adversary gets to see the tally and outputs a result and proof *)
  proc get_tally(r:result, pi:prf) : result * prf { O.board, O.h, O.g } 

  (* adversary gets to make an inital guess after seeing either bb0 or bb1 *)
  proc initial_guess() : bool { O.h, O.g }  

  (* adversary gets access to verify oracle and gets to make a guess based
     on what he sees, i.e. who are happy etc. *)
  proc final_guess() : bool { O.verify, O.h, O.g }
                                                                    
}.


(**** Mb-BPRIV left side ****)

module DU_MB_BPRIV_L(V:VotingSystem, A:DU_MB_BPRIV_adv, 
                  H:HOracle.Oracle, G:GOracle.Oracle) = {
  
  module O = DU_MB_BPRIV_oracles(V, H, G, Left)
  module A = A(O)
  module V = V(H,G)

  proc main() : bool = {
    var i, id,p, c, valid, valid';
    var d;

    (* initialize global variables *)
    BP.vmap       <- empty; 
    BP.pubmap     <- empty;
    BP.secmap     <- empty;
    BP.secmapD    <- empty;
    BP.bb0        <- [];
    BP.bb1        <- [];
    BP.setchecked <- fset0;
    BP.sethappy   <- fset0;

    (* initialize random oracles *)
    H.init();
    G.init();

    (* setup *)
    (BP.pk, BP.sk) <@ V.setup(); 
    
    (* registration *)
    i <- 0;
    while (i < card BP.setidents) {
      id             <- nth witness (elems BP.setidents) i;
      (p,c)          <@ V.register(id,BP.pk,BP.sk);
      BP.secmap.[id] <- c;
      BP.pubmap.[id] <- p;

      if (id \in BP.setD) {
        BP.secmapD.[id] <- oget BP.secmap.[id];
      }
      i <- i + 1;
    }

    (* first bulletin board created by adversary *)
    BP.bb <@ A.create_bb(BP.pk, BP.secmapD, BP.pubmap, BP.setHcheck); 

    (* if sentences resulting in the adversary making a guess, 
       or in outputting a random bit *)
    if (!(BP.setHcheck \subset fdom BP.vmap)) {
      BP.d <$ {0,1};
    } else {
      valid <@ V.validboard(BP.bb, BP.pk);
      if (!valid) {
        BP.d <$ {0,1};
      } else {
        (BP.r, BP.pi) <@ V.tally(BP.bb, BP.pk, BP.sk);
             d        <@ A.initial_guess();
         (* adversary proposes new result and proof in bbstar *)
         BP.bbstar    <@ A.get_tally(BP.r, BP.pi);
         valid'       <@ V.verifytally((BP.pk, Publish BP.bb, BP.bbstar.`1), 
                                       BP.bbstar.`2);
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

(**** mb-BPRIV simulator type ****)

module type DU_MB_BPRIV_simulator = {
  proc init()    : unit
  proc o(x:g_in) : g_out
  proc prove(st: (pkey * pubBB * result)) : prf
}.

(**** mb-BPRIV right side ****)
module DU_MB_BPRIV_R(V:VotingSystem, A:DU_MB_BPRIV_adv, H:HOracle.Oracle,  
                  G:GOracle.Oracle, S:DU_MB_BPRIV_simulator, R:Recover') = {
  
  module O = DU_MB_BPRIV_oracles(V, H, S, Right)
  module A = A(O)

  proc main() : bool = {
    var i, id, p, c, valid, valid';
    var d;
    
    (* initialize global variables *)
    BP.vmap    <- empty; 
    BP.pubmap  <- empty;
    BP.secmap  <- empty;
    BP.secmapD <- empty;
    BP.bb0     <- [];
    BP.bb1     <- [];
    BP.setchecked <- fset0;
    BP.sethappy   <- fset0;

    (* initialize random oracles and simulator *)
    H.init();
    G.init();
    S.init();

    (* setup *)
    (BP.pk, BP.sk) <@ V(H,S).setup(); 
    
    (* registration *)
    i <- 0;
    while (i < card BP.setidents) {
      id             <- nth witness (elems BP.setidents) i;
      (p,c)          <@ V(H,S).register(id,BP.pk,BP.sk);
      BP.secmap.[id] <- c;
      BP.pubmap.[id] <- p;

      if (id \in BP.setD) {
        BP.secmapD.[id] <- oget BP.secmap.[id];
      }
      i <- i + 1;
    }

    (* first bulletin board created by adversary *)
    BP.bb <@ A.create_bb(BP.pk, BP.secmapD, BP.pubmap, BP.setHcheck); 

    (* if sentences resulting in the adversary making a guess or outputting a random bit *)
    if (!(BP.setHcheck \subset fdom BP.vmap)) {
      BP.d <$ {0,1};
    } else {
      valid <@ V(H,S).validboard(BP.bb, BP.pk);
      if (!valid) {
        BP.d <$ {0,1};
      } else {
         BP.bb'       <@ R.rec(rem_ids BP.bb0, rem_ids BP.bb1, BP.bb);
        (BP.r, BP.pi) <@ V(H,G).tally(BP.bb', BP.pk, BP.sk);
         BP.pi'       <@ S.prove(BP.pk, Publish BP.bb, BP.r);
           d          <@ A.initial_guess();
         (* adversary proposes new result and proof in bbstar *)
         BP.bbstar    <@ A.get_tally(BP.r, BP.pi');
         valid'       <@ V(H,S).verifytally((BP.pk, Publish BP.bb, BP.bbstar.`1), 
                                            BP.bbstar.`2);
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


(* Typechecks *)
section.

require import Real. 

declare module H <: HOracle.Oracle.
declare module G <: GOracle.Oracle.
declare module V <: VotingSystem. 
declare module A <: DU_MB_BPRIV_adv.  
declare module S <: DU_MB_BPRIV_simulator. 
declare module R <: Recover'. 

local lemma bpriv_typecheck &m : 
  exists eps, 
   `| Pr[DU_MB_BPRIV_L(V,A,H,G).main() @ &m : res] 
      - Pr[DU_MB_BPRIV_R(V,A,H,G,S,R).main() @ &m : res] | 
    <= eps by []. 

end section. 
