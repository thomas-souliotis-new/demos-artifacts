(* -------------------------------------------------------------------- *)
(* Sanity instance of Privacy.eca.  The abstract Sigma-protocol is       *)
(* instantiated with a trivial protocol (unit messages and coins), which *)
(* discharges every axiom of the theory: the abstraction is consistent.  *)
(* This instance says nothing about the security of a real Sigma-        *)
(* protocol; the paper uses the disjunctive Chaum-Pedersen protocol,     *)
(* whose special HVZK simulator is such a coin bijection.               *)
(* -------------------------------------------------------------------- *)
require import AllCore Distr DiffieHellman.
require Privacy.
import G GP GP.ZModE.

op x0 : exp.
op ch0 : bool -> bool -> unit = fun _ _ => tt.

clone Privacy as P22 with
  type prand <- unit,
  type fmsg  <- unit,
  type resp  <- unit,
  type chal  <- unit,
  op dprand  <- dunit tt,
  op commitP <- (fun _ _ _ => tt),
  op respond <- (fun _ _ _ _ => tt),
  op simul   <- (fun _ _ _ => (tt, tt)),
  op sbij    <- (fun _ _ _ t => t),
  op sbiji   <- (fun _ _ _ t => t),
  op chal_of <- ch0,
  op xx      <- x0
proof *.
realize dprand_ll by apply dunit_ll.
realize dprand_funi by move=> [] [].
realize sbijK by done.
realize sbijiK by done.
realize hvzk by done.

(* The instantiated statement: *)
print P22.privacy_abs.
