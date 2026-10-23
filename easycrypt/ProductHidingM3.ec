(* -------------------------------------------------------------------- *)
(* Sanity instance of ProductHiding.eca: m = 3 candidates, encoding set  *)
(* X = {1, x, x^2} for an arbitrary x in Z_q, and the two permutations    *)
(* sigma0 = (1, x, x^2), sigma1 = (x, 1, x^2).  The clone discharges all *)
(* parameter axioms of the abstract theory, so Lemma 2 is not vacuous.   *)
(* -------------------------------------------------------------------- *)
require import AllCore List DiffieHellman.
require ProductHiding.
import G GP GP.ZModE.

op x : exp.

clone ProductHiding as PH3 with
  op n      <- 2,
  op xs     <- [one; x; x * x],
  op sigma0 <- [one; x; x * x],
  op sigma1 <- [x; one; x * x]
proof *.
realize gt0_n by trivial.
realize size_xs by trivial.
realize perm_sigma0 by apply perm_eq_refl.
realize perm_sigma1 by rewrite perm_consCA perm_eq_refl.

(* The instantiated statement: *)
print PH3.product_hiding_abs.
