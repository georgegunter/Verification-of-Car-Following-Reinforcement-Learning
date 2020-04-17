(* ======================================================================== *)
(*      Bivariate Polynomial Resultants via a Modular Euclidean Method      *)
(*                                                                          *)
(*  by G.O.Passmore, LFCS, Univ. Edinburgh and Clare Hall, Univ. Cambridge  *)
(* Contact: (e) grant.passmore@cl.cam.ac.uk   (w) www.cl.cam.ac.uk/~gp351/. *)
(* ======================================================================== *)

signature Resultant =
sig

(* Resultant_x(f,g) for polynomials f,g in Q[x] *)

val univ_resultant : Algebra.poly -> Algebra.poly -> Rat.rat;

(* Resultant_x(f,g) for polynomials f,g in Q[y,x] *)

val biv_resultant : Algebra.poly -> Algebra.poly -> Algebra.poly;

end
