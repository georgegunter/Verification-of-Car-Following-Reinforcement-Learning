
(* ======================================================================== *)
(*                    Sturm Chains and Real Root Isolation                  *)
(*                                                                          *)
(*  by G.O.Passmore, LFCS, Univ. Edinburgh and Clare Hall, Univ. Cambridge  *)
(* Contact: (e) grant.passmore@cl.cam.ac.uk   (w) www.cl.cam.ac.uk/~gp351/. *)
(* ======================================================================== *)

signature Sturm =
sig

datatype sign = NEG | ZERO | POS;

val d_dx : Algebra.poly -> Algebra.poly
val square_free : Algebra.poly -> Algebra.poly
val sturm_chain : Algebra.poly -> Algebra.poly list
val gen_sturm_chain : Algebra.poly -> Algebra.poly -> Algebra.poly list
val sign_of_rat : Rat.rat -> sign
val num_sign_changes : sign list -> int
val isolate_roots : Algebra.poly -> (Rat.rat * Rat.rat) list
val isolate_roots_no_overlap : Algebra.poly -> (Rat.rat * Rat.rat) list
val refine_root : Algebra.poly -> (Rat.rat * Rat.rat) -> (Rat.rat * Rat.rat)
val num_roots_in_cl_intvl : Algebra.poly -> (Rat.rat * Rat.rat) -> int

end
