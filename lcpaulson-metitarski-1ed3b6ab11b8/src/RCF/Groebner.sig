(* ======================================================================== *)
(*        Groebner basis computation using Buchberger's Algorithm           *)
(*                                                                          *)
(* by G.O.Passmore, Cambridge Computer Laboratory and LFCS, Edinburgh, 2011 *)
(* Contact: (e) grant.passmore@cl.cam.ac.uk   (w) www.cl.cam.ac.uk/~gp351/. *)
(* ======================================================================== *)

signature Groebner =
sig

(* Commuting pairs for S-polynomial waiting lists *)

val uc_pairs : 'a list -> ('a * 'a) list

(* S-polynomial *)

val s_poly : Algebra.poly -> Algebra.poly -> Algebra.poly;

(* Multivariate polynomial division *)

val p_div : Algebra.poly -> Algebra.poly list -> (Algebra.poly array * Algebra.poly);

(* Groebner basis construction *)

val buchberger : Algebra.poly list -> Algebra.poly list;

(* Reduce a Groebner basis *)

val gb_reduce : Algebra.poly list -> Algebra.poly list;

end;
