(* ======================================================================== *)
(*       Connection between MetiTarski formulas and polynomial algebra      *)
(*                 version 0.0a, last updated 19-July-2011                  *)
(*                                                                          *)
(* by G.O.Passmore, Cambridge Computer Laboratory and LFCS, Edinburgh, 2011 *)
(* Contact: (e) grant.passmore@cl.cam.ac.uk   (w) www.cl.cam.ac.uk/~gp351/. *)
(* ======================================================================== *)

signature MTAlgebra = sig

(* MT<->Algebraic polynomial notation hash table type *)

type mt_var_vid_ht;

val mk_vv_ht : int -> (string, Algebra.var_id) Polyhash.hash_table;

val poly_of_tm : mt_var_vid_ht * Term.term -> Algebra.poly;

val poly_of_atom : mt_var_vid_ht * Atom.atom -> Algebra.poly;

val polys_of_fm : mt_var_vid_ht * Formula.formula -> Algebra.poly list;

val eval_fm_at_sp : Formula.formula -> RealAlg.real_alg -> bool -> bool;

end
