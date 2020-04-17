(* ======================================================================== *)
(*                     Partial CAD Projection Ordering                      *)
(*                                                                          *)
(* by G.O.Passmore, Cambridge Computer Laboratory and LFCS, Edinburgh, 2011 *)
(* Contact: (e) grant.passmore@cl.cam.ac.uk   (w) www.cl.cam.ac.uk/~gp351/. *)
(* ======================================================================== *)

signature CADProjO = sig

val proj_order_fm : Formula.formula -> string list;

end;
