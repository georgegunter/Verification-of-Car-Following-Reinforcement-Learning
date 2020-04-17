(* ======================================================================== *)
(*             A Proof-Producing Exists RCF proof procedure                 *)
(*                   based on the Real Nullstellensatz                      *)
(*          (including Groebner reduction, in the spirit of Tiwari)         *)
(*                                                                          *)
(* by G.O.Passmore, Cambridge Computer Laboratory and LFCS, Edinburgh, 2012 *)
(* Contact: (e) grant.passmore@cl.cam.ac.uk   (w) www.cl.cam.ac.uk/~gp351/. *)
(* ======================================================================== *)

signature Nullsatz =
sig

val nsatz_search : Atom.atom list -> int -> bool;

val nsatz_search_on_fml : Formula.formula -> int -> bool;

end;
