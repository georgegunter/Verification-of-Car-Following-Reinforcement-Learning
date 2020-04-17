(* ======================================================================== *)
(* Some common values useful for RCF related things.                        *)
(*                                                                          *)
(* by G.O.Passmore, Cambridge Computer Laboratory and LFCS, Edinburgh, 2012 *)
(* Contact: (e) grant.passmore@cl.cam.ac.uk   (w) www.cl.cam.ac.uk/~gp351/. *)
(* ======================================================================== *)

signature Common =
sig

(* Signal: subprocess cpu time limit exceeded *)

val sigxcpu : Posix.Signal.signal;

val no_underscores : string -> string;

val varname : string -> string;

val string_tuple : string list -> string;

datatype mt = Real_Model of (string * real) list
	    | Rat_Model of (string * Rat.rat) list;

datatype tv = Sat of mt option | Unsat | Unknown;

exception JudgmentReached of tv;

val alpha_num : char -> bool;

val lex : char list -> string list;

val rat_of_float : real -> Rat.rat;

end;
