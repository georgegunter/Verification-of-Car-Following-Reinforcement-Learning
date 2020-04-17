(* ======================================================================== *)
(* Connection between RAHD/MetiTarski and SMT solvers (Z3 only, currently)  *)
(*                                                                          *)
(* by G.O.Passmore, Cambridge Computer Laboratory and LFCS, Edinburgh, 2012 *)
(* Contact: (e) grant.passmore@cl.cam.ac.uk   (w) www.cl.cam.ac.uk/~gp351/. *)
(* ======================================================================== *)

signature SMT =
sig

val determine_Z3_version : unit -> unit
val Z3_write_rcf_problems_to_file : bool ref
val core_file_name : string ref
val smt_unsat : string list -> Formula.formula -> bool;
val smt_judgment_with_strategy : string list -> Formula.formula -> string -> string -> Common.tv;
val z3_linear_relax : string list -> Formula.formula -> int -> bool;
val z3_nlsat : string list -> Formula.formula -> int -> bool;
val z3_nlsat_no_factor : string list -> Formula.formula -> int -> bool;
val z3_nl_arith : string list -> Formula.formula -> int -> bool;
val z3_nl_arith_gb : string list -> Formula.formula -> int -> bool;
val z3_no_conflicts_judgment : string list -> Formula.formula -> Common.tv;
val z3_nlsat_quick_check : string list -> Formula.formula -> Common.tv;
val smt_close : bool -> unit;
val smt_used : bool ref;
val RCF_time_limit : int ref;
val smt_print_fml_with_consts_oneline : string list -> Formula.formula -> string;
val smt_print_fml_with_consts : string list -> Formula.formula -> string;
val z3_parse_model : string -> (string * real * bool) list;
val use_model_history : bool ref;
val model_history_rat : (string * Rat.rat) list list ref;
val model_history_float : (string * real) list list ref;
end;
