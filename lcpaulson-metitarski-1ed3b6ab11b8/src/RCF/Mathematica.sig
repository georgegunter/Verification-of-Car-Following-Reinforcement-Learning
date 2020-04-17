(* ======================================================================== *)
(*       Interface between MetiTarski and Mathematica's MathKernel          *)
(*                                                                          *)
(* by G.O.Passmore, Cambridge Computer Laboratory and LFCS, Edinburgh, 2012 *)
(* Contact: (e) grant.passmore@cl.cam.ac.uk   (w) www.cl.cam.ac.uk/~gp351/. *)
(* ======================================================================== *)

signature Mathematica =
sig

(* Datatypes for handling Mathematica RCF strategy options *)

datatype mk_tfa = O_True | O_False | O_Automatic;

type mk_opts =
     { Exact_Pi : bool,
       ARS_Decision : bool,
       Brown_Projection : bool,
       CAD : bool,
       CAD_Combine_Cells : mk_tfa,
       CAD_Default_Precision : real,
       CAD_Extra_Precision : real,
       CAD_Sort_Variables : bool,
       Equational_Constraints_CAD : mk_tfa,
       FGLM_Basis_Conversion : bool,
       FGLM_Elimination : mk_tfa,
       Generic_CAD : bool,
       Groebner_CAD : bool,
       Linear_Equations : bool,
       Linear_QE : mk_tfa,
       LW_Decision : bool,
       LW_Preprocessor : mk_tfa,
       Project_Algebraic : mk_tfa,
       Prove_Multiplicities : mk_tfa,
       Quadratic_QE : mk_tfa,
       QVS_Preprocessor : mk_tfa,
       Reduce_Powers : bool,
       Root_Reduced : bool,
       Simplex : bool,
       Thread_Or : bool,
       Zeng_Decision : bool};

(* The active set of options used when opening a MathKernel connection.
   See Mathematica.sml for the specifics of these default settings. *)

val mk_active_options : mk_opts ref;

(* Final bool argument for mk_s_cad and mk_s_resolve signifies whether or
   not "pi" should be treated as the exact mathematical pi in Mathematica. *)

val mk_s_resolve : string list -> string list -> Formula.formula -> bool -> bool;

(* Version of mk_s_resolve for univariate relaxations and SAT filtration. *)

val mk_s_resolve_sat : Formula.formula -> bool;

(* Check if an RCF formula is UNSAT using a time-limit *)

val mk_unsat_timelimit : string list -> Formula.formula -> int -> bool;

val sf_unsat : string list -> Formula.formula -> bool -> Time.time -> Common.tv;
val mk_decision_time_limit : Time.time ref;
val mk_close : bool -> unit;
val mk_cpu_time : unit -> Time.time;
val mathematica_used : bool ref;

(* Turn a Formula.formula into a Mathematica formula *)
val mk_s_str : string list -> string list -> Formula.formula -> bool -> string;

(* Turn an existential Formula.formula into a Mathematica Resolve[] string *)
val mk_resolve_str : string list -> string list -> Formula.formula -> bool -> string;

(* Use Mathematica to isolate real roots of univariate system only *)
val univ_m_root_iso : Formula.formula -> unit

end;
