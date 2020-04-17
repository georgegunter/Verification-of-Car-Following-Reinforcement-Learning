(* ======================================================================== *)
(*               Core Arithmetical and Narrowing Machinery for              *)
(*                  Generalised (Non-Compact) Real Intervals                *)
(*                                                                          *)
(*    with interval endpoints taken over FP_ext = (FP union {-inf, +inf})   *)
(*       (our +-inf are distinct from the floating point infinities)        *)
(*                                                                          *)
(* by G.O.Passmore, Cambridge Computer Laboratory and LFCS, Edinburgh, 2011 *)
(* Contact: (e) grant.passmore@cl.cam.ac.uk   (w) www.cl.cam.ac.uk/~gp351/. *)
(* ======================================================================== *)

signature IntvlsFP = 
sig

(* Boundary type: Either left closed ('[') or right closed (']') *)

datatype bt = LEFT_CLOSED | RIGHT_CLOSED;

(* Infinity type *)

datatype infty = NEG_INFTY | POS_INFTY;

(* Endpoint type, Q_ext: Either an exact precision rational or +/- infty *)

datatype ep = Num of real | Infty of infty;

(* Generalised interval type: a left boundary type, left and right
   endpoints, and a right boundary type. *)

type intvl = bt * ep * ep * bt;

(* Type for var_ids *)

type var_id = int;

(* Type for interval contexts *)

type intvl_ctxt = (var_id, intvl) Polyhash.hash_table;

(* Type for Branch-and-Prune ICP return values: 

   Either

    (i) BAP ICP made no progress on the problem (no term in the
    formula could be bound within any interval other than ]-inf,
    +inf[), or
 
    (ii) BAP ICP made progress but did not narrow any term to be
    within an empty interval, or

    (iii) BAP ICP did narrow some term to be within an empty interval,
    thus refuting the satisfiability of the formula upon which ICP was
    applied. *)

datatype bap_r = BAP_EMPTY | BAP_RESULT of intvl_ctxt list | BAP_NO_PROGRESS;

(* Run ICP using branch and prune on ``ICP friendly'' formulas. *)

val bap_on_fml : Formula.formula * int * int * int -> bap_r;

(* Run ICP using branch and prune on a list of atoms. *)

val bap_on_al : Atom.atom list * int * int * int -> bap_r;

(* Make sure that the modification of floating point rounding
   modes is working in the version of Poly/ML being used. *)

val check_fp_rm_works : unit -> bool;

(* ICP SAT-search judgment datatype *)

type vr_map = (string * Rat.rat) list;
datatype icp_sat_j = J_Unsat | J_Sat of vr_map | J_Unknown;

(* ICP-based SAT witness finding procedure. *)

val icp_sat_on_fml : Formula.formula -> icp_sat_j;

val eval_qf_fml : Formula.formula -> vr_map -> bool;

(* SOME quantifier-free matrix of Existential formula, 
   NONE if not purely existential. *)

val qfm : Formula.formula -> Formula.formula option;

(* Convert formula to DNF list of atom lists *)

val dnf : Formula.formula -> Formula.formula list list;

exception DNF_TOO_LARGE;

val icp_atom_lst : Formula.formula list -> (string * Term.term list) list;

val var_intervals_from_al : Atom.atom list -> ( (string * intvl) list ) option;

val smt_rag_sat_on_fml : Formula.formula -> icp_sat_j;

(* Floating point <-> Rat.rat rationals *)

val rat_to_fp_lo : Rat.rat -> real;

val rat_to_fp_hi : Rat.rat -> real;

(* Manipulating floating point rounding mode *)

(* Floating point rounding mode *)

datatype fp_rm = LO | HI | NM;

(* Set floating point rounding mode *)

val set_rm : fp_rm -> unit;

end;
