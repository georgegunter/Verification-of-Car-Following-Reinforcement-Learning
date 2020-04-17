(* --------------------------------------------------------------------------- *)
(* Analysis of RCF+ formulas using decision methods (QEPCAD, Mathematica, ICP) *)
(* --------------------------------------------------------------------------- *)

signature RCF =
sig

val cert_rcf_only : bool ref;
val m_root_iso_only : bool ref;
val call_rcf_conj : LiteralSet.set -> LiteralSet.set list -> bool;
val call_rcf_conj_quick_decision : LiteralSet.set -> LiteralSet.set list -> Common.tv;
val close_with_time : bool -> unit;
val extra_cpu_time : Time.time ref;
val kill_in_progress : bool ref;

(* Glossary --

   ADM:  Algebraic Decision Method,
   EADM: External ADM. *)

datatype adm_coop = EADM_ONLY | ICP_THEN_EADM | ICP_ONLY;
datatype eadm = QEPCAD | MATHEMATICA | SMT_Z3;

val set_adm_coop_method : adm_coop -> unit;
val set_eadm : eadm -> unit;
val read_eadm : unit -> eadm;
val set_d_time_limit : Time.time -> unit;
val set_mk_active_options : Mathematica.mk_opts -> unit;

val icp_enabled : unit -> bool;
val cad_enabled : unit -> bool;

val num_refuted_by_eadm : int ref;
val num_refuted_by_icp : int ref;
val proj_order : bool ref;
val set_proj_order : bool -> unit;

val use_exact_pi : bool ref;

val trace_machine_learning : bool ref;

val check_icp_sat : bool ref;
val check_univ_rcf_sat : bool ref;
val eadm_on_univ : bool ref;
val set_strategy_id : int -> unit;
val strategy_id : int option ref;

end
