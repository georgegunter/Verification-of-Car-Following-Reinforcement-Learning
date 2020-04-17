(* ========================================================================= *)
(* THE INTERFACE TO EXTERNAL ALGEBRAIC DECISION METHODS / PROOF PROCEDURES   *)
(* (c) 2012 University of Cambridge, distributed under the MIT license       *)
(* ========================================================================= *)

structure RCF :> RCF =
struct

open Useful;
open Common;

(* Use only internal certifying RCF proof procedures.  Currently, we
   only support univariate RCF (we are complete for this fragment). *)

val cert_rcf_only = ref false;

(* Use Mathematica to isolate univariate real roots of input polynomials
   and print these in an Isabelle/HOL compatible format. *)

val m_root_iso_only = ref false;

(* Glossary --

   ADM:  Algebraic Decision Method,
   EADM: External ADM. *)

(* Datatype for ADM / EADM cooperation setting. *)

datatype adm_coop = EADM_ONLY | ICP_THEN_EADM | ICP_ONLY;

(* Datatype for External Algebraic Decision Method;
   Currently choices are between QepcadB and Mathematica. *)

datatype eadm = QEPCAD | MATHEMATICA | SMT_Z3;

val strategy_id = ref (SOME 1);

fun set_strategy_id n = strategy_id := SOME n;

(* Set log_rcf to true to generate .trace files with RCF subproblems
   in all supported formats (Mathematica, QepcadB, SMT2). *)

val log_rcf = ref false;

val eadm_on_univ = ref false;

val adm_coop_setting = ref EADM_ONLY;

val proj_order = ref true;

val use_exact_pi = ref true;

val eadm = ref SMT_Z3;

val extra_cpu_time = ref Time.zeroTime;

val kill_in_progress = ref false;

(* Should we generate traces for machine learning? *)

val trace_machine_learning = ref false;

(* Should we use ICP to search for an RCF counter-example
   before calling any RCF refutation procedures? *)

val check_icp_sat = ref false;

(* Should we check univariate relaxations of RCF problems
   for satisfiability (trusting only SAT answers) before
   attempting to full multivariate problems? The idea is
   to only do expensive SAT checking on full multivariate
   problems if the univariate relaxion is UNSAT. *)

val check_univ_rcf_sat = ref false;

(* Set the time limit of each EADM decision call.
   Note that this currently only affects Mathematica. *)

fun set_d_time_limit t =
    (Mathematica.mk_decision_time_limit := t);

(* Set Mathematica active options record. *)

fun set_mk_active_options opts =
    (Mathematica.mk_active_options := opts);

fun set_adm_coop_method (x) =
    (if ((x = ICP_THEN_EADM orelse x = ICP_ONLY)
         andalso not(IntvlsFP.check_fp_rm_works())) then
         die "To use ICP, you must use Poly/ML version 5.4.1 or later."
     else
         case x of
             EADM_ONLY => chatting 2 andalso chat "Enabled EADM only (no ICP).\n"
           | ICP_THEN_EADM => chatting 2 andalso chat "Enabled ICP followed by EADM.\n"
           | ICP_ONLY => (strategy_id := NONE;
                          chatting 2 andalso chat "Enabled ICP only (no EADM).\n");
     adm_coop_setting := x);

fun set_eadm QEPCAD = (chatting 3 andalso chat "EADM := QepcadB.\n";
                       strategy_id := NONE;
                       eadm := QEPCAD)
  | set_eadm MATHEMATICA = (chatting 3 andalso chat "EADM := Mathematica.\n";
                            strategy_id := NONE;
                            eadm := MATHEMATICA)
  | set_eadm SMT_Z3 = (chatting 3 andalso chat "EADM := SMT (Z3-nonlinear).\n";
                       SMT.use_model_history := false;
                       strategy_id := NONE;
                       eadm := SMT_Z3);

fun read_eadm () = !eadm; (* JPB addition to allow the appropriate environment variable to be checked in Metis.sml *)

fun icp_enabled () =
    !adm_coop_setting = ICP_THEN_EADM orelse !adm_coop_setting = ICP_ONLY;

(* Is CAD enabled?  Note that the CAD procedure could be provided by
   any number of EADM tools.  Some EADM tools which provide CAD may
   have their CAD machinery disabled; this is possible with
   Mathematica, for instance.  Currently, the following logic suffices
   to determine whether or not CAD is enabled. *)

fun cad_enabled () =
    (!adm_coop_setting = EADM_ONLY orelse !adm_coop_setting = ICP_THEN_EADM)
    andalso
    (!eadm = QEPCAD orelse
     !eadm = SMT_Z3 orelse
     (!eadm = MATHEMATICA andalso (#CAD (!Mathematica.mk_active_options))));

fun eadm_enabled () =
    !adm_coop_setting = EADM_ONLY orelse !adm_coop_setting = ICP_THEN_EADM;

fun set_proj_order b =
    (chatting 2 andalso chat ("CAD projection ordering := " ^ Bool.toString b);
     proj_order := b);

fun mathematica_rcf () = !eadm = MATHEMATICA;

(* Deprecated: val write_trace_file = false;
   Use log_rcf (above) now. *)

(* Total number of RCF+ formulas refuted by CAD *)

val num_refuted_by_eadm = ref 0;

(* Total number of RCF+ formulas refuted by ICP *)

val num_refuted_by_icp = ref 0;

(* Attempt ICP on a formula: We return TRUE iff ICP refutes the formula. *)

local open IntvlsFP in
open Nullsatz;
fun try_icp fm =
    (chatting 4 andalso chat("\n\nIn TRY_ICP!\n Formula for ICP: " ^ Formula.toString(fm) ^ ".\n\n");
     let val result = bap_on_fml(fm, 5, 2, 2)
     in
         case result of
             BAP_EMPTY => (chatting 2 andalso
                           chat("\n\n\n*** Branch-and-prune ICP refuted an RCF formula! ***\n\n\n");
                           num_refuted_by_icp := !num_refuted_by_icp + 1;
                           true)
           | _ => nsatz_search_on_fml fm 10
     end)
end;

val best_rat_models = ref [] : (string * Rat.rat) list list ref;

(* Check to see if any rational witnesses in the SMT model history
   satisfy an (implicitly existentially quantified) RCF formula. *)

fun check_sat_by_model_history xvars fm =
    let fun var_in_model v m =
            List.exists (fn (v', _) => v = v') m
        fun m_ok m = List.all (fn v => var_in_model v m) xvars
        fun check_model m = (m_ok m) andalso IntvlsFP.eval_qf_fml fm m
        fun find_sat_model ms left source =
            case ms of [] => false
                     | (m :: ms') =>
                       if check_model m then
                           (source := left @ ms';
                            best_rat_models := m :: (if (length (!best_rat_models) > 10)
                                                     then List.take (!best_rat_models, 10)
                                                     else (!best_rat_models));
                            (* print ("Model hit: ^ " ^ Int.toString (length left) ^ ".\n"); *)
                            true)
                       else find_sat_model ms' (m :: left) source
        val sat = (find_sat_model (!best_rat_models) [] best_rat_models orelse
                   find_sat_model (!SMT.model_history_rat) [] SMT.model_history_rat)
        (* val _ = print ("Length of Non-repeaters:" ^ (Int.toString (length (!SMT.model_history_rat))) ^ ", Repeaters: " ^ (Int.toString (length (!best_rat_models))) ^ "\n") *)
        (* val _ = chatting 4 andalso (if sat then chat ("(* RCF subproblem satisfied by model in model history! *)\n") else chat "") *)
    in
        sat
    end;

(* Inefficient version of the above function used for counting the
   number of successes during a search for common models. This is used
   to produce data in our paper submitted to CICM 2012, and not for
   production proving use. *)

val num_past_models = ref 0;
val successful_rat_models = ref [];

fun check_sat_by_model_history' xvars fm =
    let fun var_in_model v m =
            List.exists (fn (v', _) => v = v') m
        fun m_ok m = List.all (fn v => var_in_model v m) xvars
        fun check_model m = (m_ok m) andalso IntvlsFP.eval_qf_fml fm m
        val find_it = List.find check_model (!SMT.model_history_rat)
        val sat = case find_it of
                      SOME m => (successful_rat_models := Useful.setify (m :: (!successful_rat_models));
                                 true)
                    | NONE => false
        val _ = if sat then
                    (print ("Model worked! New successful num_past_models: ");
                     num_past_models := (!num_past_models) + 1;
                     print ((Int.toString(!num_past_models))
                            ^ " ; (Num stored, Num used) rational models: "
                            ^ (Int.toString(List.length (!SMT.model_history_rat)))
                            ^ ", "
                            ^ (Int.toString(List.length (!successful_rat_models)))
                            ^ ".\n"))
                else ()
    in
        sat
    end;

(***************************************************************************)
(* Some heterogenous RCF strategies.                                       *)

(* fun strat_0 opn xvars fm =
    if (length xvars = 1) then Qepcad.call_qepcad' opn xvars [] fm
    else case IntvlsFP.smt_rag_sat_on_fml fm of
             IntvlsFP.J_Sat _ => false
           | IntvlsFP.J_Unsat => true
           | IntvlsFP.J_Unknown =>
             SMT.z3_nlsat xvars fm 10000; *)

fun strat_0 opn xvars fm =
    if check_sat_by_model_history xvars fm
    then false (* return SAT *)
    else
        SMT.z3_nlsat xvars fm 100000;

fun strat_1 opn xvars fm =
    if check_sat_by_model_history xvars fm
    then false (* return SAT *)
    else
        SMT.z3_nlsat xvars fm 100000;

fun strat_2 opn xvars fm =
    SMT.z3_nlsat_no_factor xvars fm 100000;

fun strat_3 opn xvars fm =
    if check_sat_by_model_history xvars fm
    then false (* return SAT *)
    else
        if (length xvars = 1) then
            SMT.z3_nlsat xvars fm 100000
        else
            case IntvlsFP.smt_rag_sat_on_fml fm of
                IntvlsFP.J_Sat _ => false
              | IntvlsFP.J_Unsat => true
              | IntvlsFP.J_Unknown =>
                SMT.z3_nlsat_no_factor xvars fm 100000;

fun strat_4 opn xvars fm =
    if (length xvars = 1) then Qepcad.call_qepcad' opn xvars [] fm
    else SMT.z3_linear_relax xvars fm 1 orelse
         if (length xvars = 2) then Mathematica.mk_unsat_timelimit xvars fm 10
         else SMT.z3_nlsat xvars fm 10 orelse SMT.z3_nlsat xvars fm 20
              orelse Mathematica.mk_unsat_timelimit xvars fm 100;

(* fun strat_2 opn xvars fm =
    if (length xvars = 1)
    then case opn of
             true => Qepcad.call_qepcad' opn xvars [] fm
           | false => SMT.z3_nlsat xvars fm 100000
    else
        case IntvlsFP.smt_rag_sat_on_fml fm of
            IntvlsFP.J_Sat _ => false
          | IntvlsFP.J_Unsat => true
          | IntvlsFP.J_Unknown =>
            SMT.z3_nlsat_no_factor xvars fm 100000; *)

fun strat_10 opn xvars fm =
    if (length xvars = 1) then Qepcad.call_qepcad' opn xvars [] fm
    else if (length xvars = 2) then Mathematica.mk_s_resolve xvars [] fm false
    else SMT.z3_linear_relax xvars fm 1 orelse SMT.z3_nlsat xvars fm 10;

fun strat_11 opn xvars fm =
    if (length xvars = 1) then Qepcad.call_qepcad' opn xvars [] fm
    else if (length xvars <= 5) then
        (SMT.z3_nlsat xvars fm 10000
         orelse Mathematica.mk_unsat_timelimit xvars fm 20)
    else (SMT.z3_linear_relax xvars fm 1000
          orelse Mathematica.mk_unsat_timelimit xvars fm 20);

fun exec_strategy id opn xvars uvars fm =
    if uvars=[] then
        case id of
            0 => strat_0 opn xvars fm
          | 1 => strat_1 opn xvars fm
          | 2 => strat_2 opn xvars fm
          | 3 => strat_3 opn xvars fm
          | 4 => strat_4 opn xvars fm
          | _ => raise Useful.Error ("Unknown strategy #" ^ (Int.toString id))
    else false;

(* Run an RCF `quick decision,' taking into account model sharing.
   This is used for speculative RCF.

   We return a Common.tv value. *)

fun rcf_quick_decision xvars fm =
    if check_sat_by_model_history xvars fm
    then Common.Sat NONE
    else SMT.z3_nlsat_quick_check xvars fm;

(***************************************************************************)

(* Some simple machinery to log certain RCF formulas and export them
   as MetiTarski problems.  We do this so that we can use the runmetit
   script and its accompanying STATUS-* file analysis tools to help us
   find RCF problems which perform much differently under different
   RCF proof methods. This takes place in a directory called
   $HOME/rcf_logs/. *)

fun tptp_print_rat (q : Rat.rat) = Rat.toString q;

fun tptp_print_term t =
  case t of
    Term.Var x => Common.varname x
  | Term.Rat r => tptp_print_rat r
    (* Taking care that our output formula will be the negation of our given existential
       RCF formula, so we want its variables to not have the prefix "sko"! *)
  | Term.Fn (s,[]) => if String.isPrefix "sko" s then
                          String.extract (Common.no_underscores s, 3, NONE)
                      else Common.no_underscores s
  | Term.Fn("-", [tm]) => "(-" ^ (tptp_print_term tm) ^ ")"
  | Term.Fn("^", [tm1, tm2]) => "(" ^ (tptp_print_term tm1) ^ " ^ " ^ (tptp_print_term tm2) ^ ")"
  | Term.Fn("*", [tm1, tm2]) => "(" ^ (tptp_print_term tm1) ^ " * " ^ (tptp_print_term tm2) ^ ")"
  | Term.Fn("-", [tm1, tm2]) => "(" ^ (tptp_print_term tm1) ^ " - " ^ (tptp_print_term tm2) ^ ")"
  | Term.Fn("+", [tm1, tm2]) => "(" ^ (tptp_print_term tm1) ^ " + " ^ (tptp_print_term tm2) ^ ")"
  | Term.Fn(a,_) => raise Useful.Error ("tptp_print_term: no match for " ^ a);

fun tptp_print_atom ((reln, [x, y]) : Atom.atom) =
    "(" ^ (tptp_print_term x) ^ " " ^ reln ^ " " ^ (tptp_print_term y) ^ ")"
  | tptp_print_atom _ = raise Useful.Error "tptp_print_atom: atom's reln must be binary";

local open Formula
in
  fun tptp_print_fml False = "(0=1)"
    | tptp_print_fml True  = "(0=0)"
    | tptp_print_fml (Atom a) = tptp_print_atom a
    | tptp_print_fml (Not p)  = "~" ^ (tptp_print_fml p)
    | tptp_print_fml (And(p,q)) = "(" ^ (tptp_print_fml p) ^ " & " ^ (tptp_print_fml q) ^ ")"
    | tptp_print_fml (Or(p,q))  = "(" ^ (tptp_print_fml p) ^ " | " ^ (tptp_print_fml q) ^ ")"
    | tptp_print_fml (Imp(p,q)) = "(" ^ (tptp_print_fml p) ^ " => " ^ (tptp_print_fml q) ^ ")"
    | tptp_print_fml (Iff(p,q)) = "(" ^ (tptp_print_fml p) ^ " <=> " ^ (tptp_print_fml q) ^ ")"
    | tptp_print_fml (Forall(x,p)) = tptp_qquant "!" (x,p)
    | tptp_print_fml (Exists(x,p)) = tptp_qquant "?" (x,p)
  and tptp_qquant qname (x,p) = qname ^ "[" ^ (Name.toString x) ^ "] : (" ^ (tptp_print_fml p) ^ ")"
end;

val rcf_trace = ref (NONE : TextIO.outstream option);

fun open_rcf_trace() = case !rcf_trace of
    SOME os => os
  | NONE =>
      let val {base,...} = OS.Path.splitBaseExt
                             (List.last (CommandLine.arguments ()) handle Empty => "XXX")
          val os = TextIO.openOut(base ^ ".trace");
      in rcf_trace := SOME os; os
      end;

fun log_rcf_to_file xvars fm =
    let val rcf_os = open_rcf_trace()
    in
        TextIO.output(rcf_os, "-----[begin problem]-----\n"
                              ^ "% In Mathematica format:\n"
                              ^ ("Timing[" ^ (Mathematica.mk_resolve_str xvars [] fm (!use_exact_pi)) ^ "]")
                              ^ "\n\n"
                              ^ "% In QepcadB format:\n"
                              ^ (Qepcad.qepcad_str xvars fm)
                              ^ "\n\n"
                              ^ "% In SMTLib2 format:\n"
                              ^ (SMT.smt_print_fml_with_consts_oneline xvars fm)
                              ^ "\n-----[end problem]-----\n\n")
    end;

(* Call the activated EADM: We return TRUE iff EADM refutes the formula. *)

(* If machine learning traces are being generated, then we have to actually
   open a new QepcadB session every time we encounter a problem.  This is so
   that we can get timing information, which requires that the QepcadB
   process be closed before its timing can be obtained.

   Moreover, the cutime measurement is cummulative for all previous child
   processes.  Hence, we must do a little arithmetic on cutime to find out
   the time taken by the most recent QepcadB call.

   Tricky! *)

fun call_eadm _ _ _ Formula.True = false
  | call_eadm _ _ _ Formula.False = true
  | call_eadm opn xvars uvars fm =
        let val result = case !eadm of
                             QEPCAD => Qepcad.call_qepcad' opn xvars uvars fm
                           | MATHEMATICA => Mathematica.mk_s_resolve xvars uvars fm (!use_exact_pi)
                           | SMT_Z3 => if (uvars=[]) then
                                           (print "call_eadm!";
                                            SMT.smt_unsat xvars fm)
                                           (* SMT.z3_linear_relax xvars fm 1 *)
                                           (* SMT.z3_nlsat xvars fm 100 *)
                                           (* SMT.z3_nl_arith xvars fm 10 *)
                                           (* SMT.z3_nl_arith_gb xvars fm 10 *)
                                       else false
            val _ = if result then num_refuted_by_eadm := !num_refuted_by_eadm + 1 else ()
        in result end;

(* Compute a univariate relaxation of a purely existential RCF
   formula.  We return a quantifier-free formula which only uses the
   Skolem constant "x".  *)

local open Formula Term in

fun univ_relax_tm (Var _) = raise (Useful.Error "Can only univ_relax purely existential RCF sentences.")
  | univ_relax_tm (Rat q) = (Rat q)
  | univ_relax_tm (Fn (_, [])) = (Fn ("x", []))
  | univ_relax_tm (Fn (func_sym, [t1, t2])) = (Fn (func_sym, [univ_relax_tm t1, univ_relax_tm t2]))
  | univ_relax_tm (Fn (func_sym, [t])) = (Fn (func_sym, [univ_relax_tm t]));

fun univ_relax_fm True = True
  | univ_relax_fm False = False
  | univ_relax_fm (Atom (p, [t])) = Atom (p, [univ_relax_tm t])
  | univ_relax_fm (Atom (p, [t1, t2])) = Atom (p, [univ_relax_tm t1, univ_relax_tm t2])
  | univ_relax_fm (Not f) = Not (univ_relax_fm f)
  | univ_relax_fm (And (f1, f2)) = And (univ_relax_fm f1, univ_relax_fm f2)
  | univ_relax_fm (Or (f1, f2)) = Or (univ_relax_fm f1, univ_relax_fm f2)
  | univ_relax_fm (Imp (f1, f2)) = Imp (univ_relax_fm f1, univ_relax_fm f2)
  | univ_relax_fm (Iff (f1, f2)) = Iff (univ_relax_fm f1, univ_relax_fm f2)
  | univ_relax_fm (Exists (_, f)) = univ_relax_fm f
  | univ_relax_fm (Forall _) = raise Useful.Error "Can only univ_relax purely existential RCF sentences.";
end;

(* Version of Call_EADM for using univariate relaxations to check SAT
   of multivariate RCF formulae.  Note that unlike call_eadm above, we
   return TRUE iff we recognize (univ. relaxation of) FM to be SAT. *)

fun call_eadm_univ_sat Formula.True = true
  | call_eadm_univ_sat Formula.False = false
  | call_eadm_univ_sat fm =
    let val univ_relaxation = univ_relax_fm fm
        val result = if !eadm = QEPCAD then
                         Qepcad.call_qepcad_sat univ_relaxation
                     else Mathematica.mk_s_resolve_sat univ_relaxation
        val _ = if result then (chatting 3 andalso chat(">>> Univ_Relax filtered out SAT RCF formula!\n")) else true
    in result end;

fun non_label (_, (_,ts)) = not (null ts);

val fmlOfClause = Formula.listMkDisj o map Literal.toFormula o List.filter non_label o LiteralSet.toList;

(* Eliminate occurrences of true or false: CAD does not like them! *)

fun simpkConj fms =
      if List.exists (fn Formula.False => true | _ => false) fms then Formula.False
      else Formula.listMkConj (List.filter (fn Formula.True => false | _ => true) fms)

(* ---------------------------------------------------------------------- *)
(* Use Hashing to Detect Duplicates.                                      *)
(* ---------------------------------------------------------------------- *)

fun hash_literal_set_list [] = 0w0
  | hash_literal_set_list (x::xs) =
      Polyhash.hashw (LiteralSet.hash x, hash_literal_set_list xs);

val equal_literal_set_list = ListPair.all (uncurry LiteralSet.equal)

exception HASH_RCF;

(*Create a hash table for clauses, of the given size*)
fun mk_rcf_table n =
      Polyhash.mkTable (Word.toIntX o hash_literal_set_list, equal_literal_set_list)
                       (n, HASH_RCF);

val rcf_full_ht = mk_rcf_table 7000
val rcf_fml_ht = mk_rcf_table 7000

fun thm_mem x = List.exists (LiteralSet.equal x);
fun thm_subset s t = List.all (fn x => thm_mem x t) s;

(*Deletes trivial equalities (constant symbol = rational number) to eliminate a
  variable prior to calling QEPCAD. Could be generalised.*)
fun is_constdef (true, ("=",[s,t])) =
        (Term.isConst s andalso Term.isRat t) orelse (Term.isConst t andalso Term.isRat s)
  | is_constdef _ = false;

fun no_constdefs lits = LiteralSet.all (not o is_constdef) lits;

fun isOpen (false, ("<=", [_,_])) = true
  | isOpen (false, ("=", [_,_])) = true
  | isOpen _ = false

val varsInLits =
  LiteralSet.foldl (fn (lit,s) => NameSet.union s (Literal.freeVars lit)) NameSet.empty;

fun cache_call_rcf (ncl,ths) doit =
  let val lits_ncl = LiteralSet.fromList ncl
  in
      case Polyhash.peek rcf_full_ht (lits_ncl::ths) of
          SOME b => (chatting 3 andalso
                       chat ("Cached RCF result for\n" ^
                             Formula.toString
                               (simpkConj (map Literal.toFormula ncl @ map fmlOfClause ths)));
                     b)
        | NONE =>
           case Polyhash.peek rcf_fml_ht [lits_ncl] of
              SOME ths0 =>
                if thm_subset ths0 ths then
                    (chatting 3 andalso
                     chat ("Cached RCF formula (subset):\n" ^
                           Formula.toString (simpkConj (map Literal.toFormula ncl)));
                     true)
                else doit (ncl,ths)
            | NONE => doit (ncl,ths)
  end;

(* Variant of cache_call_rcf for quick-decision *)

fun cache_call_rcf_quick_decision (ncl,ths) doit =
  let val lits_ncl = LiteralSet.fromList ncl
  in
      case Polyhash.peek rcf_full_ht (lits_ncl::ths) of
          SOME b => (chatting 3 andalso
                       chat ("Cached RCF result for\n" ^
                             Formula.toString
                               (simpkConj (map Literal.toFormula ncl @ map fmlOfClause ths)));
                     case b of
                         true => Common.Unsat
                       | false => Common.Sat NONE)
        | NONE =>
           case Polyhash.peek rcf_fml_ht [lits_ncl] of
              SOME ths0 =>
                if thm_subset ths0 ths then
                    (chatting 3 andalso
                     chat ("Cached RCF formula (subset):\n" ^
                           Formula.toString (simpkConj (map Literal.toFormula ncl)));
                     Common.Unsat)
                else doit (ncl,ths)
            | NONE => doit (ncl,ths)
  end;


(*Variables in the clause being examined (cl) are taken as fixed and are therefore
  combined with constants of the clause and quantified existentially.
  Variables in the global algebraic clauses (ths) are taken as universal.
  qepcad_abs_fm could be inserted here...
*)

val last_witness = ref ([], []) : ((string list) * IntvlsFP.vr_map) ref;

fun call_rcf_conj cl ths =
  let val ths = List.filter no_constdefs (map (LiteralSet.filter non_label) ths)
      val ncl = map Literal.negate (List.filter non_label (LiteralSet.toList cl))
                (*A CONJUNCTIVE list of negated literals*)
      val opn_ths = List.filter (LiteralSet.all isOpen) ths
      val opn_ncl = List.filter isOpen ncl
      val uvars = map varname (NameSet.toList
                   (foldl (fn (th,s) => NameSet.union s (varsInLits th)) NameSet.empty ths))
      fun doit opn (ncl,ths) =
        let val fm = simpkConj (map Literal.toFormula ncl @ map fmlOfClause ths)
            val fm_skos = rev (NameSet.toList (Formula.freeSkos fm))
            val lits_ncl = LiteralSet.fromList ncl
            val fms_vars = map varname (NameSet.toList (varsInLits lits_ncl))
            val xvars = (fm_skos@fms_vars)
            (* spo: Should we compute a projection ordering? *)
            val spo = (!strategy_id = NONE) andalso !proj_order andalso cad_enabled()
                      andalso null uvars andalso length xvars > 1
                      (* andalso not(mathematica_rcf()) *)
            val xvars' = if spo then CADProjO.proj_order_fm(fm) else xvars
            val _ = if !log_rcf then (log_rcf_to_file xvars' fm) else ()
            val _ = spo andalso chatting 3 andalso xvars <> xvars' andalso
                    chat ("Default CAD projection order: " ^ string_tuple(xvars) ^ ", \n"
                          ^ "Revised CAD projection order: " ^ string_tuple(xvars') ^ ".\n")
            val sat_j =
                (* Only use internal certifying RCF procedures *)
                if !cert_rcf_only then
                    case CertRCFp.univ_refute fm of
                        true => IntvlsFP.J_Unsat
                      | false => IntvlsFP.J_Unknown
                else
                    (* Use other methods beyond internal certifying ones *)
                    if !check_icp_sat (* andalso (length xvars') > 1 *) andalso uvars = []
                       andalso fms_vars = [] then
                        let val (vs, b) = !last_witness in
                            if (vs = xvars') andalso IntvlsFP.eval_qf_fml fm b
                            then (IntvlsFP.J_Sat b) else IntvlsFP.icp_sat_on_fml fm
                        end
                    else IntvlsFP.J_Unknown
            val sat_j' = case sat_j of
                             IntvlsFP.J_Unknown => if not(!cert_rcf_only) andalso !check_univ_rcf_sat
                                                      andalso length xvars > 1
                                                      andalso call_eadm_univ_sat fm then
                                                       IntvlsFP.J_Sat [] else IntvlsFP.J_Unknown
                           | _ => sat_j
            val b = case sat_j' of
                        IntvlsFP.J_Sat b => (if not(null b) then last_witness := (xvars', b) else (); false)
                      | IntvlsFP.J_Unsat => true
                      | IntvlsFP.J_Unknown =>
                        if not(!strategy_id = NONE orelse !cert_rcf_only = true) then
                            exec_strategy (case !strategy_id of SOME n => n | NONE => 0) opn xvars' uvars fm
                        else (if !eadm_on_univ andalso length xvars = 1 andalso not(!cert_rcf_only) then
                             ((* print "eadm_univ..."; *)
                              let val r = call_eadm opn xvars' uvars fm
                              in ((* print (if r then "success" else "failure"); *)
                                  r) end) else false)
                        orelse
                        (not(!eadm_on_univ andalso length xvars = 1)
                         andalso not(!cert_rcf_only)
                         andalso icp_enabled() andalso try_icp(fm)) orelse
                        (not(!eadm_on_univ andalso length xvars = 1)
                         andalso not(!cert_rcf_only)
                         andalso eadm_enabled() andalso call_eadm opn xvars' uvars fm)
        in  Polyhash.insert rcf_full_ht (lits_ncl::ths, b);
            if b then Polyhash.insert rcf_fml_ht ([lits_ncl], ths) else ();
             b
        end
  in
    if null uvars then
       if List.all isOpen ncl andalso length opn_ths = length ths (*open!!*)
       then cache_call_rcf (ncl,ths) (doit true)  (*F-quantifier on original formula*)
       else cache_call_rcf (opn_ncl, opn_ths) (doit true)
            orelse cache_call_rcf (ncl,ths) (doit false)
    else cache_call_rcf (ncl,ths) (doit false)
  end;

(* A `quick-decision' version of call_rcf_conj.  Note that this
   returns a Common.tv truth value.  Also, note that it interoperates
   with the rcf_cache (SAT or UNSAT answers are stored in the
   cache. UNKNOWN answers are not.)  Also, note that this can only be
   used with purely existential formulas. We will automatically return
   UNKNOWN for any formulas with universally quantified variables. *)

fun call_rcf_conj_quick_decision cl ths =
  let val ths = List.filter no_constdefs (map (LiteralSet.filter non_label) ths)
      val ncl = map Literal.negate (List.filter non_label (LiteralSet.toList cl))
                (*A CONJUNCTIVE list of negated literals*)
      val opn_ths = List.filter (LiteralSet.all isOpen) ths
      val opn_ncl = List.filter isOpen ncl
      val uvars = map varname (NameSet.toList
                   (foldl (fn (th,s) => NameSet.union s (varsInLits th)) NameSet.empty ths))
      fun doit (ncl,ths) =
        let val fm = simpkConj (map Literal.toFormula ncl @ map fmlOfClause ths)
            val fm_skos = rev (NameSet.toList (Formula.freeSkos fm))
            val lits_ncl = LiteralSet.fromList ncl
            val fms_vars = map varname (NameSet.toList (varsInLits lits_ncl))
            val xvars = (fm_skos@fms_vars)
            val _ = if !log_rcf then (log_rcf_to_file xvars fm) else ()
            val b = rcf_quick_decision xvars fm
        in (case b of
                Common.Unsat => (Polyhash.insert rcf_full_ht (lits_ncl::ths, true);
                                 Polyhash.insert rcf_fml_ht ([lits_ncl], ths))
              | Common.Sat _ => Polyhash.insert rcf_full_ht (lits_ncl::ths, false)
              | Common.Unknown => ();
            b)
        end
  in
    if null uvars then
        cache_call_rcf_quick_decision (ncl,ths) doit
    else Common.Unknown
  end;



(* Close external tools.
   If a tool generates subprocesses which won't be timed by the normal SML
   timing mechanisms, then we add this to the global ref extra_cpu_time. *)

fun close_with_time ignore_outcome =
    (if !Mathematica.mathematica_used then
         (if not(!kill_in_progress) then
              let val mk_time = Mathematica.mk_cpu_time()
                  val _ = Mathematica.mk_close ignore_outcome
              in
                  extra_cpu_time := Time.+(!extra_cpu_time, mk_time)
              end
          else Mathematica.mk_close ignore_outcome) else ();
     if !Qepcad.qepcad_used then Qepcad.close_qepcad ignore_outcome else ();
     if !SMT.smt_used then SMT.smt_close ignore_outcome else ());

(* Is a literal's relation symbol `<='? *)

fun is_lit_leq (_, ("<=", _)) = true
  | is_lit_leq _ = false;


end
