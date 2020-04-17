(* ========================================================================= *)
(* METITARSKI PROVER                                                         *)
(*                                                                           *)
(* Copyright (c) 2007-2011 Lawrence C Paulson                                *)
(* Copyright (c) 2001-2009 Joe Hurd                                          *)
(*                                                                           *)
(* MetiTarski is free software; you can redistribute it and/or modify        *)
(* it under the terms of the GNU General Public License as published by      *)
(* the Free Software Foundation; either version 2 of the License, or         *)
(* (at your option) any later version.                                       *)
(*                                                                           *)
(* MetiTarski is distributed in the hope that it will be useful,             *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of            *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the             *)
(* GNU General Public License for more details.                              *)
(*                                                                           *)
(* You should have received a copy of the GNU General Public License         *)
(* along with MetiTarski; if not, write to the Free Software                 *)
(* Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA *)
(* ========================================================================= *)

open Useful;

(* ------------------------------------------------------------------------- *)
(* The program name.                                                         *)
(* ------------------------------------------------------------------------- *)

val PROGRAM = "metit";

(* ------------------------------------------------------------------------- *)
(* Program options.                                                          *)
(* ------------------------------------------------------------------------- *)

val QUIET = ref false;

val TEST = ref false;

val TPTP : string option ref = ref NONE;

val cpu_limit = ref 600000;

(* Display a "." for Metis every 10 cpu secs and a "+" for RCF every 10 cpu secs
   This happens only with --verbose 1, that is, when !traceLevel=1. *)
val metis_symbol = ".";
val RCF_symbol = "+";
val metis_display_time_step = 10;
val RCF_display_time_step = 10;
val display_time_in_millisecs = 10000; (* used to determine if display is to be used at all *)
val next_metis_symbol_due = ref metis_display_time_step;
val next_RCF_symbol_due = ref RCF_display_time_step;

(* the following refers to the temporary file used for storing the tptp *)
(* expressions after filtering of comment lines and redundant brackets  *)
(* this is normally deleted but can be kept for debug purposes.         *)
(* If KEEP_TEMP_FILE is set to true then the temporary file is kept and *)
(* not deleted and the name is printed for the user.                    *)
val KEEP_TEMP_FILE =  false;

(* ---------------------------------------------------------- *)
(* flags/options to be used with the auto-including of axioms *)
(* ---------------------------------------------------------- *)
val autoInclude = ref false;
val extended = ref false;
val superExtended = ref false;
val linearLimits = ref false; (* include axioms for linear limits for sin and cos *)
val constantLimits = ref false;
val extendedFuncs = ref false;
val superExtendedFuncs = ref false;
val linearLimitsFuncs = ref false;
val constantLimitsFuncs = ref false; (* NB this currently is sin/cos same as linear limits *)
(* ---------------------------------------------------------- *)
(* flag to indicate iterative deepening on weights is allowed *)
(* when using autoInclude - this may be set in future from the*)
(* command line but for the time being is just turned on or   *)
(* off here.                                                  *)
(* Set it to true if you want iterative deepening.            *)
(* ---------------------------------------------------------- *)
val allowIterativeDeepening = ref false;

(* ------------------------------------------------------------------- *)
(* flag to indicate that an smt2 version of the file should be written *)
(* if it doesn't already exist.                                        *)
(* ------------------------------------------------------------------- *)
val writeSMTLIBfile = ref false;



val ITEMS = ["name","goal","clauses","size","category","proof","saturation"];

val extended_items = "all" :: ITEMS;

val show_items = map (fn s => (s, ref false)) ITEMS;

fun show_ref s =
    case List.find (equal s o fst) show_items of
      NONE => raise Bug ("item " ^ s ^ " not found")
    | SOME (_,r) => r;

fun show_set b = app (fn (_,r) => r := b) show_items;

fun showing s = not (!QUIET) andalso (s = "status" orelse !(show_ref s));

fun notshowing s = not (showing s);

fun showing_any () = List.exists showing ITEMS;

fun notshowing_any () = not (showing_any ());

fun show "all" = show_set true
  | show s = case show_ref s of r => r := true;

fun hide "all" = show_set false
  | hide s = case show_ref s of r => r := false;

(* ------------------------------------------------------------------------- *)
(* Process command line arguments and environment variables.                 *)
(* ------------------------------------------------------------------------- *)
(* Default values - these are not refs *)
val max_splits_r = ~1
val atom_weight_r = 0;
val maxStackDepth =  100;
val SOSweightFactor = 2.0;

(* selects what type of case splitting to do *)
val backTracking = ref true
val caseSplitting = ref true
(* if cases parameters have been actively set then this will *)
(* over-ride the defaults set above.                         *)
val casesParam1Set = ref false
val casesParam1 = ref 0
val casesParam2Set = ref false
val casesParam2 = ref 0

(* Functions to check environment variables Z3_NONLIN, qe etc. *)
(* NB the checks are crude just to pick up the error of        *)
(* making Z3_NONLIN a directory etc                            *)

fun envVarErr msg = (print msg; raise Error "environment variable");

fun getEnv varname msg =
  case OS.Process.getEnv varname of
      NONE => envVarErr ("Environment variable " ^ varname ^ " is not set.  " ^ msg ^ "\n")
    | SOME s => s;

fun checkExec s varname =
  if OS.FileSys.access (s,[OS.FileSys.A_EXEC]) then ()
  else envVarErr ("No executable access to the File " ^ s ^ ", designated by " ^ varname ^ ".\n")
    handle OS.SysErr (msg,SOME e) =>
      envVarErr ("\nEncountered a SysErr when checking " ^ varname ^ "\n"^
                               "Exception : " ^ OS.errorName e ^ " " ^ OS.errorMsg e ^ "\n" );

(* Check environment variable for Z3 *)
fun check_Z3_NONLIN () =
  let val s = getEnv "Z3_NONLIN" "It should point to the Z3 executable."
  in  if OS.FileSys.isDir s handle _ => false
      then envVarErr ("\nZ3_NONLIN = "^ s ^" must point to a binary file, NOT a directory.\n")
      else checkExec s "Z3_NONLIN"
  end;

(* Check environment variable for Mathematica Kernel *)
fun check_MATH_KERNEL () =
  let val s = getEnv "MATH_KERNEL" "It should point to the Mathematica Kernel executable."
  in  if OS.FileSys.isDir s handle _ => false
      then envVarErr ("\nMATH_KERNEL = "^ s ^" must point to a binary file, NOT a directory.\n")
      else checkExec s "MATH_KERNEL"
  end;

(* Check environment variable for Qepcad *)
fun check_qe () =
  let val s = getEnv "qe" ""
  in  if (OS.FileSys.isDir s handle _ => false) then checkExec (s^"/bin/qepcad") "qe"
      else envVarErr ("Environment variable qe = " ^ s ^ " must point to a directory.\n")
  end;

fun check_appropriate_environment_variables () =
    case RCF.read_eadm () of
        RCF.QEPCAD => check_qe ()
      | RCF.MATHEMATICA => check_MATH_KERNEL ()
      | RCF.SMT_Z3 => check_Z3_NONLIN ();

fun check_RCF_version_numbers () =
    (* at present this only applies to Z3 *)
    case RCF.read_eadm () of
        RCF.SMT_Z3 => SMT.determine_Z3_version ()
      | _ => ();

fun extend_algebraic_ops (allow_nesting) =
    case RCF.read_eadm () of
         RCF.MATHEMATICA => (Poly.allow_special_functions := true;Poly.allow_nested_special_functions := allow_nesting)
     |   RCF.QEPCAD => raise Error "RCF Special functions cannot be used with QEPCAD, use Mathematica."
     |   RCF.SMT_Z3 => raise Error "RCF Special functions cannot be used with Z3, use Mathematica.";



fun parse_cases_params s =
  if s = "off" then
     let
         val _ = caseSplitting := false
     in
         (0,10)
     end
  else
     case map Int.fromString (String.tokens (fn c => c = #"+") s) of
       [SOME ms]          => let val _ = casesParam1Set := true in (ms, 0) end
     | [SOME ms, SOME aw] => let val _ = casesParam1Set := true val _ = casesParam2Set := true in (ms, aw) end
     | _ => die "case split parameters have the form INT+INT, INT, or \"off\""

fun set_cases_params s =
  let
     val (ms, aw) = parse_cases_params s
  in  casesParam1 := ms; casesParam2 := aw  end;

local
  open Useful Options;
in
  val specialOptions =
    [{switches = ["--show"], arguments = ["ITEM"],
      description = "show ITEM (see below for list)",
      processor =
        beginOpt (enumOpt extended_items endOpt) (fn _ => fn s => show s)},

     {switches = ["--writeSMTLIB"], arguments = [],
      description = "write an SMTLIB version of TPTP file",
      processor = beginOpt endOpt (fn _ => (writeSMTLIBfile := true))},

     {switches = ["--writeRCFproblems"], arguments = [],
      description = "write SMTLIB files for each RCF problem sent to Z3",
      processor = beginOpt endOpt (fn _ => (SMT.Z3_write_rcf_problems_to_file := true))},


     {switches = ["--autoInclude"], arguments = [],
      description = "Automatically select axiom files to include",
      processor = beginOpt endOpt (fn _ => (autoInclude := true; extended := false; superExtended := false))},

     {switches = ["--autoIncludeExtended"], arguments = [],
      description = "auto includes extended axioms",
      processor = beginOpt endOpt (fn _ => (autoInclude := true; extended := true; superExtended := false))},

     {switches = ["--autoIncludeSuperExtended"], arguments = [],
      description = "auto includes super extended axioms",
      processor = beginOpt endOpt (fn _ => (autoInclude := true;extended := false; superExtended := true))},

     {switches = ["--optProof"], arguments = [],
      description = "Optimise proof by rerunning decisions",
      processor = beginOpt endOpt (fn _ => (SplitStack.breadthFirstProof := true; SplitStack.replayProofDecisions := true))},


      (* allow Mathematica to work with special functions in "algebraic" clauses *)
      {switches = ["--allowSF_in_GC"], arguments = [],
      description = "Allow special functions in algebraic literals in the Given Clause only (Mathematica only)",
      processor = beginOpt endOpt (fn _ => (RCF.set_eadm(RCF.MATHEMATICA);RCF.use_exact_pi := true;
                                            Resolution.allow_sf_in_algebraic_clauses := false;
                                            RCF.proj_order := false;extend_algebraic_ops (true)))},

     {switches = ["--allowUSF_in_GC"], arguments = [],
      description = "Allow only un-nested special functions in algebraic literals in the Given Clause only (Mathematica only)",
      processor = beginOpt endOpt (fn _ => (RCF.set_eadm(RCF.MATHEMATICA);RCF.use_exact_pi := true;
                                            Resolution.allow_sf_in_algebraic_clauses := false;
                                            RCF.proj_order := false;extend_algebraic_ops (false)))},

      {switches = ["--allowSF"], arguments = [],
      description = "Allow special functions in algebraic literals as well as the Given Clause (Mathematica only)",
      processor = beginOpt endOpt (fn _ => (RCF.set_eadm(RCF.MATHEMATICA);RCF.use_exact_pi := true;
                                            Resolution.allow_sf_in_algebraic_clauses := true;
                                            RCF.proj_order := false;extend_algebraic_ops (true)))},

      {switches = ["--allowUSF"], arguments = [],
      description = "Allow un-nested special functions in algebraic literals as well as the Given Clause (Mathematica only)",
      processor = beginOpt endOpt (fn _ => (RCF.set_eadm(RCF.MATHEMATICA);RCF.use_exact_pi := true;
                                            Resolution.allow_sf_in_algebraic_clauses := true;
                                            RCF.proj_order := false;extend_algebraic_ops (false)))},




     {switches = ["--hide"], arguments = ["ITEM"],
      description = "hide ITEM (see below for list)",
      processor =
        beginOpt (enumOpt extended_items endOpt) (fn _ => fn s => hide s)},
     {switches = ["-p"], arguments = [],
      description = "show proof",
      processor = beginOpt endOpt (fn _ => show "proof")},
     {switches = ["--time"], arguments = ["positive real number"],
      description = "processor time limit (in seconds)",
      processor = realOpt (SOME 0.0, NONE) endOpt (fn k => cpu_limit := Real.toInt IEEEReal.TO_NEAREST (1000.0*k))},

     {switches = ["--RCFtime"], arguments = ["positive integer"],
      description = "RCF decision time limit (in milliseconds) (Mathematica and Z3 only)",
      processor = intOpt (SOME 0, NONE) endOpt (fn k => (Mathematica.mk_decision_time_limit :=
               (Time.fromMilliseconds (IntInf.fromInt k)); SMT.RCF_time_limit := k))},

     {switches = ["--maxweight","-w"], arguments = ["positive integer"],
      description = "maximum weight of a retained clause",
      processor = intOpt (SOME 0, NONE) endOpt Waiting.set_maxweight},
     {switches = ["--maxalg"], arguments = ["positive integer"],
      description = "maximum number of symbols in an algebraic clause",
      processor = intOpt (SOME 0, NONE) endOpt Resolution.set_maxalg},
(* ------------------------------------------------------------------------ *)
(* maximum run of nonSOS clauses allowed before giving up ...               *)
     {switches = ["--maxnonSOS"], arguments = ["positive integer"],
      description = "maximum run of non SOS given clauses allowed before giving up",
      processor = intOpt (SOME 0, NONE) endOpt Resolution.setMaxRunOutsideSOS},
(* ------------------------------------------------------------------------ *)
(*  Turns on re-running with high value of maxalg if waiting becomes empty  *)
     {switches = ["--rerun"], arguments = ["off/ON"],
      description = "before giving up, rerun with high maxalg (default is on)",
      processor = beginOpt (enumOpt ["off","on"] endOpt)
                    (fn _ => fn s => Resolution.rerunWithHighMaxAlg (s="on") )},
(* ------------------------------------------------------------------------ *)
     {switches = ["--tptp"], arguments = ["DIR"],
      description = "specify the TPTP installation directory",
      processor =
        beginOpt (stringOpt endOpt) (fn _ => fn s => TPTP := SOME s)},
     {switches = ["--tstp"], arguments = [],
      description = "generate standard TSTP: no infixes, etc.",
      processor = beginOpt endOpt (fn _ => Tptp.standardTSTP := true)},
(* ------------------- Paramodulation --------------------- *)
     {switches = ["--paramodulation"], arguments = ["off/ON"],
      description = "turn full paramodulation off (default is on)",
      processor =
        beginOpt (enumOpt ["off","on"] endOpt) (fn _ => fn s => Clause.useParamodulation := (s="on"))},
(* -------------------------------------------------------- *)
     {switches = ["--cases"], arguments = ["#cases+weight"],
      description = "max permitted active case splits/nonSOS weighting factor in tenths (10 = neutral weighting)",
      processor =
        beginOpt (stringOpt endOpt) (fn _ => fn s => set_cases_params s)},
(* ---------------- This is case splitting with backtracking -------------- *)
     {switches = ["--backtracking"], arguments = ["off/ON"],
      description = "turn backtracking off (default is on)",
      processor =
        beginOpt (enumOpt ["off","on"] endOpt) (fn _ => fn s => backTracking := (s="on"))},

(* ----- This enables only internal certifying RCF procedures ----- *)
     {switches = ["--univ_cert_rcf"], arguments = [],
      description = "enable only certifying RCF procedures (univariate only)",
      processor = beginOpt endOpt (fn _  => RCF.cert_rcf_only := true)},

(* ----- This enables only Mathematica-based root isolation ----- *)
     {switches = ["--univ_m_root_iso"], arguments = [],
      description = "Use Mathematica to isolate roots (univariate only)",
      processor = beginOpt endOpt (fn _  => RCF.m_root_iso_only := true)},

(* --------------- This enables projection ordering for CAD --------------- *)
     {switches = ["--proj_ord"], arguments = ["off/ON"],
      description = "switch CAD projection ordering off (default is on)",
      processor = beginOpt (enumOpt ["off","on"] endOpt)
                    (fn _ => fn s => RCF.set_proj_order (s="on"))},
(* ----- This enables polynomial ICP and Nullstellensatz search before EADM ----- *)
     {switches = ["--nsatz_eadm"], arguments = [],
      description = "enable polynomial Nullstellensatz search before EADM",
      processor = beginOpt endOpt (fn _  => RCF.set_adm_coop_method(RCF.ICP_THEN_EADM))},
(* -------------- This enables only polynomial ICP, no EADM ------------- *)
     {switches = ["--icp"], arguments = [],
      description = "enable only polynomial ICP, no EADM",
      processor = beginOpt endOpt (fn _  => RCF.set_adm_coop_method(RCF.ICP_ONLY))},
(* ------- This enables Mathematica as the EADM -------- *)
     {switches = ["-m", "--mathematica"], arguments = [],
      description = "use Mathematica as EADM",
      processor = beginOpt endOpt (fn _  => RCF.set_eadm(RCF.MATHEMATICA))},
(* ------- This enables SMT solver (Z3_nonlin) as the EADM -------- *)
     {switches = ["--z3"], arguments = [],
      description = "use SMT solver Z3 (version>=4.0) as EADM, no model-sharing",
      processor = beginOpt endOpt (fn _  => RCF.set_eadm(RCF.SMT_Z3))},
(* ------- This enables QepcadB as the EADM -------- *)
     {switches = ["--qepcad"], arguments = [],
      description = "use QepcadB as the EADM",
      processor = beginOpt endOpt (fn _  => RCF.set_eadm(RCF.QEPCAD))},
(* -------------- This enables ICP-based SAT search for RCF formulas------- *)
     {switches = ["--icp_sat"], arguments = [],
      description = "use ICP to search for RCF counter-example before refutation",
      processor = beginOpt endOpt (fn _  => RCF.check_icp_sat := true)},
(* ----- This enables univ. relaxation for SAT filtration on RCF formulas ----- *)
     {switches = ["--univ_sat"], arguments = [],
      description = "use univariate relaxations for RCF SAT checks (EADM only)",
      processor = beginOpt endOpt (fn _  => RCF.check_univ_rcf_sat := true)},
(* ----- Set RCF strategy ID ----- *)
     {switches = ["--strategy"], arguments = ["positive integer"],
      description = "ID of RCF strategy (default is 1: Z3(no_univ_factor) + model-sharing)",
      processor = intOpt (SOME 0, NONE) endOpt (fn k => RCF.set_strategy_id k)},
     {switches = ["--unsafe_divisors"], arguments = [],
      description = "don't verify that divisors are nonzero",
      processor = beginOpt endOpt (fn _ => Poly.unsafe_divisors := true)},
     {switches = ["--full"], arguments = [],
      description = "include variable instantiations in proofs",
      processor = beginOpt endOpt (fn _ => Tptp.fullProofs := true)},
     {switches = ["-q","--quiet"], arguments = [],
      description = "Run quietly; indicate provability with return value",
      processor = beginOpt endOpt (fn _ => (traceLevel := 0; QUIET := true))},
     {switches = ["--test"], arguments = [],
      description = "Skip the proof search for the input problems",
      processor = beginOpt endOpt (fn _ => TEST := true)} ];
end;

(*LCP:  version numbering and date stamp*)
val dateString = Date.fmt "%d %b %Y" (Date.fromTimeLocal (Time.now()));

val versionString = "MetiTarski 2.5 (built "^ dateString ^")"^"\n";

val programOptions =
    {name = PROGRAM,
     version = versionString,
     header = "usage: "^PROGRAM^" [option ...] problem.tptp ...\n" ^
              "Proves the input TPTP problem files.\n",
     footer = "Possible ITEMs are {" ^ join "," extended_items ^ "}.\n" ^
              "Problems can be read from standard input using the " ^
              "special - filename.\n",
     options = specialOptions @ Options.basicOptions};

fun exit x : unit = Options.exit programOptions x;
fun succeed () = Options.succeed programOptions;
fun fail mesg = Options.fail programOptions mesg;
fun usage mesg = Options.usage programOptions mesg;

fun processOptions () =
    let
      val args = CommandLine.arguments ()

      val (_,work) = Options.processOptions programOptions args

      val () =
          case !TPTP of
            SOME _ => ()
          | NONE => TPTP := OS.Process.getEnv "TPTP"
    in
      work
    end;

(* ------------------------------------------------------------------------- *)
(* Top level. LCP:  reporting runtime and killing child processes            *)
(* ------------------------------------------------------------------------- *)

exception Timeout;

(*The QEPCAD process must be closed prior to calling this function,
  otherwise its runtime will appear to be zero.*)
fun runtime_msg () =
  let val {utime,cutime, ...} = Posix.ProcEnv.times()
      val rcf_time = if Time.>(!RCF.extra_cpu_time, Time.zeroTime) then
                         case !RCF.strategy_id of
                             NONE => !RCF.extra_cpu_time (* Mathematica time *)
                           | _ => cutime (* Everything except Mathematica *)
                     else cutime
      val tot_utime = Time.+(utime, rcf_time)
  in  "Processor time: " ^
      Time.toString tot_utime ^ " = " ^
      Time.toString utime ^ " (Metis) + " ^ (Time.toString rcf_time) ^ " (RCF)\n"
  end;

(*Prevents the printing of multiple exit messages, caused by exceptions raised
  by the killing of the subprocess. Oddly, exception handlers don't catch these.*)
val exitr = ref false;

(*Close, print runtime, quit.*)
fun fail_cleanly msg =
 (if !exitr orelse !QUIET then () else (exitr := true; TextIO.closeOut TextIO.stdErr; print msg);
  RCF.kill_in_progress := true;
  RCF.close_with_time true;
  if !QUIET then () else print (runtime_msg());
  OS.Process.exit OS.Process.failure);

fun string_of_exn (OS.SysErr (msg,_)) = "Operating System error: " ^ msg
  | string_of_exn e = exnMessage e;

(* ------------------------------------------------------------------------- *)
(* The core application.                                                     *)
(* ------------------------------------------------------------------------- *)

(*MetisDebug
val next_cnf =
    let
      val cnf_counter = ref 0
    in
      fn () =>
         let
           val ref cnf_count = cnf_counter
           val () = cnf_counter := cnf_count + 1
         in
           cnf_count
         end
    end;
*)

local
  fun display_sep () =
      if notshowing_any () then ()
      else print (nChars #"-" (!Print.lineLength) ^ "\n");

  fun display_name filename =
      if notshowing "name" then ()
      else print ("Problem: " ^ filename ^ "\n\n");

  fun display_goal tptp =
      if notshowing "goal" then ()
      else
        let
          val goal = Tptp.goal tptp
        in
          print ("Goal:\n" ^ Formula.toString goal ^ "\n\n")
        end;

  fun display_clauses cls =
      if notshowing "clauses" then ()
      else print ("Clauses:\n" ^ Problem.toString cls ^ "\n\n");

  fun display_size cls =
      if notshowing "size" then ()
      else
        let
          fun plural 1 s = "1 " ^ s
            | plural n s = Int.toString n ^ " " ^ s ^ "s"

          val {clauses,literals,symbols,typedSymbols} = Problem.size cls
        in
          print
            ("Size: " ^
             plural clauses "clause" ^ ", " ^
             plural literals "literal" ^ ", " ^
             plural symbols "symbol" ^ ", " ^
             plural typedSymbols "typed symbol" ^ ".\n\n")
        end;

  fun display_category cls =
      if notshowing "category" then ()
      else
        let
          val cat = Problem.categorize cls
        in
          print ("Category: " ^ Problem.categoryToString cat ^ ".\n\n")
        end;

  local
    fun display_proof_start filename =
        print ("\nSZS output start CNFRefutation for " ^ filename ^ "\n");

    fun display_proof_body problem proofs =
        let
          val comments = []

          val includes = []

          val formulas =
              Tptp.fromProof
                {problem = problem,
                 proofs = proofs}

          val proof =
              Tptp.Problem
                {comments = comments,
                 includes = includes,
                 formulas = formulas}

          val mapping = Tptp.defaultMapping
          val mapping = Tptp.addVarSetMapping mapping (Tptp.freeVars proof)

          val filename = "-"
        in
          Tptp.write
            {problem = proof,
             mapping = mapping,
             filename = filename}
        end;

    fun display_proof_end filename =
        print ("SZS output end CNFRefutation for " ^ filename ^ "\n\n");
  in
    fun display_proof filename problem proofs =
        if notshowing "proof" then ()
        else
          let
            val () = display_proof_start filename
            val () = display_proof_body problem proofs
            val () = display_proof_end filename
          in
            ()
          end;
  end;

  fun display_saturation filename ths =
      if notshowing "saturation" then ()
      else
        let
(*MetisDebug
          val () =
              let
                val problem =
                    Tptp.mkProblem
                      {comments = ["Saturation clause set for " ^ filename],
                       includes = [],
                       names = Tptp.noClauseNames,
                       roles = Tptp.noClauseRoles,
                       problem = {axioms = [],
                                  conjecture = map Thm.clause ths}}

                val mapping =
                    Tptp.addVarSetMapping Tptp.defaultMapping
                      (Tptp.freeVars problem)
              in
                Tptp.write
                  {problem = problem,
                   mapping = mapping,
                   filename = "saturation.tptp"}
              end
*)
          val () = print ("\nSZS output start Saturation for " ^ filename ^ "\n")
          val () = app (fn th => print (Thm.toString th ^ "\n")) ths
          val () = print ("SZS output end Saturation for " ^ filename ^ "\n\n")
        in
          ()
        end;

  fun display_status filename status =
      if notshowing "status" orelse !exitr orelse !QUIET then ()
      else print ("SZS status " ^ Tptp.toStringStatus status ^
                  " for " ^ filename ^ "\n");

  fun display_problem filename cls =
      let
(*MetisDebug
        val () =
            let
              val problem =
                  Tptp.mkProblem
                    {comments = ["CNF clauses for " ^ filename],
                     includes = [],
                     names = Tptp.noClauseNames,
                     roles = Tptp.noClauseRoles,
                     problem = cls}

              val mapping =
                  Tptp.addVarSetMapping Tptp.defaultMapping
                    (Tptp.freeVars problem)

              val filename = "cnf_" ^ Int.toString (next_cnf ()) ^ ".tptp"
            in
              Tptp.write
                {problem = problem,
                 mapping = mapping,
                 filename = filename}
            end
*)
        val () = display_clauses cls
        val () = display_size cls
        val () = display_category cls
      in
        ()
      end;

  fun mkTptpFilename filename =
    let val filename = stripSuffix (equal #" ") (stripPrefix (equal #" ") filename)
    in
      case !TPTP of
        NONE => filename
      | SOME tptp =>
          if String.isPrefix "/" filename then filename (*Absolute path name*)
          else
            let val tptp = stripSuffix (equal #"/") tptp
            in
              tptp ^ "/" ^ filename
            end
    end;

  fun readIncludes mapping seen formulas includes =
      case includes of
        [] => formulas
      | inc :: includes =>
        if StringSet.member inc seen then
          readIncludes mapping seen formulas includes
        else
          let
            val seen = StringSet.add seen inc

            val filename = mkTptpFilename inc

            val Tptp.Problem {includes = i, formulas = f, ...} =
                MT_Tptp.read {filename = filename, mapping = mapping}

            val formulas = f @ formulas

            val includes = List.revAppend (i,includes)
          in
            readIncludes mapping seen formulas includes
          end;

(* -------------------------------------------------------------------- *)
(* Utility functions for code to automatically determine axiom includes *)
(* -------------------------------------------------------------------- *)

  fun writeOutIncludes [] = print "----------------------------\n"
    | writeOutIncludes (inc::includes) =
          let
             val _ = print(inc ^ "\n")
          in
             writeOutIncludes includes
          end;

  fun getThmList' [] acc = acc
    | getThmList' ({problem={axioms,conjecture},...}::rest) acc =
           let
               val axioms = map Thm.axiom axioms
               val conjecture = map Thm.conjecture conjecture
               val acc = acc @ axioms
               val acc = acc @ conjecture
           in
               getThmList' rest acc
           end

   fun getThmList probs = getThmList' probs []

  fun printThmList' [] output = print (output ^ "\n")
    | printThmList' (th::ths) output =
           let
               val output  = output ^ Print.toString Thm.pp th ^ "\n"
           in
               printThmList' ths output
           end;
  fun printThmList thmList = printThmList' thmList "\nConjecture Clause List\n";

  fun getFunctionSet [] fx = fx
    | getFunctionSet (th::ths) fx =
           let
                fun addLits [] fx = fx
                 |  addLits (lit::lits) fx =
                       let
                            fun onlyArity1plus nameArity =
                                (NameArity.arity nameArity > 0) orelse
                                (NameArity.arity nameArity = 0 andalso
                                 NameArity.name nameArity= "pi")

                            val name_arity_set = Literal.functions lit
                            val name_arity_set = NameAritySet.filter onlyArity1plus name_arity_set
                            val fx = NameAritySet.union name_arity_set fx
                       in
                            addLits lits fx
                       end
                val literals = LiteralSet.toList (Thm.clause th)
                val fx = addLits literals fx
            in
                getFunctionSet ths fx
            end;
  fun getFunctionNames thmList =
        NameAritySet.toList (getFunctionSet thmList (NameAritySet.empty))

  fun printFunctionNames thmList =
      let
         fun printNameList [] output = print (output ^ "\n")
          |  printNameList (name::names) output =
               printNameList names (output ^ (NameArity.name name) ^ "\n")
          fun printAll names = printNameList names "List of function names\n"
          val nameList = getFunctionNames thmList
      in
          printAll nameList
      end;

(* Long and rather messy function to actually add the includes *)
   fun addIncludes fx =
       let
          (* check for the presence of functions sometimes requiring extended axioms *)
          fun memList l = List.exists (fn z => NameAritySet.member z fx) l;
          val _ = extendedFuncs := memList [("sqrt",1), ("arctan",1), ("cos",1),
                               ("exp",1), ("ln",1), ("log",1), ("pow",2), ("sin",1)]

          val _ = superExtendedFuncs := memList [("arctan",1), ("cos",1), ("sin",1)]
          val _ = linearLimitsFuncs := memList [("cos",1), ("sin",1)]
          val _ = constantLimitsFuncs := !linearLimitsFuncs
         (* only add the trans axioms if there are no special functions present  FIXME should refer to Poly/special_functions*)
          val add_trans = not (memList [("abs",1),("arccos",1), ("arcsin",1), ("arctan",1),("besselJ",2),
                 ("cbrt",1), ("cos",1), ("cosh",1), ("exp",1), ("floor",1), ("ln",1), ("log",1),("nthrt",2),
                 ("pow",2), ("sin",1), ("sinh",1), ("sqrt",1), ("tan",1), ("tanh",1)])
          val incs = if add_trans then ["Axioms/trans.ax"] else []
          val incs = incs @ ["Axioms/general.ax"]
          val incs = if (NameAritySet.member ("min",2) fx) orelse (NameAritySet.member ("max",2) fx)
                     then incs @ ["Axioms/minmax.ax"] else incs
          val incs = if (NameAritySet.member ("abs",1) fx) then
                     incs @ ["Axioms/abs.ax"]
                     else incs
          val incs = if (NameAritySet.member ("floor",1) fx) then
                     incs @ ["Axioms/floor.ax"]
                     else incs
          val incs = if (NameAritySet.member ("arccos",1) fx) then
                         if(!extended orelse !superExtended)then
                            incs @ ["Axioms/arccos.ax","Axioms/arcsin-lower.ax","Axioms/arcsin-upper.ax",
                                    "Axioms/pi.ax","Axioms/sqrt-extended.ax","Axioms/sqrt-general.ax"]
                         else
                            incs @ ["Axioms/arccos.ax","Axioms/arcsin-lower.ax","Axioms/arcsin-upper.ax",
                                  "Axioms/pi.ax","Axioms/sqrt-general.ax","Axioms/sqrt-lower.ax","Axioms/sqrt-upper.ax"]
                  else incs
          val incs = if (NameAritySet.member ("arcsin",1) fx) then
                          if(!extended orelse !superExtended)then
                            incs @ ["Axioms/arcsin-lower.ax","Axioms/arcsin-upper.ax",
                                    "Axioms/sqrt-extended.ax","Axioms/sqrt-general.ax"]
                         else
                            incs @ ["Axioms/arcsin-lower.ax","Axioms/arcsin-upper.ax",
                                 "Axioms/sqrt-general.ax","Axioms/sqrt-lower.ax","Axioms/sqrt-upper.ax"]
                  else incs
          val incs = if (NameAritySet.member ("arctan",1) fx) then
                         if !extended then
                             incs @["Axioms/arctan-extended.ax"]
                         else if (!superExtended) then
                             incs @["Axioms/arctan-extended2.ax"]
                         else
                             incs @["Axioms/arctan-lower.ax","Axioms/arctan-upper.ax"]
                  else incs
          val incs = if (NameAritySet.member ("cbrt",1) fx) then
                  incs @ ["Axioms/cbrt-lower.ax","Axioms/cbrt-upper.ax"]
                  else incs
          val incs = if (NameAritySet.member ("cos",1) fx) then
                        if !extended then
                            incs @ ["Axioms/cos-extended.ax"]
                        else if !superExtended then
                            incs @ ["Axioms/cos-extended2.ax"]
                        else if !linearLimits then
                            incs @ ["Axioms/cos-linear.ax","Axioms/cos.ax"]
                        else if !constantLimits then
                            incs @ ["Axioms/cos-constant.ax","Axioms/cos.ax"]
                        else
                            incs @ ["Axioms/cos.ax"]
                   else incs
          val incs = if (NameAritySet.member ("cosh",1) fx) then
                     incs @ ["Axioms/cosh-lower.ax","Axioms/cosh-upper.ax"]
                     else incs
          val incs = if (NameAritySet.member ("exp",1) fx) then
                         if !extended orelse !superExtended then
                              incs @ ["Axioms/exp-lower.ax","Axioms/exp-extended.ax",
                                      "Axioms/exp-general.ax"]
                         else
                             incs @ ["Axioms/exp-general.ax","Axioms/exp-lower.ax",
                                     "Axioms/exp-upper.ax"]
                   else incs
          val incs = if (NameAritySet.member ("ln",1) fx) then
                         if !extended orelse !superExtended then
                             incs @ ["Axioms/ln-lower.ax","Axioms/ln-extended.ax",
                                     "Axioms/ln-general.ax"]
                         else
                             incs @ ["Axioms/ln-general.ax","Axioms/ln-lower.ax",
                                     "Axioms/ln-upper.ax"]
                   else incs
          val incs = if (NameAritySet.member ("log",1) fx) then
                         if !extended orelse !superExtended then
                             incs @ ["Axioms/log.ax","Axioms/ln-lower.ax",
                                     "Axioms/ln-extended.ax","Axioms/ln-general.ax"]
                         else
                             incs @ ["Axioms/log.ax","Axioms/ln-general.ax",
                                     "Axioms/ln-lower.ax","Axioms/ln-upper.ax"]
                   else incs
          val incs = if (NameAritySet.member ("pi",0) fx) then incs @ ["Axioms/pi.ax"]
                     else incs
          val incs = if (NameAritySet.member ("pow",2) fx) then
                         if(!extended orelse !superExtended)then
                             incs @ ["Axioms/pow.ax","Axioms/ln-lower.ax",
                                     "Axioms/ln-extended.ax","Axioms/ln-general.ax",
                                     "Axioms/exp-lower.ax","Axioms/exp-extended.ax"]
                         else
                             incs @ ["Axioms/pow.ax","Axioms/ln-general.ax",
                                     "Axioms/ln-lower.ax","Axioms/ln-upper.ax",
                                     "Axioms/exp-lower.ax","Axioms/exp-upper.ax"]
                   else incs
          val incs = if (NameAritySet.member ("sin",1) fx) then
                         if !extended then
                               incs @ ["Axioms/sin-extended.ax"]
                         else if !superExtended then
                               incs @ ["Axioms/sin-extended2.ax"]
                         else if !linearLimits then
                               incs @ ["Axioms/sin-linear.ax","Axioms/sin.ax"]
                         else if !constantLimits then
                               incs @ ["Axioms/sin-constant.ax","Axioms/sin.ax"]
                         else
                               incs @ ["Axioms/sin.ax"]
                   else incs
          val incs = if (NameAritySet.member ("sinh",1) fx) then
                   incs @
                       ["Axioms/sinh-lower.ax","Axioms/sinh-upper.ax"]
                   else incs
          val incs = if (NameAritySet.member ("sqrt",1) fx) then
                         if(!extended orelse !superExtended)then
                            incs @ ["Axioms/sqrt-extended.ax","Axioms/sqrt-general.ax"]
                         else
                            incs @ ["Axioms/sqrt-general.ax","Axioms/sqrt-lower.ax","Axioms/sqrt-upper.ax"]
                   else incs
          val incs = if (NameAritySet.member ("tan",1) fx) then
                   incs @
                       ["Axioms/tan-lower.ax","Axioms/tan-upper.ax",
                        "Axioms/tan.ax"]
                   else incs
          val incs = if (NameAritySet.member ("tanh",1) fx) then
                   incs @
                       ["Axioms/tanh-lower.ax","Axioms/tanh-upper.ax"]
                   else incs
          val incs = if (NameAritySet.member ("besselJ",2) fx) then
                   incs @
                       ["Axioms/Bessel.ax"]
                   else incs
          val incs = if (NameAritySet.member ("nthrt",2) fx) then
                   incs @
                       ["Axioms/nthrt-lower.ax","Axioms/nthrt-upper.ax"]
                   else incs
       in
          incs
       end;

(* functions to determine if any user includes are "missing" i.e. find which *)
(* special functions are covered by the user includes and issue a warning if *)
(* there are functions present which are not covered.                        *)
(* NB this could be made more sophisticated by checking the axioms and conjecture *)
(* functions separately to ensure all functions in the conjecture are covered by  *)
(* an axiom. The routine below simply checks the names of the include files.      *)

(* check for the presence of function names in the includes  *)
(* NB it is important to check for acos before cos and so on *)
(* 2nd May 2013 the include files asin, acos and atan are changed to *)
(* arcsin, arccos and arctan to match the functions that they contain *)
(* 22nd October 2013 changed to return a list of functions as *)
(* minmax.ax has two different functions in one axiom file    *)
fun includeToFn inc =
    if(String.isSubstring "pi" inc)then SOME [("pi",0)] else
    if(String.isSubstring "abs" inc)then SOME [("abs",1)] else
    if(String.isSubstring "floor" inc)then SOME [("floor",1)] else
    if(String.isSubstring "arccos" inc)then SOME [("arccos",1)] else
    if(String.isSubstring "arcsin" inc)then SOME [("arcsin",1)] else
    if(String.isSubstring "arctan" inc)then SOME [("arctan",1)] else
    if(String.isSubstring "cosh" inc)then SOME [("cosh",1)] else
    if(String.isSubstring "sinh" inc)then SOME [("sinh",1)] else
    if(String.isSubstring "tanh" inc)then SOME [("tanh",1)] else
    if(String.isSubstring "cos" inc)then SOME [("cos",1)] else
    if(String.isSubstring "sin" inc)then SOME [("sin",1)] else
    if(String.isSubstring "tan" inc)then SOME [("tan",1)] else
    if(String.isSubstring "cbrt" inc)then SOME [("cbrt",1)] else
    if(String.isSubstring "exp" inc)then SOME [("exp",1)] else
    if(String.isSubstring "ln" inc)then SOME [("ln",1)] else
    if(String.isSubstring "log" inc)then SOME [("log",1)] else
    if(String.isSubstring "pow" inc)then SOME [("pow",2)] else
    if(String.isSubstring "sqrt" inc)then SOME [("sqrt",1)] else
    if(String.isSubstring "minmax" inc)then SOME [("min",2),("max",2)] else
    if(String.isSubstring "Bessel" inc) then SOME [("besselJ",2)] else
    if(String.isSubstring "nthrt" inc) then SOME [("nthrt",2)] else
    ((*print ("No function found in inc : " ^ inc ^ "\n");*)NONE);

fun coveredFunctions [] cfx general = (cfx,general)
 |  coveredFunctions (inc::includes) cfx general =
    let
        val fn_list_option = includeToFn inc
        val general = if general then general else String.isSubstring "general" inc
        val cfx = case fn_list_option of SOME f => (NameAritySet.addList cfx f)
                                 |  NONE => cfx
    in
        coveredFunctions includes cfx general
    end;

fun getCoveredFunctions includes = coveredFunctions includes (NameAritySet.empty) false

(* This function is long-winded to allow for the fact that  *)
(* some functions are expressed in terms of others so axiom *)
(* files are required for dependent functions as well as    *)
(* explicitly included ones.                                *)
fun warnOnMissingIncludes fx includes filename =
    let
        val (cfx,general) = getCoveredFunctions includes
        val _ = if general then () else warn ("Axioms/general.ax not included in file "^filename^"; ")
        fun warn_on_main_function (f,flist) =
                      if (NameAritySet.member f fx) andalso
                         not (NameAritySet.member f cfx)
                      then ((NameArity.name f)::flist)
                      else flist
        fun warn_on_dependent_function ((fparent, fd),dflist) =
              if NameAritySet.member fparent fx andalso not (NameAritySet.member fd cfx)
              then (((NameArity.name fd)^ " needed by " ^ NameArity.name fparent)::dflist)
              else dflist
        val main_list = [("abs",1),("arccos",1),("arcsin",1),("arctan",1),
                         ("cosh",1),("floor",1),("sinh",1),("tanh",1),("cos",1),("sin",1),
                         ("tan",1),("cbrt",1),("exp",1),("ln",1),("log",1),
                         ("pow",2),("sqrt",1),("pi",0),("min",2),("max",2),("besselJ",2),("nthrt",2)]
        val dependent_list = [(("arccos",1),("arcsin",1)),
                              (("arccos",1),("pi",0)),
                              (("arccos",1),("sqrt",1)),
                              (("arcsin",1),("sqrt",1)),
                              (("log",1),("ln",1)),
                              (("pow",2),("ln",1)),
                              (("pow",2),("exp",1))]
        val flist = foldl warn_on_main_function [] main_list
        val flist = foldl warn_on_dependent_function flist dependent_list
        fun flist_to_string [] s = s^" in file "^filename^"."
         |  flist_to_string (f::fs) "" =  flist_to_string fs f
         |  flist_to_string (f::fs) s = flist_to_string fs (s ^ "," ^ f)
    in
       if null flist then ()
       else warn("no include files found for : "^(flist_to_string flist ""))
    end;

(* function to warn about function names that are not recognized *)
(* to try and catch such cases as using atan instead of arctan  FIXME should use the list in Poly/special_functions *)
val known_list = [("abs",1),("arccos",1),("arcsin",1),("arctan",1),
                         ("cosh",1),("floor",1),("sinh",1),("tanh",1),("cos",1),("sin",1),
                         ("tan",1),("cbrt",1),("exp",1),("ln",1),("log",1),
                         ("pow",2),("sqrt",1),("pi",0),("+",2),("-",2),("-",1),
                         ("*",2),("^",2),("/",2),("min",2),("max",2),("besselJ",2),("nthrt",2)];
val known_functions = NameAritySet.fromList known_list;

fun warn_on_functions fx filename =
    let
       val all_functions = NameAritySet.union fx known_functions
       val unknown_functions = NameAritySet.difference all_functions known_functions
       (* filter out any Skolem functions [beginning with sko] *)
       fun non_sko (name,_) = not (String.isPrefix "sko" name)
       val unknown_list = List.filter non_sko (NameAritySet.toList unknown_functions)
    in
       if null unknown_list then ()
       else warn ("Unrecognized Special Functions: " ^
                   String.concatWith ", " (map #1 unknown_list) ^ " in file "^filename)
    end;


(* ------------------------------------------- *)
(* End of utility functions for axiom includes *)
(* ------------------------------------------- *)


fun read mapping filename =
    let
        (* Temporary debug code to test SMTLIB *)
        (*
        val _ = SMTLIB.testTokenReading filename ("Tokens_from_"^filename)
        val _ = SMTLIB.testSExpressions filename ("S_Expressions_from_"^filename)
        val _ = SMTLIB.testInterpreter filename ("Interpreted_Commands_from_"^filename)
        val _ = raise Error "SMTLIB Debug exit"
        *)
        (* End of temporary debug code         *)
        fun getExtension (#"."::name) ext = ((implode ext),(implode (rev name)))
         |  getExtension [] ext = ("",(implode ext)) (* in this case the "ext" is the main file name *)
         |  getExtension (c::cs) ext = getExtension cs (c::ext)
        val (ext,fname) = getExtension (rev(explode filename)) []


        val problem = case ext of "smt2" => SMTLIB.read filename
                                | _ =>
                                  (* preprocess to remove comments and redundant brackets *)
                                  let
                                     val filename = SMTLIB.filter_tptp_file filename
                                     val problem = MT_Tptp.read {filename = filename, mapping = mapping}
                                     val _ = if KEEP_TEMP_FILE then
                                               print ("Temporary file name is : \n"^filename^"\n")
                                             else ()
                                     val _ = if KEEP_TEMP_FILE then () else OS.FileSys.remove filename
                                  in
                                     problem
                                  end


        val Tptp.Problem {comments,includes,formulas} = problem

        (* if the flag is set then produce an SMTLIB version of the tptp file *)
        val _ = if (!writeSMTLIBfile) andalso ext = "tptp" then
                let
                   val fname = fname^".smt2"
                   val exists =
                         let
                            val stream = TextIO.openIn fname
                            val _ = TextIO.closeIn stream
                         in
                            true
                         end
                         handle _ => false
                 in
                     if exists then () else SMTLIB.write fname problem
                end
                else ()
        (* ------------------------------------------------------------------ *)



        (* Debug (for SMTLIB testing) *)
        (*
        val Tptp.Formula {body,...} = hd formulas
        val Tptp.FofFormulaBody(formula) = body
        val _ = print("First formula : \n"^(Formula.toString formula)^"\n")
        *)
        (* End of debug *)

        (* ------------------------------------------------------------- *)
        (* code to generate includes automatically from the forumalas    *)
        (* ignore formulas in existing includes - doing this is a design *)
        (* decision - it means that automatic axiom selection can only   *)
        (* apply to conjectures in the main file.                        *)
        (* ------------------------------------------------------------- *)
        (* Set the auto include flag if there are no user includes *)
        (* val _ = if not (!autoInclude) then autoInclude := (List.null includes) else () *)

        val problemMinusIncludes = Tptp.Problem
                                       {comments = comments,
                                        includes = [],formulas = formulas}
        (* We grab the pre-CNF goal formula in case we want to give it
           directly to the CertRCF module. *)
        val preCNFGoal = Tptp.goal problemMinusIncludes
        (* -------------------------------------------------------------- *)
        (* Check for free variables and flag an error if they are present *)
        (* change made 22nd April 2013                                    *)
        (* -------------------------------------------------------------- *)
        val free_vars = Tptp.freeVarsFOFonly problemMinusIncludes
        val _ = if(NameSet.null free_vars) then ()
                else
                    let
                        (* NB in the following can't use NameSet.toString as it just prints the number *)
                        (* of free variables not their names.                                          *)
                        val free_var_list = rev(NameSet.toList free_vars)
                        fun f (vnames,vname) = vnames ^ "\n" ^ vname
                        val free_var_names = foldl f "" free_var_list
                    (* additional temporary code to write the file name to a list *)
                    (* use this in conjunction with runmetit.pl...
                      val log_file = TextIO.openAppend "Files_with_free_variables.txt"
                      val bat_file = TextIO.openAppend "Files_with_free_variables.bat"
                      val _ = TextIO.output (log_file,(filename ^ "\n"))
                      val _ = TextIO.output (bat_file,("cp $HOME/MetiTarski/metitarski/tptp/Problems/"^filename^"\n"))
                      val _ = TextIO.closeOut log_file
                      val _ = TextIO.closeOut bat_file
                      .... end of temporary code *)
                    in
                        raise Error ("Conjecture contains the following free variables :\n"^free_var_names^
                                     "Free variables are not allowed,\nplease explicitly quantify them.\n")
                    end
        (*----------------------------------------------------------------*)

        val probs = Tptp.normalize problemMinusIncludes
        val thmList = getThmList probs
        (* val _ = printThmList thmList
        val _ = printFunctionNames thmList *)
        val fx = getFunctionSet thmList (NameAritySet.empty)
        val generatedIncludes = addIncludes fx
        val _ = if !autoInclude then print("Generated Include List\n") else ()
        val _ = if !autoInclude then writeOutIncludes generatedIncludes else ()
        (* ------------------------------------------------------------------ *)
        (* if autoinclude is not set then check includes and warn if any seem *)
        (* to be missing.                                                     *)
        (* ------------------------------------------------------------------ *)
        val _ = if not (!autoInclude) then warnOnMissingIncludes fx includes filename else ()
        (* ---------------------------------------------------------------------- *)
        (* If autoInclude is set then add the generated includes to the existing  *)
        (* list of includes. This may lead to duplication but this doesn't matter *)
        (* as duplicates are removed in function readIncludes.                    *)
        (* ---------------------------------------------------------------------- *)
        val includes = if (!autoInclude) then (generatedIncludes @ includes) else includes
        (* ---------------------------------------------- *)
        (* end of code to automatically generate includes *)
        (* ---------------------------------------------- *)
        (* -------------------------------------------------------------------- *)
        (* Issue warnings for unknown functions to try and catch errors such as *)
        (* using atan instead of arctan.                                        *)
        (* -------------------------------------------------------------------- *)
        val _ = warn_on_functions fx filename
        (* -------------------------------------------------------------------- *)
    in
        if null includes then (problem, preCNFGoal)
        else
            let
                val seen = StringSet.empty

                val includes = rev includes

                (* val _ = writeOutIncludes includes *)

                val formulas = readIncludes mapping seen formulas includes
            in
                (Tptp.Problem
                     {comments = comments,
                      includes = [],
                      formulas = formulas},
                 preCNFGoal)
            end
    end;

  (*LCP: No resolutionParameters, no models....*)

  fun refute {axioms,conjecture} =
      let
        val axioms = map Thm.axiom axioms
        and conjecture = map Thm.conjecture conjecture
        val problem = {axioms = axioms, conjecture = conjecture}
        val resolution = Resolution.new Resolution.default problem
      in
        Resolution.loop resolution
      end;

  fun refuteAll filename tptp probs acc =
      case probs of
        [] =>
        let
          val status =
              if !TEST then Tptp.UnknownStatus
              else if Tptp.hasFofConjecture tptp then Tptp.TheoremStatus
              else Tptp.UnsatisfiableStatus

          val () = display_status filename status

          val () =
              if !TEST then ()
              else display_proof filename tptp (rev acc)
        in
          true
        end
      | prob :: probs =>
        let
          val {subgoal,problem,sources} = prob

          val () = display_problem filename problem
        in
          if !TEST then refuteAll filename tptp probs acc
          else
            case refute problem of
              Resolution.Contradiction th =>
              let
                val subgoalProof =
                    {subgoal = subgoal,
                     sources = sources,
                     refutation = th}

                val acc = subgoalProof :: acc
              in
                refuteAll filename tptp probs acc
              end
            | Resolution.Satisfiable ths =>
              let
                val status = Tptp.GaveUpStatus (*Incomplete, so cannot report "satisfiable"*)
                val () = display_status filename status
                val () = display_saturation filename ths
              in
                false
              end
        end;

  val filename_p = ref "???";
in
  fun prove mapping filename =
      let
        (*For the Poly/ML signal structure, not the SML/NJ one. It will run AS A SEPARATE THREAD*)
        fun sig_xcpu_handler _ =
              (display_status filename Tptp.TimeoutStatus;
               fail_cleanly "Processor time limit exceeded.\n");
        fun sig_int_handler _  = fail_cleanly "Interrupt signal received.\n";
        fun sig_alrm_handler _ = fail_cleanly "Alarm signal received.\n";
        val () = display_sep ()
        val () = display_name filename
        (* write the filename to Thm.sml to allow better error reporting *)
        val () = Thm.filename := filename
        (* set the RCF output file name core based on filename *)
        (* for the case where RCF files are to be written      *)
        val _ = SMT.core_file_name := (filename ^ "_RCF_problem_")
        val (tptp, preCNFGoal) = read mapping filename
        val () = display_goal tptp
        val problems = Tptp.normalize tptp
        val _ = Signal.signal (Common.sigxcpu, Signal.SIG_HANDLE sig_xcpu_handler);
        val _ = Signal.signal (Posix.Signal.int, Signal.SIG_HANDLE sig_int_handler);
        val _ = Signal.signal (Posix.Signal.alrm, Signal.SIG_HANDLE sig_alrm_handler);
        (* -------------------------------------------------------------- *)
        (* If autoInclude is set and the extended functions are present   *)
        (* then take an iterative deepening approach to w the max weight, *)
        (* provided the flag allowIterativeDeepening is set to true.      *)
        (* -------------------------------------------------------------- *)
        val iterate_on_w = !autoInclude andalso !extendedFuncs andalso !allowIterativeDeepening
        val max_w = !Waiting.maxweight
        val _ = if iterate_on_w then Waiting.maxweight := 600.0 else ()
        (* ------------------------------------------------------------------ *)
        (* output moved here to allow extra runs to be done, if need be, with *)
        (* extended includes - see below...                                   *)
        (* ------------------------------------------------------------------ *)
        val _ = filename_p := filename;
        (* ------------------------------------------------------------------ *)
        (* Check to see if goal is purely algebraic. Currently, we only use   *)
        (* this when --univ_cert_rcf (CertRCF) is enabled (cf. result_of_run).*)
        (* ------------------------------------------------------------------ *)
        fun is_purely_rcf g =
            let val g' = Tptp.Formula {name = Tptp.FormulaName "input goal",
                                       role = Tptp.ConjectureRole,
                                       source = Tptp.NoFormulaSource,
                                       body = Tptp.FofFormulaBody g}
                val all_lits = LiteralSet.all
                val alg_clause = all_lits (orf Literal.is_label (Poly.is_algebraic_literal false))
                val ps = Tptp.normalize (Tptp.Problem
                                             {comments = [],
                                              includes = [],
                                              formulas = [g']})
                val ps' = List.map (#problem) ps
                fun prob_is_rcf p = List.all alg_clause (Problem.toClauses p)
            in
                List.all prob_is_rcf ps'
            end
        val result_of_run =
            (* --------------------------------------------------------------- *)
            (* If user has selected CertRCF and goal is purely algebraic, then *)
            (* we use CertRCFp directly upon the goal, bypassing resolution.   *)
            (* --------------------------------------------------------------- *)
            if !(RCF.cert_rcf_only) andalso is_purely_rcf preCNFGoal
            then
                let val r = CertRCFp.univ_prove_q preCNFGoal
                    val status =
                        if !TEST then Tptp.UnknownStatus
                        else
                            if r then Tptp.TheoremStatus
                            else
                                if Formula.isForall preCNFGoal
                                then Tptp.CounterSatisfiableStatus
                                else
                                    if Formula.isExists preCNFGoal
                                    then Tptp.UnsatisfiableStatus
                                    else
                                        Tptp.UnknownStatus
                    val () = (print "\n"; display_status filename status)
                in r end
            else
                (* --------------------------------------------------------------- *)
                (* If user has selected M_Root_Iso and goal is purely algebraic, then *)
                (* we use CertRCFp directly upon the goal, bypassing resolution.   *)
                (* --------------------------------------------------------------- *)
                if !(RCF.m_root_iso_only) then
                    let val r = Mathematica.univ_m_root_iso preCNFGoal
                        (* After printing the roots, we always return Unknown status *)
                        val status = Tptp.UnknownStatus
                        val () = (print "\n"; display_status filename status)
                    in false end
                else
                    (* Else, we enter MetiTarski's main resolution loop *)
                    refuteAll filename tptp problems []
        (* -------------------------------------------------------------------------- *)
        (* If auto include is set - perhaps by the user or by there being no includes *)
        (* in the source file, and refuteAll has returned false to indicate it has    *)
        (* given up then try the extended include options...                          *)
        (* -------------------------------------------------------------------------- *)
        val have_another_go = not result_of_run andalso !autoInclude andalso !extendedFuncs andalso
                              not (!extended) andalso not (!superExtended)
        val _ = if have_another_go then print ("\nRepeating run with extended axioms\n") else ()
        val _ = if have_another_go then extended := true else ()
        val tptp_extended = if have_another_go then
                                #1 (read mapping filename)
                            else tptp
        val _ = if have_another_go then extended := false else ()
        val problems_extended = if have_another_go then Tptp.normalize tptp_extended else problems
        val result_of_run = if have_another_go then refuteAll filename tptp_extended problems_extended [] else result_of_run
        (* if the extended axioms were tried and didn't work then try the super extended ones if the relevant functions are present *)
        val have_another_go = have_another_go andalso not result_of_run andalso !superExtendedFuncs
        val _ = if have_another_go then print ("\nRepeating a second time with super extended axioms\n") else ()
        val _ = if have_another_go then superExtended := true else ()
        val tptp_extended = if have_another_go then
                                #1 (read mapping filename)
                            else tptp
        val _ = if have_another_go then superExtended := false else ()
        val problems_extended = if have_another_go then Tptp.normalize tptp_extended else problems
        val result_of_run = if have_another_go then refuteAll filename tptp_extended problems_extended [] else result_of_run
        (* --- give the constant limits a go --- *)
        (* 26/10/12 constant limits were found to cause Mathematica to hang on some problems *)
        (* so to avoid this happening they will not be used as part of autoInclude...        *)
        (*
        val have_another_go = have_another_go andalso not result_of_run andalso !constantLimitsFuncs
        val _ = if have_another_go then print ("\nRepeating a third time with constant limit axioms\n") else ()
        val _ = if have_another_go then constantLimits := true else ()
        val tptp_extended = if have_another_go then read mapping filename else tptp
        val _ = if have_another_go then constantLimits := false else ()
        val problems_extended = if have_another_go then Tptp.normalize tptp_extended else problems
        val result_of_run = if have_another_go then refuteAll filename tptp_extended problems_extended [] else result_of_run
        *)
        (* ---------------------------------------------------------------------------------------------- *)
        (* If iterative deepenging on w is set then need to run through the sequence again at full weight *)
        (* if it is not set then just end at this point to avoid wasting resources and upsetting          *)
        (* Mathematica etc.                                                                               *)
        (* ---------------------------------------------------------------------------------------------- *)
        val _ = if iterate_on_w then Waiting.maxweight := max_w else ()
        val _ = if not result_of_run andalso iterate_on_w then print ("\nIterative deepinging on w, w increased for repeat run\n") else ()
        val result_of_run = if not result_of_run andalso iterate_on_w then refuteAll filename tptp problems [] else result_of_run
        val have_another_go = not result_of_run andalso !autoInclude andalso !extendedFuncs andalso
                              not (!extended) andalso not (!superExtended) andalso iterate_on_w
        val _ = if have_another_go then print ("\nRepeating run with extended axioms\n") else ()
        val _ = if have_another_go then extended := true else ()
        val tptp_extended = if have_another_go then
                                #1 (read mapping filename)
                            else tptp
        val _ = if have_another_go then extended := false else ()
        val problems_extended = if have_another_go then Tptp.normalize tptp_extended else problems
        val result_of_run = if have_another_go then refuteAll filename tptp_extended problems_extended [] else result_of_run
        (* if the extended axioms were tried and didn't work then try the super extended ones if the relevant functions are present *)
        val have_another_go = have_another_go andalso not result_of_run andalso !superExtendedFuncs
        val _ = if have_another_go then print ("\nRepeating a second time with super extended axioms\n") else ()
        val _ = if have_another_go then superExtended := true else ()
        val tptp_extended = if have_another_go then
                                #1 (read mapping filename)
                            else tptp
        val _ = if have_another_go then superExtended := false else ()
        val problems_extended = if have_another_go then Tptp.normalize tptp_extended else problems
        val result_of_run = if have_another_go then refuteAll filename tptp_extended problems_extended [] else result_of_run
        (* --- give the constant limits a go --- *)
        (* 26/10/12 constant limits were found to cause Mathematica to hang on some problems *)
        (* so to avoid this happening they will not be used as part of autoInclude...        *)
        (*
        val have_another_go = have_another_go andalso not result_of_run andalso !constantLimitsFuncs
        val _ = if have_another_go then print ("\nRepeating a third time with constant limit axioms\n") else ()
        val _ = if have_another_go then constantLimits := true else ()
        val tptp_extended = if have_another_go then read mapping filename else tptp
        val _ = if have_another_go then constantLimits := false else ()
        val problems_extended = if have_another_go then Tptp.normalize tptp_extended else problems
        val result_of_run = if have_another_go then refuteAll filename tptp_extended problems_extended [] else result_of_run
        *)
        (* ----------------------------------------------------------------- *)
        (* have now tried all extended axioms at all max weights (2 of them) *)
        (* so can return the final result                                    *)
        (* ----------------------------------------------------------------- *)
      in
        result_of_run
      end
    handle
       IO.Io {name,function,cause} =>
         (display_status filename Tptp.ErrorStatus;
          if function = "TextIO.openIn" then (print ("File " ^ name ^ " not found!\n"); false)
          else fail_cleanly ("Exception IO raised for file " ^ filename ^ "\n" ^
                        "  name = " ^ name ^  ", function = " ^ function ^
                        ", cause = " ^ string_of_exn cause ^ "\n"))
     | Parse.NoParse =>
         (display_status filename Tptp.SyntaxErrorStatus;
          fail_cleanly ("Syntax error in file " ^ filename ^ "\n"))
     | Timeout =>
         (display_status filename Tptp.TimeoutStatus;
          fail_cleanly "Processor time limit exceeded.\n")
     | Thread.Thread.Interrupt =>
         (display_status filename Tptp.TimeoutStatus;
          fail_cleanly "Interrupt signal received.\n")
     | Error s =>
         (display_status filename Tptp.ErrorStatus;
          fail_cleanly (PROGRAM^" failed: " ^ s ^ ", file = " ^ filename ^ "\n"))
     | Bug s =>
         (display_status filename Tptp.ErrorStatus;
          fail_cleanly ("BUG found in "^PROGRAM^" program:\n" ^ s^ "  file = " ^ filename ^ "\n"))
     | OS.SysErr (msg,SOME e) => (display_status filename Tptp.ErrorStatus;
           fail_cleanly ("\n===> SysErr Exception " ^ (OS.errorName e) ^ " raised: " ^ (OS.errorMsg e) ^ "\n"))
     | OS.SysErr (msg,NONE) => (display_status filename Tptp.ErrorStatus;
           fail_cleanly ("\n===> SysErr Exception " ^ msg ^ "\n"))
     | e => (display_status filename Tptp.ErrorStatus;
             fail_cleanly ("Exception " ^ exnName e ^ " raised by "^PROGRAM^" program.\n" ^ "  file = " ^ filename ^ "\n  " ^ string_of_exn e ^ "\n"))

  fun proveAll mapping filenames =
      List.all (prove mapping) filenames;

 (*WD "orelse true" will only effect result if using metit on multiple
 files on the command line and a SZS status GaveUp is
 received. Something I don't think we do or need to do. StatusGaveUp
 was returning a code 0 which is incorrect. It is not clear why the
 QUIET tag turned this behaviour off. It was implemented in revision
 420 with no explanation*)

(* function to get pids using a system call - to be used to get the cpu usage of Qepcad etc *)
  fun getProcs () =
   OS.Process.system "ps >> pids.txt";
  fun getPID () =
   SysWord.toInt (Posix.Process.pidToWord (Posix.ProcEnv.getpid ()));

  fun getRCFTime () =
  let
    val pid = getPID()
    val fname = OS.FileSys.tmpName ()
    val _ = OS.Process.system ("ps -Oppid,utime,time " ^ ">>" ^ fname)
    val sin = TextIO.openIn fname
    fun cnvt_time_string s =
        (* this routine assumes that the time is in the form mins:seconds.tenths even when the number of mins > 60 *)
        (* (i.e. no separate designation of hours) this is how it is output on a Mac under OS X)                   *)
        let
           (* must allow for the case of there being an hours string though this will be rare *)
           val (mins_s::secs_s_l) = String.tokens (fn c => c= #":") s
        in
           if null secs_s_l then NONE else
                  let
                     val mins = Real.fromString mins_s
                     val mins_value = case mins of SOME min_val => min_val
                                        | NONE =>  0.0
                     val (secs_s::_) = secs_s_l
                     val secs = Real.fromString secs_s
                     val secs_value = case secs of SOME sec_val => sec_val
                                        | NONE => 0.0

                  in
                    SOME (Time.fromReal (mins_value*60.0+secs_value))
                  end
        end

    fun getQepcadCPU l =
        let
           val isRCFProcess =
                   case OS.Process.getEnv "Z3_NONLIN" of
                         NONE => (* Z3 not set up *)
                                  String.isSubstring "qepcad" l orelse String.isSubstring "MathKernel" l
                     |  SOME z3path =>
                             String.isSubstring "qepcad" l orelse String.isSubstring "MathKernel" l orelse
                              String.isSubstring (OS.Path.file z3path) l
        in
           if isRCFProcess then
              let
                 val (s_pid::s_ppid::s_utime::s_time::_) = String.tokens (fn c => c= #" ") l
                 val ppid_option = Int.fromString s_ppid
                 val utime_option = cnvt_time_string s_utime
                 val time_option = cnvt_time_string s_time
                 val cpu_option = case ppid_option of SOME ppid => if (ppid = pid) then utime_option else NONE
                                                  | NONE => NONE
              in
                 cpu_option
              end
          else
               NONE
        end
    fun read () =
       let
           val s = TextIO.inputLine sin
       in
           case s of
                SOME ss => (case getQepcadCPU ss of SOME cpu => SOME cpu | NONE => read ())
             |  NONE => ((OS.FileSys.remove fname);NONE)
       end
  in
    read ()
  end;


  (*Creates a new thread that monitors the cpu usage quits within a second of detecting that
    the total usage has exceeded the limit. Also checks wall clock time (with twice the limit)
    because sometimes QEPCAD gets stuck. Thanks to DCJM for help.*)
  (* Altered (by JPB) April 2012 to include output of symbols to indicate cpu usage and also *)
  (* to use ps etc to monitor RCF cpu usage as well as that of Metis.                        *)
  (* NB I have found empirically that the thread dies if the sleep is set to 1 or 2 seconds  *)
  (* (not immediately but after running for some time) while increasing it to 5 or 10 secs   *)
  (* appears to be more stable.                                                              *)

  fun monitor_cpu millisecs =
    if millisecs < display_time_in_millisecs then (* for short runs remove the overhead of calling ps etc and use wall time *)
	let val tw = Time.fromMilliseconds (IntInf.fromInt millisecs)
            fun poll (realT) =
                let val wall = Timer.checkRealTimer realT
                in
                   if wall > tw then
                     (display_status (!filename_p) Tptp.TimeoutStatus;
                      fail_cleanly "Wall time limit exceeded.\n")
                   else
                      sleeping (realT, Time.fromMicroseconds 1)
                end
                and sleeping (realT,w) = (OS.Process.sleep w; poll (realT))
        in
            Thread.Thread.fork(fn () => sleeping(Timer.startRealTimer(),Time.fromMicroseconds 1),[])
        end
    else (* for times greater than 10 secs use cpu time and also ps to keep track of RCF time *)
      let val t = Time.fromMilliseconds (IntInf.fromInt millisecs)
          and tw = Time.fromSeconds (IntInf.fromInt (2*millisecs))
        fun poll (cpuT,realT) =
          let val {usr, sys} = Timer.checkCPUTimer cpuT
              and wall       = Timer.checkRealTimer realT
              val RCFcpu_option = getRCFTime ()
              fun seconds i = Time.fromSeconds (IntInf.fromInt i)
              val _ = if !traceLevel = 1 andalso usr > seconds(!next_metis_symbol_due)
                      then (print(metis_symbol);
                            next_metis_symbol_due := !next_metis_symbol_due + metis_display_time_step)
                       else ()
              val _ = case RCFcpu_option of
                          SOME RCFcpu =>
                              if !traceLevel = 1 andalso RCFcpu > seconds (!next_RCF_symbol_due)
                              then (print(RCF_symbol);
                                    next_RCF_symbol_due := !next_RCF_symbol_due + RCF_display_time_step)
                              else ()
                        | NONE => ()
              val RCF_time_limit_exceeded = case RCFcpu_option of SOME RCFcpu =>
                                                                        RCFcpu > t
                                              |  NONE => false
          in
            if wall > tw orelse usr > t  orelse RCF_time_limit_exceeded (*or, usr+sys to include system kernel time*)
	    then (if !traceLevel = 1 then print("\n") else ();
	          display_status (!filename_p) Tptp.TimeoutStatus;
                  fail_cleanly "Processor time limit exceeded.\n")
            else sleeping (cpuT, realT, Time.fromSeconds 5)
          end
        and sleeping (cpuT,realT,w) = (OS.Process.sleep w; poll (cpuT,realT))
     in
       (* Version to wake up after 5 secs to allow dots to be put out on the screen *)
        Thread.Thread.fork(fn () => sleeping(Timer.startCPUTimer(),Timer.startRealTimer(),Time.fromSeconds 5),[])
     end;

end;

(* ------------------------------------------------------------------------- *)
(* Top level. LCP                                                            *)
(* ------------------------------------------------------------------------- *)

(*LCP: export from Poly/ML requires these declarations to be made within a function!
   also our version performs process communication.*)
fun metis () =
let
  (*BasicDebug val () = print "Running in basic DEBUG mode.\n" *)
  (*MetisDebug val () = print "Running in metis DEBUG mode.\n" *)

  val work = processOptions ()

  (* check any needed environment variables have been setup ok *)
  val _ = check_appropriate_environment_variables ()
  val _ = check_RCF_version_numbers () (* mainly to set the flag for the Z3 version *)
  (* Set the various case splitting options *)
  val _ = if !caseSplitting andalso !backTracking then
          let
             val _ = if !casesParam1Set then
                     Resolution.maxStackDepth := !casesParam1
                     else
                     Resolution.maxStackDepth := maxStackDepth
             val _ = if !casesParam2Set then
                     Waiting.SOSweightFactor := 0.1 * Real.fromInt (!casesParam2)
                     else
                     Waiting.SOSweightFactor := SOSweightFactor
             val _ = Active.max_splits_r := 0
          in
             ()
          end
          else if !caseSplitting then
          let
             val _ = if !casesParam1Set then
                     Active.max_splits_r := !casesParam1
                     else
                     Active.max_splits_r := max_splits_r
             val _ = if !casesParam2Set then
                     Waiting.SOSweightFactor := 0.1 * Real.fromInt (!casesParam2)
                     else
                     Waiting.SOSweightFactor := 1.0
             val _ = Resolution.maxStackDepth := 0
          in
             ()
          end
          else
          let
              val _ = Active.max_splits_r := 0
              val _ = Resolution.maxStackDepth := 0
              val _ = Waiting.SOSweightFactor := 1.0
          in
             ()
          end
  val _ = Literal.atom_weight_r := atom_weight_r
  (* -------------------------------------------------------------------------- *)
  (* if the maximum weight has not been specifically set then adjust it upwards *)
  (* to allow for the increase from SOSweightFactor.                            *)
  (* -------------------------------------------------------------------------- *)
  val w = !Waiting.maxweight
  val w = if !Waiting.maxweightSet then w else w * (!Waiting.SOSweightFactor)
  val _ = Waiting.maxweight := w

  val _ = if null work then usage "no input problem files"
          else monitor_cpu (!cpu_limit);
  val success = proveAll Tptp.defaultMapping work
in
  RCF.close_with_time false;

  if !QUIET then ()
  else print (runtime_msg());

  if RCF.icp_enabled() then
      print ("# RCF+ formulas refuted by:  EADM = " ^ Int.toString(!RCF.num_refuted_by_eadm)
             ^ ", ICP = " ^ Int.toString(!RCF.num_refuted_by_icp) ^ ".\n")
  else ();

  if !QUIET then ()
  else print ("Maximum weight in proof search: " ^ Int.toString (Real.floor (!Waiting.maxweight_used)) ^ "\n");
  exit {message = NONE, usage = false, success = success}
end
handle e => fail_cleanly ("Exception " ^ exnName e ^ " raised: " ^ string_of_exn e ^ "\n");
