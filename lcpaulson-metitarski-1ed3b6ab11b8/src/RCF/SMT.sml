(* ======================================================================== *)
(* Connection between RAHD/MetiTarski and SMT solvers (Z3 only, currently)  *)
(*                                                                          *)
(* by G.O.Passmore, Cambridge Computer Laboratory and LFCS, Edinburgh, 2012 *)
(* Contact: (e) grant.passmore@cl.cam.ac.uk   (w) www.cl.cam.ac.uk/~gp351/. *)
(* ======================================================================== *)

structure SMT :> SMT =
struct

open Useful;
open Common;

val smt_used = ref false;

(* reference variable to allow an RCF time limit to be set     *)
(* which over-rides the strategy time limits if it is non-zero *)
(* a zero value is ignored.                                    *)
(* The value is in milliseconds.                               *)
val RCF_time_limit = ref 0;


(* Code to create a log of all output sent to z3    *)
(* this can be fed directly into Z3 as an SMT2 file *)
val write_z3_log = false;
val z3_log = ref (NONE : TextIO.outstream option);
fun open_z3_log () = if write_z3_log then
                     (z3_log := (SOME (TextIO.openOut "Z3_log.smt2")) handle _ => z3_log := NONE)
                     else z3_log := NONE;
fun close_z3_log () = case (!z3_log) of SOME out_stream => (TextIO.output (out_stream,"\n(exit)\n");
                                                            TextIO.closeOut out_stream)
                                      | NONE => ();
(* NB in the following could just use the case statement to not write output when there is no log file  *)
(* but I thought an additional if would carry less overhead for the normal case when log is not written *)
fun write_to_z3_log str = if write_z3_log then
    case (!z3_log) of SOME out_stream => TextIO.output (out_stream,str)
                    | NONE => ()
    else ();



(* ------------------------------------------------------------- *)
(* code to create output files from RCF calls                    *)
(* ------------------------------------------------------------- *)
val Z3_write_rcf_problems_to_file = ref false;

val core_file_name = ref "Z3_rcf_problem_";

val Z3_rcf_problem_count = ref 0;

fun Z3_rcf_problem_file_name () =
    let
       val i = (!Z3_rcf_problem_count) + 1;
       val _ = Z3_rcf_problem_count := i;
    in
       (!core_file_name) ^ (Int.toString i) ^ ".smt2"
    end;

fun write_Z3_rcf_problem_file fml_str =
    let
       val fname = Z3_rcf_problem_file_name ()
       val out_strm = TextIO.openOut fname
       val _ = TextIO.output (out_strm,fml_str)
       val _ = TextIO.output (out_strm,"\n")
       val _ = TextIO.output (out_strm,"(check-sat)\n")
       val _ = TextIO.output (out_strm,"(exit)\n")
       val _ = TextIO.closeOut out_strm
    in
       ()
    end;




(* Z3 model history:
   We keep two, one for exact rational models, -and-
                one for real algebraic numbers (we store float approx's). *)

val model_history_rat = ref [] : (string * Rat.rat) list list ref;
val model_history_float = ref [] : (string * real) list list ref;

(* Use a model history? *)

val use_model_history = ref true;

(* In-stream and Out-stream of smt_proc object *)
val smt_proc = ref (NONE : ((TextIO.instream, TextIO.outstream) Unix.proc
			    * TextIO.instream * TextIO.outstream) option);

fun smt_is () =
    case !smt_proc of
	SOME (_, y, _) => SOME y
      | NONE => NONE;

fun smt_os () =
    case !smt_proc of
	SOME (_, _, z) => SOME z
      | NONE => NONE;

(* Code to determine version of Z3 as there is a parameter name change *)
(* between versions 4.3.1 and 4.3.2 !! - this affects the strings that *)
(* MetiTarski must send to request models.                             *)
val z3_4_3_2_or_newer = ref true;

fun z3_version_str () =
    let
	val temp_file_name = OS.FileSys.tmpName ()
	val command_str = "$Z3_NONLIN -version >> " ^ temp_file_name ^ "\n"
	val _ = OS.Process.system command_str
        val in_strm = TextIO.openIn temp_file_name
        val s_o = TextIO.inputLine in_strm
        val _ = TextIO.closeIn in_strm
        val _ = OS.FileSys.remove temp_file_name
    in
        case s_o of SOME s => s
                  | NONE => ""
    end;

fun z3_version_numbers v_str =
    let
	val prefix = "Z3 version "
        val _ = if String.isPrefix prefix v_str then () else
                raise Error ("unrecognized Z3 version string : "^ v_str)
        val lpf = String.size prefix
        val ver_num_str = String.extract (v_str,lpf,NONE)
        val vnum_list = String.fields (fn c => c = #".") ver_num_str
        val (vs1::vs2::vs3::[]) = if List.length vnum_list = 3 then vnum_list else
                raise Error ("couldn't interpret Z3 version number string : " ^ ver_num_str)
        val v1 = case Int.fromString vs1 of SOME i => i | NONE => raise Error ("Z3 v1 is not int : " ^ vs1)
        val v2 = case Int.fromString vs2 of SOME i => i | NONE => raise Error ("Z3 v2 is not int : " ^ vs2)
        val v3 = case Int.fromString vs3 of SOME i => i | NONE => raise Error ("Z3 v3 is not int : " ^ vs3)
    in
        (v1,v2,v3)
    end;

fun set_Z3_version_flag (v1,v2,v3) =
    if v1 > 4 orelse (v1=4 andalso v2 > 3) orelse (v1=4 andalso v2=3 andalso v3 > 1)
    then (z3_4_3_2_or_newer := true) else (z3_4_3_2_or_newer := false);

fun determine_Z3_version () =
    let
        (* determine the version of z3 *)
        val z3_vs = z3_version_str ()
	(* I don't think we need to print the Z3 version anymore. -Grant *)
        (* val _ = print z3_vs *)
        val (v1,v2,v3) = z3_version_numbers z3_vs
        val _ = set_Z3_version_flag (v1,v2,v3)
    in
        ()
    end;


(* Code to read Z3 return results *)
datatype Z3_return = Z3_sat|Z3_unsat|Z3_unknown|Z3_model of string|Z3_error of string|Z3_failed;

fun brackets_match str =
    let
	val chars = explode str
        fun bracket_count [] n = n
         |  bracket_count (#"("::cs) n = bracket_count cs (n+1)
         |  bracket_count (#")"::cs) n = bracket_count cs (n-1)
         |  bracket_count (_::cs) n = bracket_count cs n
        val n = bracket_count chars 0
    in
      n = 0
    end;

(* the following uses bracket matching to read a single SMTLib result from *)
(* Z3 which may be multi-line as in the case of (model .....               *)
fun read_single_Z3_output ios str_so_far =
    case (TextIO.inputLine ios) of NONE => raise Error "Z3 output terminated prematurely - NB this may be an OS timeout - "
     | SOME line =>
         let
             val str = str_so_far ^ line
         in
             if brackets_match str then str else read_single_Z3_output ios str
         end;


fun get_Z3_return () =
    let
       val ios = case smt_is() of SOME is => is |NONE => raise Error "No Z3 input stream"
       val return_string = read_single_Z3_output ios ""
       val _ = if brackets_match return_string then () else
               raise Error ("Unmatched brackets in Z3 return : " ^ return_string)
       val return_value =
           if String.isPrefix "sat" return_string then Z3_sat
           else
           if String.isPrefix "unsat" return_string then Z3_unsat
           else
           if String.isPrefix "unknown" return_string then Z3_unknown
           else
           if String.isPrefix "(model" return_string then Z3_model return_string
           else
           if String.isPrefix "(error" return_string then raise Error ("Z3 error : " ^ return_string)
           else
           if String.isPrefix "failed" return_string then Z3_failed
           else
           raise Error ("Unable to interpret Z3 return : " ^ return_string)
     in
           return_value
     end;


(* ------------------------------------------------------------------------- *)
(* Printing of RCF formulas in SMT-Lib 2.0 format.                           *)
(* ------------------------------------------------------------------------- *)

fun smt_print_rat (q : Rat.rat) =
    let fun smt_print_int i =
	    if (i < 0) then
		("(- " ^ (IntInf.toString (abs i)) ^ ".)")
	    else ((IntInf.toString i) ^ ".") in
	let val (a, b) = Rat.quotient_of_rat q in
	    if b = 1 then smt_print_int a else
	    ("(/ " ^ (smt_print_int a) ^ " " ^ (smt_print_int b) ^ ")")
	end
    end;

(* As of 16-April-2013, Z3 now has a built-in pi symbol, not accessible through NLSAT,
   but whose existence causes Z3 to raise an error if we try to declare a symbol called pi.
   So, we change the name of our pi to avoid clashes.
   Note that we make a corresponding transformation metit_our_pi --> pi in the models
   we store in the model history. See the function z3_get_model for this.
   *)

fun clean_xvar xvar =
    if (xvar = "metit_our_pi") then raise Useful.Error "The symbol metit_our_pi is special and users are not allowed to use it in their problems."
    else if (xvar = "pi") then "metit_our_pi"
    else Common.no_underscores xvar;

fun smt_print_term t =
  case t of
    Term.Var x => Common.varname x
  | Term.Rat r => smt_print_rat r
  | Term.Fn (s,[]) => clean_xvar s
  | Term.Fn("-", [tm]) => "(- " ^ (smt_print_term tm) ^ ")"
  | Term.Fn("^", [tm1, tm2]) => "(^ " ^ (smt_print_term tm1) ^ " " ^ (smt_print_term tm2) ^ ")"
  | Term.Fn("*", [tm1, tm2]) => "(* " ^ (smt_print_term tm1) ^ " " ^ (smt_print_term tm2) ^ ")"
  | Term.Fn("-", [tm1, tm2]) => "(- " ^ (smt_print_term tm1) ^ " " ^ (smt_print_term tm2) ^ ")"
  | Term.Fn("+", [tm1, tm2]) => "(+ " ^ (smt_print_term tm1) ^ " " ^ (smt_print_term tm2) ^ ")"
  | Term.Fn(a,_) => raise Useful.Error ("smt_print_term: no match for " ^ a);

fun smt_print_atom ((reln, [x, y]) : Atom.atom) =
    "(" ^ reln ^ " " ^ (smt_print_term x) ^ " " ^ (smt_print_term y) ^ ")"
  | smt_print_atom _ = raise Useful.Error "smt_print_atom: atom's reln must be binary";

local open Formula
in
  fun smt_print_fml False = "false"
    | smt_print_fml True  = "true"
    | smt_print_fml (Atom a) = smt_print_atom a
    | smt_print_fml (Not p)  = "(not " ^ (smt_print_fml p) ^ ")"
    | smt_print_fml (And(p,q)) = "(and " ^ (smt_print_fml p) ^ " " ^ (smt_print_fml q) ^ ")"
    | smt_print_fml (Or(p,q))  = "(or " ^ (smt_print_fml p) ^ " " ^ (smt_print_fml q) ^ ")"
    | smt_print_fml (Imp(p,q)) = "(=> " ^ (smt_print_fml p) ^ " " ^ (smt_print_fml q) ^ ")"
    | smt_print_fml (Iff(p,q)) = "(<=> " ^ (smt_print_fml p) ^ " " ^ (smt_print_fml q) ^ ")"
    | smt_print_fml (Forall(x,p)) = smt_qquant "forall" (x,p)
    | smt_print_fml (Exists(x,p)) = smt_qquant "exists" (x,p)
  and smt_qquant qname (x,p) = "(" ^ qname ^ " ((" ^ (Name.toString x) ^ " Real)) " ^ (smt_print_fml p) ^ ")"
end;

fun smt_print_fml_with_consts xvars fml =
     (String.concatWith "\n" (map (fn v => "(declare-fun " ^ (clean_xvar v) ^ " () Real)") xvars))
     ^ "\n" ^ "(assert " ^ (smt_print_fml fml) ^ ")";

(* addition to allow debug output that can be read back into MetiTarski *)
fun smt_print_fml_as_conjecture_with_consts xvars fml =
     let
        val formula = smt_print_fml fml
        val conjecture = if String.isPrefix "(not" formula then formula else ("(not (not " ^ formula ^ "))")
     in
     (String.concatWith "\n" (map (fn v => "(declare-fun " ^ (clean_xvar v) ^ " () Real)") xvars))
     ^ "\n" ^ "(assert "  ^ conjecture ^ ")"
     end;


fun smt_print_fml_with_consts_oneline xvars fml =
    (String.concatWith " " (map (fn v => "(declare-fun " ^ (clean_xvar v) ^ " () Real)") xvars))
    ^ " " ^ "(assert " ^ (smt_print_fml fml) ^ ")";
(* ------------------------------------------------------------------------- *)
(* SMT (Z3_nonlin) process I/O machinery                                     *)
(* ------------------------------------------------------------------------- *)


fun string_of_signal s =
    if s = Posix.Signal.hup then "Hangup"
    else if s = Posix.Signal.ill then "Illegal instruction"
    else if s = Posix.Signal.int then "Interrupt"
    else if s = Posix.Signal.kill then "Kill"
    else if s = Posix.Signal.segv then "Segmentation violation"
    else if s = Posix.Signal.bus then "Bus error"
    else "signalled " ^ SysWord.toString (Posix.Signal.toWord s);

local open Unix
in
fun stringOfStatus W_EXITED = "exited"
  | stringOfStatus (W_EXITSTATUS w) = "exit " ^ Word8.toString w
  | stringOfStatus (W_SIGNALED s) = string_of_signal s
  | stringOfStatus (W_STOPPED w) = "stopped";
end;

(* Signal: subprocess cpu time limit exceeded *)

(* Close SMT process *)

fun smt_close ignore_outcome =
    case !smt_proc of
	SOME (proc, instr, outstr) =>
	let
	    val _ = Unix.kill (proc, Posix.Signal.kill)
	    val status = Unix.fromStatus (Unix.reap proc)
            val _ = close_z3_log ()
	in
	    (if ignore_outcome orelse Useful.mem status [Unix.W_EXITED, Unix.W_SIGNALED 9] then ()
	     else if status = Unix.W_SIGNALED sigxcpu
	     then print "Processor time limit exceeded for SMT solver\n"
	     else print ("****ERROR: exit status = " ^ stringOfStatus status ^ "\n");
	     smt_proc := NONE)
	end
      | NONE => ();


fun stream_strings_until_prompt is prompt_str acc =
    case smt_is() of
	SOME is => (case TextIO.inputLine is of
			NONE => raise Useful.Error "SMT solver has unexpectedly terminated - NB this may be an OS timeout - "
		      | SOME line =>
			(Useful.chatting 4 andalso Useful.chat ("SMT: " ^ line);
			 if String.isSubstring prompt_str line
			 then List.rev acc
			 else stream_strings_until_prompt is prompt_str (line :: acc)))
      | NONE => raise Useful.Error "No SMT process.";

fun stream_strings_until_prefix is prefix_str acc =
    case smt_is() of
	SOME is => (case TextIO.inputLine is of
			NONE => raise Useful.Error "SMT solver has unexpectedly terminated - NB this may be an OS timeout - "
		      | SOME line =>
			(Useful.chatting 4 andalso Useful.chat ("SMT: " ^ line);
			 if String.isPrefix prefix_str line
			 then List.rev acc
			 else stream_strings_until_prefix is prefix_str (line :: acc)))
      | NONE => raise Useful.Error "No SMT process.";

fun smt_writeln (s) =
    case smt_os() of
	SOME os => ((* print ("--\nTo SMT: " ^ s ^ "\n--\n"); *) write_to_z3_log s;
		    TextIO.output (os, (s ^ "\n")); TextIO.flushOut os)
      | NONE => raise Useful.Error "No SMT process.";

(* Z3 config string for creating models *)

fun z3_produce_models_str () =
    if (!z3_4_3_2_or_newer) then
    ("(set-option :produce-models true)(set-option :pp.decimal true)"
    ^ "(set-option :pp.decimal-precision 20)")
    else
    ("(set-option :produce-models true)(set-option :pp-decimal true)"
    ^ "(set-option :pp-decimal-precision 20)");

(* Open an SMT process and setup the global smt_proc with I/O streams *)

fun smt_open() = case !smt_proc of
    SOME pio => pio
  | NONE =>
    let val smt_bin_str = case OS.Process.getEnv"Z3_NONLIN" of
			      NONE => Useful.die ("Environment variable Z3_NONLIN must " ^
						  "point to Z3 nonlinear (nlsat) binary")
			    | SOME s => s
	val proc = Unix.execute(smt_bin_str, [(* "NLSAT=true", *)"-in", "-smt2"])
	val (instr, outstr) = Unix.streamsOf proc
        val _ = open_z3_log ()
    in
	smt_used := true;
      	smt_proc := SOME (proc, instr, outstr);
	smt_writeln (z3_produce_models_str ());
	(proc, instr, outstr)
    end;

fun first_substring [] line = NONE
  | first_substring (s::ss) line =
      if String.isSubstring s line then SOME s
      else first_substring ss line;

fun strings_in_stream ss is =
   case TextIO.inputLine is of
       NONE => raise Error "SMT solver has unexpectedly terminated - NB this may be an OS timeout - "
     | SOME line =>
        (chatting 4 andalso chat ("SMT: " ^ line);
         if String.isSubstring "Error" line
         then raise Bug ("SMT ERROR MSG: " ^ line) else ();
         case first_substring ss line of
             SOME s => s
           | NONE => strings_in_stream ss is);  (*keep looking*)

fun strings_in_stream_until_prefix' p ls is =
   case TextIO.inputLine is of
       NONE => raise Error "SMT solver has unexpectedly terminated - NB this may be an OS timeout - "
     | SOME line =>
        (chatting 4 andalso chat ("SMT: " ^ line);
         case String.isPrefix p line of
             true => List.rev (line :: ls)
           | false => strings_in_stream_until_prefix' p (line :: ls) is);  (*keep looking*)

fun strings_in_stream_until_prefix p =
    strings_in_stream_until_prefix'
	p [] (case smt_is() of SOME is => is
			     | NONE => raise Useful.Error "No input stream for SMT.");

(* A parser for Z3 models, using the method of recursive descent.

   Example Z3 model string:
    (model (define-fun x () Real 0.5)
           (define-fun y () Real 12.91?)
           (define-fun z () Real 390.01))

   Result:

    > z3_parse_model "(model (define-fun x () Real 0.5)
                      (define-fun y () Real 12.91?)
                      (define-fun z () Real 390.01))";

    val it = [("x", 0.5, true), ("y", 12.91, false), ("z", 390.01, true)]:
      (string * real * bool) list

  We return a list of type (string * real * bool) list, consisting of
  triples of the form (v, f, e?) where v is a variable string, f is a
  float/real, and e? is true iff Z3 says the sample-pt is exact (not
  flagged with a `?' in Z3's printout of the model.)  Note that
  rounding is not an issue here w.r.t. soundness, as these models are
  only ever used to accelerate the recognition of SAT for RCF
  formulas. They are never used to prove that anything is UNSAT. *)

exception Z3_PARSE_MODEL of string;

fun z3_parse_model m_str =
    let fun parse_funs l =
	    case l of
		("(" :: r) =>
		(case parse_funs r of
		     (f_lst, s) => (f_lst, s))
	      | _ => (case parse_fun l of
			  (f, r) =>
			  if (hd r) = "(" then
			      let val (f_lst, r) = parse_funs r in
				  ([f] @ f_lst, r)
			      end
			  else ([f], r))
	and parse_fun l =
	    case l of
		[] => raise Z3_PARSE_MODEL "failure in parse_fun(1)"
	      | ("define" :: "-" :: "fun" :: name :: "(" :: ")" :: "Real" :: h :: "." :: t :: ")" :: rst)
		=> let val new_fn = (name,
				     (case (Real.fromString (String.concat [h, ".", t]))
				       of SOME r => r
					| NONE => raise Z3_PARSE_MODEL "failure in parse_fun(2)"),
				     true)
		   in (new_fn, rst) end
	      | ("define" :: "-" :: "fun" :: name :: "(" :: ")" :: "Real" :: h :: "." :: t :: "?" :: ")" :: rst)
		=> let val new_fn = (name,
				     (case (Real.fromString (String.concat [h, ".", t]))
				       of SOME r => r
					| NONE => raise Z3_PARSE_MODEL "failure in parse_fun(3)"),
				     false) (* <-- `?' indicates this witness is inexact. *)
		   in (new_fn, rst) end
	      | ("define" :: "-" :: "fun" :: name :: "(" :: ")" :: "Real" :: "(" :: "-" :: h :: "." :: t :: ")" :: ")" :: rst)
		=> let val new_fn = (name,
				     (case (Real.fromString (String.concat [h, ".", t]))
				       of SOME r => ~r
					| NONE => raise Z3_PARSE_MODEL "failure in parse_fun(2)"),
				     true)
		   in (new_fn, rst) end
	      | ("define" :: "-" :: "fun" :: name :: "(" :: ")" :: "Real" :: "(" :: "-" :: h :: "." :: t :: "?" :: ")" :: ")" :: rst)
		=> let val new_fn = (name,
				     (case (Real.fromString (String.concat [h, ".", t]))
				       of SOME r => ~r
					| NONE => raise Z3_PARSE_MODEL "failure in parse_fun(3)"),
				     false) (* <-- `?' indicates this witness is inexact. *)
		   in (new_fn, rst) end

	      | _ => raise Z3_PARSE_MODEL "failure in parse_fun(4)"
	fun parse_wrapper l =
	    case l of
		[] => raise Z3_PARSE_MODEL "failure in parse_wrapper(1)"
	      | ("(" :: "model" :: r) =>
		(case parse_funs r of
		     (model_lst, ")" :: s) => (model_lst, s)
		   | _ => raise Z3_PARSE_MODEL "failure in parse_wrapper(2)")
	      | _ => raise Z3_PARSE_MODEL "failure in parse_wrapper(3)"
    in case parse_wrapper (Common.lex (explode m_str))
	of (m, _) => m end;

(* Read a model from a current Z3 process which has deduced its current
   context to be SAT. *)

fun z3_get_model () =
    (smt_writeln "(get-model)";
     let
         fun wait_for_model () = case get_Z3_return () of Z3_model s => s
                                  | _ => wait_for_model ();
         val model_str = wait_for_model ()
	 val model = z3_parse_model model_str
     in
         (* print ("\n\nModel! String: " ^ model_str ^ ".\n");
	 print ("Parsed model: ");
	 map (fn (v, p, e) => (print (v ^ " |-> " ^ (Real.toString p) ^ "   exact: " ^ (Bool.toString e))))
	     model;
	 *)
     	 (* Adjust metit_our_pi to be called pi -- 16-April-2013 *)
	 map (fn (v, p, e) => (if (v = "metit_our_pi") then ("pi", p, e) else (v, p, e))) model
     end);

(* Get a model and add it to the model history. *)

fun z3_process_model () =
    if (!use_model_history) then
	let val m = z3_get_model()
	    fun rat_pt (_, _, e) = e
	    val rat_model = List.all rat_pt m
	    fun make_rat_pt (v, p, e) = (v, rat_of_float p)
	    fun make_rat_model model = map make_rat_pt model
	    fun make_float_model model = map (fn (v, p, e) => (v, p)) model
	in if rat_model then
	       model_history_rat := (make_rat_model m) :: (!model_history_rat)
	   else model_history_float := (make_float_model m) :: (!model_history_float)
	end
    else ();

(* ------------------------------------------------------------------------- *)
(* SMT (Z3_nonlin) SAT/UNSAT decision function (only for Exists formulas)    *)
(* ------------------------------------------------------------------------- *)
(* Returns true (for success) iff SMT solver (Z3_nonlin) returns UNSAT       *)

(* String for invoking Z3's NLSAT tactic with requisite pre-processing. *)

val nlsat_str =
    "(and-then simplify purify-arith propagate-values elim-term-ite"
    ^ " solve-eqs tseitin-cnf simplify nlsat)";

(* String for invoking Z3's NLSAT tactic with requisite pre-processing,
   but with factorisation disabled. *)

fun nlsat_no_factor_str () =
    if (!z3_4_3_2_or_newer) then
    ("(and-then simplify purify-arith propagate-values elim-term-ite"
    ^ " solve-eqs tseitin-cnf simplify (using-params nlsat :factor false :min-mag 256))")
    else
    ("(and-then simplify purify-arith propagate-values elim-term-ite"
    ^ " solve-eqs tseitin-cnf simplify (using-params nlsat :factor false :algebraic-min-mag 256))");

val nlsat_var_shuffle_str =
    "(check-sat-using (and-then simplify purify-arith propagate-values"
    ^ " elim-term-ite solve-eqs tseitin-cnf simplify (using-params nlsat :shuffle-vars true :seed 13)))";

val nlsat_factor_before_str =
    "(and-then simplify purify-arith propagate-values elim-term-ite"
    ^ " solve-eqs tseitin-cnf factor simplify nlsat)";

(* A light-weight `quick-check' Z3 strategy for use in speculative
   RCF.  Note that we give a hard limit to lifting conflicts and
   algebraic number symbolic crossovers. We give two variants, one
   for univariate and one for multivariate. *)

fun nlsat_quick_check_univ_str ()
  = if(!z3_4_3_2_or_newer) then
    ("(and-then "
    ^ "simplify "
    ^ "purify-arith "
    ^ "propagate-values "
    ^ "elim-term-ite "
    ^ "solve-eqs "
    ^ "tseitin-cnf "
    ^ "simplify "
    ^ "(using-params nlsat :max-conflicts 3 :factor false :min-mag 256))")
   else
    ("(and-then "
    ^ "simplify "
    ^ "purify-arith "
    ^ "propagate-values "
    ^ "elim-term-ite "
    ^ "solve-eqs "
    ^ "tseitin-cnf "
    ^ "simplify "
    ^ "(using-params nlsat :max-conflicts 3 :factor false :algebraic-min-mag 256))");

fun nlsat_quick_check_multiv_str ()
  = if(!z3_4_3_2_or_newer) then
    ("(and-then "
    ^ "simplify "
    ^ "purify-arith "
    ^ "propagate-values "
    ^ "elim-term-ite "
    ^ "solve-eqs "
    ^ "tseitin-cnf "
    ^ "simplify "
    ^ "(using-params nlsat :max-conflicts 3 :factor true :min-mag 256))")
    else
    ("(and-then "
    ^ "simplify "
    ^ "purify-arith "
    ^ "propagate-values "
    ^ "elim-term-ite "
    ^ "solve-eqs "
    ^ "tseitin-cnf "
    ^ "simplify "
    ^ "(using-params nlsat :max-conflicts 3 :factor true :algebraic-min-mag 256))");

(* ------------------------------------------------------------------------- *)
(* SMT (Z3_nonlin) SAT/UNSAT decision function (only for Exists formulas),   *)
(*  with user-controllable proof strategies.                                 *)
(* ------------------------------------------------------------------------- *)
(* Returns true (for success) iff SMT solver (Z3_nonlin) returns UNSAT       *)

fun smt_unsat_with_strategy xvars Formula.False _ _ = true
  | smt_unsat_with_strategy xvars Formula.True _ _ = false
  | smt_unsat_with_strategy [] _ _ _ = false     (* no variables, so abandon *)
  | smt_unsat_with_strategy xvars fm init_str strategy_str =
   let
     val (proc, from_smt, to_smt) = smt_open()
     val varlist = string_tuple xvars
     val fml_str = smt_print_fml_with_consts xvars fm
     val conjecture_str = smt_print_fml_as_conjecture_with_consts xvars fm
     val _ = if (!Z3_write_rcf_problems_to_file) then write_Z3_rcf_problem_file conjecture_str else ()
     val _ = chatting 3 andalso chat ("----- Calling Z3 on\n" ^ fml_str ^ "\n-----")
     val _ = if not(init_str = "") then smt_writeln init_str else ()
     val _ = smt_writeln fml_str
     val _ = smt_writeln strategy_str
     val result = case get_Z3_return () of Z3_sat => "sat"
                                        |  Z3_unsat => "unsat"
                                        |  Z3_unknown => "unknown"
                                        |  Z3_error s => raise Error s
                                        |  _ => ""
     val _ = chatting 3 andalso chat ("----- Z3 result: " ^ result ^ "\n")
     val _ = if (result = "sat") then z3_process_model() else ();
     val _ = smt_writeln "(reset)"
   in
      let val res = (result = "unsat")
      in
	  res
      end
   end;

(* ------------------------------------------------------------------------- *)
(* SMT (Z3_nonlin) Judgment decision function (only for Exists formulas),    *)
(*  with default strategy (no univ_factor) and boolean return value.         *)
(* ------------------------------------------------------------------------- *)

fun smt_unsat xvars Formula.False = true
  | smt_unsat xvars Formula.True = false
  | smt_unsat [] _ = false    (*no variables, so abandon*)
  | smt_unsat xvars fm =
   let
     val (proc, from_smt, to_smt) = smt_open()
     val varlist = string_tuple xvars
     val fml_str = smt_print_fml_with_consts xvars fm
     val conjecture_str = smt_print_fml_as_conjecture_with_consts xvars fm
     val _ = if (!Z3_write_rcf_problems_to_file) then write_Z3_rcf_problem_file conjecture_str else ()
     val _ = chatting 3 andalso chat ("----- Calling Z3 on\n" ^ fml_str ^ "\n-----")
     val _ = smt_writeln fml_str
     val check_str = if (length xvars = 1) then nlsat_no_factor_str () else nlsat_factor_before_str
     val _ = smt_writeln ("(check-sat-using " ^ check_str ^
                 (if !RCF_time_limit = 0 then ")" else (":timeout "^(Int.toString (!RCF_time_limit))^")")))
     val result = case get_Z3_return () of Z3_sat => "sat"
                                        |  Z3_unsat => "unsat"
                                        |  Z3_unknown => "unknown"
                                        |  Z3_error s => raise Error s
                                        |  _ => ""
     val _ = chatting 3 andalso chat ("----- Z3 result: " ^ result ^ "\n")
     val _ = if (result = "sat") then z3_process_model() else ();
     val _ = smt_writeln "(reset)"
   in
      let val res = (result = "unsat")
      in res end
   end;

(* ------------------------------------------------------------------------- *)
(* SMT (Z3_nonlin) Judgment decision function (only for Exists formulas),    *)
(*  with user-controllable proof strategies.                                 *)
(* ------------------------------------------------------------------------- *)
(* Returns Common.tv       *)

fun smt_judgment_with_strategy xvars Formula.False _ _ = Common.Unsat
  | smt_judgment_with_strategy xvars Formula.True _ _ = Common.Sat NONE
  | smt_judgment_with_strategy [] _ _ _ = Common.Sat NONE     (* no variables, so abandon *)
  | smt_judgment_with_strategy xvars fm init_str strategy_str =
   let
     val (proc, from_smt, to_smt) = smt_open()
     val varlist = string_tuple xvars
     val fml_str = smt_print_fml_with_consts xvars fm
     val conjecture_str = smt_print_fml_as_conjecture_with_consts xvars fm
     val _ = if (!Z3_write_rcf_problems_to_file) then write_Z3_rcf_problem_file conjecture_str else ()
     val _ = chatting 3 andalso chat ("----- Calling Z3 on\n" ^ fml_str ^ "\n-----")
     val _ = if not(init_str = "") then smt_writeln init_str else ()
     val _ = smt_writeln fml_str
     val _ = smt_writeln strategy_str
     val result = case get_Z3_return () of Z3_sat => "sat"
                                        |  Z3_unsat => "unsat"
                                        |  Z3_unknown => "unknown"
                                        |  Z3_error s => raise Error s
                                        |  _ => ""
     val _ = chatting 3 andalso chat ("----- Z3 result: " ^ result ^ "\n")
     val _ = if (result = "sat") then z3_process_model() else ();
     val _ = smt_writeln "(reset)"
   in
       if (result = "unsat") then Common.Unsat
       else if (result = "sat") then Common.Sat NONE
       else Common.Unknown
   end;

(* Some more Z3 strategies.
   First, their strings. *)

(* Stop after a conflict is detected. *)

val nlsat_no_conflict_str
  = "(check-sat-using (and-then "
    ^ "simplify "
    ^ "purify-arith "
    ^ "propagate-values "
    ^ "elim-term-ite "
    ^ "solve-eqs "
    ^ "tseitin-cnf "
    ^ "(using-params nlsat :max-conflicts 2)))";

(* Stop after a conflict is detected,
   no factorisation. *)

val nlsat_no_conflict_no_factor_str
  = "(check-sat-using (and-then "
    ^ "simplify "
    ^ "purify-arith "
    ^ "propagate-values "
    ^ "elim-term-ite "
    ^ "solve-eqs "
    ^ "tseitin-cnf "
    ^ "(using-params nlsat :max-conflicts 1 :factor false)))";

val nlsat_random_var_ord_str
  = "(check-sat-using (and-then "
    ^ "simplify "
    ^ "purify-arith "
    ^ "propagate-values "
    ^ "elim-term-ite "
    ^ "solve-eqs "
    ^ "tseitin-cnf "
    ^ "(using-params nlsat :shuffle-vars true :seed 2)))";

fun z3_linear_relax xvars fm timelimit =
 smt_unsat_with_strategy
     xvars
     fm
     ("(set-option :nl-arith-gb false)\n" ^
      "(set-option :nl-arith false)\n" ^
      "(set-option :nlsat false)")
     ("(check-sat-using (and-then simplify smt) :timeout "
      ^ (Int.toString (if !RCF_time_limit = 0 then timelimit else !RCF_time_limit) ^ ")"));

fun z3_nlsat xvars fm timelimit =
 smt_unsat_with_strategy
     xvars
     fm
     ""
     ("(check-sat-using " ^ (if (length xvars = 1) then nlsat_no_factor_str () else nlsat_factor_before_str)
       ^ (if !RCF_time_limit = 0 then ")" else (" :timeout " ^ (Int.toString (!RCF_time_limit)) ^ ")")));

(* Quick-check function for speculative RCF.  Note that this function
   returns a Common.tv value, with `Unknown' meaning, very roughly,
   `likely unsat.' *)

fun z3_nlsat_quick_check xvars fm =
 smt_judgment_with_strategy
     xvars
     fm
     ""
     ("(check-sat-using " ^
      (if (length xvars = 1) then
	   nlsat_quick_check_univ_str ()
       else nlsat_quick_check_multiv_str ()) ^ ")");

fun z3_nlsat_no_factor xvars fm timelimit =
 smt_unsat_with_strategy
     xvars
     fm
     ""
     ("(check-sat-using " ^ (nlsat_no_factor_str ()) ^ " :timeout "
      ^ (Int.toString timelimit) ^ ")");

fun z3_nl_arith xvars fm timelimit =
 smt_unsat_with_strategy
     xvars
     fm
     ("(set-option :nl-arith-gb false)\n" ^
      "(set-option :nl-arith true)")
     ("(check-sat-using (and-then simplify smt) :timeout "
      ^ (Int.toString timelimit) ^ ")");

fun z3_nl_arith_gb xvars fm timelimit =
 smt_unsat_with_strategy
     xvars
     fm
     ("(set-option :nl-arith-gb true)\n" ^
      "(set-option :nl-arith false)\n")
     ("(check-sat-using (and-then simplify smt) :timeout "
      ^ (Int.toString timelimit) ^ ")");

(* Try Z3 with no conflicts, returning a Common.tv *)

fun z3_no_conflicts_judgment xvars fm =
    smt_judgment_with_strategy
    xvars
    fm
    ""
    nlsat_no_conflict_str;

(* Try Z3 with no conflicts, no factorisation,
   returning a Common.tv *)

fun z3_no_conflicts_no_factor_judgment xvars fm =
    smt_judgment_with_strategy
    xvars
    fm
    ""
    nlsat_no_conflict_no_factor_str;


end;
