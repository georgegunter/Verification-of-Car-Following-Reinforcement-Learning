(* Interface to QepcadB (refactored from older versions of MetiTarski) *)

structure Qepcad :> Qepcad =
struct

open Useful;
open Common;

val write_trace_file = false;
(* Was QepcadB used in the current session? *)
val qepcad_used = ref false;

(* ---------------------------------------------------------------------- *)
(* Abstraction of a Formula for qepcad.                                   *)
(* ---------------------------------------------------------------------- *)

(* The following code is unused, and doesn't handle rational numbers! *)

(*Creates a constant from a term, in order to perform abstraction.*)

fun qepcad_pn (Term.Var v) = [v]
  | qepcad_pn (Term.Fn("+", args)) = qepcad_pn_args "sum" args
  | qepcad_pn (Term.Fn("-", [x]))  = qepcad_pn_args "neg" [x]
  | qepcad_pn (Term.Fn("-", args)) = qepcad_pn_args "diff" args
  | qepcad_pn (Term.Fn("*", args)) = qepcad_pn_args "prod" args
  | qepcad_pn (Term.Fn("/", args)) = qepcad_pn_args "quo" args
  | qepcad_pn (Term.Fn("^", args)) = qepcad_pn_args "expt" args
  | qepcad_pn (Term.Fn(f, args)) = qepcad_pn_args f args
  | qepcad_pn _ = raise Bug "Qepcad.qepcad_pn"
and qepcad_pn_args f args = f :: List.concat (map qepcad_pn args);

fun qepcad_pn_term t = Term.Fn(no_underscores (String.concatWith "Q" (qepcad_pn t)), []);

fun qepcad_abs_term t =
  case t of
    Term.Var _ => t
  | Term.Rat _ => t
  | Term.Fn (s,[]) => t
  | Term.Fn("/", _) => t
  | Term.Fn("^",[t1,t2]) => if Poly.is_natural t2 then Term.Fn("^", [qepcad_abs_term t1, t2])
                            else qepcad_pn_term t
  | Term.Fn(f,args) => if mem f (Poly.algebraic_ops) then Term.Fn(f, map qepcad_abs_term args)
                       else qepcad_pn_term t;

local open Formula
in
fun qepcad_abs_fm False = False
  | qepcad_abs_fm True = True
  | qepcad_abs_fm (Atom (p,args)) = Atom (p, map qepcad_abs_term args)
  | qepcad_abs_fm (Not p) = Not (qepcad_abs_fm p)
  | qepcad_abs_fm (And(p,q)) = And(qepcad_abs_fm p, qepcad_abs_fm q)
  | qepcad_abs_fm (Or(p,q)) = Or(qepcad_abs_fm p, qepcad_abs_fm q)
  | qepcad_abs_fm _ = raise Bug "Qepcad.qepcad_abs_fm"

end;

val qepcad_abs_fm =
  (fn fm =>
     let val fm' = qepcad_abs_fm fm;
         val _ = chatting 4 andalso
                 chat ("qepcad_abs_fm (" ^ Formula.toString fm ^ ") = " ^
                       Formula.toString fm' ^ "\n")
     in fm' end);

(* ---------------------------------------------------------------------- *)
(* Generate the Textual Formula for qepcad.                               *)
(* ---------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Printing of RCF terms to qepcad.                                          *)
(* ------------------------------------------------------------------------- *)

fun cons s (ln::lns) = (s^ln) :: lns
  | cons s [] = [s];

fun qepcad_print_term (t, lns) =
  case t of
    Term.Var x => cons (varname x) lns
  | Term.Rat r => cons (Rat.toString r) lns
  | Term.Fn (s,[]) => cons (no_underscores s) lns
  | Term.Fn("-",[tm]) => cons "(-" (qepcad_print_term (tm, cons ")" lns))
  | Term.Fn("^",[tm1,tm2]) => qepcad_print_term (tm1, cons "^" (qepcad_print_term (tm2, lns)))
  | Term.Fn("*",_)         => cons "(" (qepcad_print_prod (t, cons ")" lns))
  | Term.Fn("-",[tm1,tm2]) => qepcad_infix_term "-" tm1 tm2 lns
  | Term.Fn("+",[tm1,tm2]) => qepcad_infix_term "+" tm1 tm2 lns
  | Term.Fn(a,_) => raise Error ("qepcad_print_term: no match for " ^ a)
and qepcad_infix_term sym x y lns =
       cons "(" (qepcad_print_term (x, cons sym (qepcad_print_term (y, cons ")" lns))))
and qepcad_print_prod (Term.Fn("*",[tm1,tm2]), lns) =  (*avoiding needless parentheses*)
      qepcad_print_prod (tm1, cons " " (qepcad_print_prod (tm2,lns)))
  | qepcad_print_prod (Term.Rat r, lns) = cons ("(" ^ Rat.toString r ^ ")") lns
      (*e.g. x (-1), not x -1 !!*)
  | qepcad_print_prod tlns = qepcad_print_term tlns

(* ------------------------------------------------------------------------- *)
(* Printing of RCF atoms to qepcad.                                          *)
(* ------------------------------------------------------------------------- *)

fun qepcad_print_atom (rel, [x,y], lns) =
      cons "[" (qepcad_print_term (x, cons rel (qepcad_print_term (y, cons "]" lns))))
  | qepcad_print_atom (p,_, _) = raise Error ("qepcad_print_atom2: " ^ p);

(* ------------------------------------------------------------------------- *)
(* Printing of RCF fol formulas to qepcad.                                   *)
(* ------------------------------------------------------------------------- *)

(* Quantifiers *)

fun exquant vars = String.concat (map (fn v => "(E " ^ v ^ ") ") vars);

(*"For infinitely many" quantifier: sound to use if the solution set is open.*)
fun fexquant vars = String.concat (map (fn v => "(F " ^ v ^ ") ") vars);

fun uquant vars = String.concat (map (fn v => "(A " ^ v ^ ") ") vars);

local open Formula
in
  fun fml_lines (False,lns) = cons "FALSE" lns
    | fml_lines (True,lns)  = cons "TRUE" lns
    | fml_lines (Atom (p,args), lns) = qepcad_print_atom (p, args, lns)
    | fml_lines (Not (Atom ("=",args)), lns) = qepcad_print_atom (" /=", args, lns)
    | fml_lines (Not (Atom ("<=",args)), lns) = qepcad_print_atom ("<", rev args, lns)
    | fml_lines (Not p, lns)   = cons "[~" (fml_lines (p, cons "]" lns))
    | fml_lines (And(p,q), lns)    = qinfix "/\\" p q lns
    | fml_lines (Or(p,q), lns)     = qinfix "\\/" p q lns
    | fml_lines (Imp(p,q), lns)    = qinfix "==>" p q lns
    | fml_lines (Iff(p,q), lns)    = qinfix "<=>" p q lns
    | fml_lines (Forall(x,p), lns) = qquant "A" (x,p) lns
    | fml_lines (Exists(x,p), lns) = qquant "E" (x,p) lns
  and qinfix sym p q (lns) = cons "[" (fml_lines (p, sym :: fml_lines (q, cons "]" lns)))
  and qquant qname (x,p) lns = cons ("(" ^ qname ^ Name.toString x ^ ") ") (fml_lines(p,lns));
end;

fun qepcad_str xvars fm = String.concatWith "" ((exquant xvars) :: (fml_lines (fm, ["."])));

(* ---------------------------------------------------------------------- *)
(* Calling qepcad from ML.                                                *)
(* ---------------------------------------------------------------------- *)

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

(** Code to generate trace output in a separate file. **)
val qe_trace = ref (NONE : TextIO.outstream option);

fun open_qe_trace() = case !qe_trace of
    SOME os => os
  | NONE =>
      let val {base,...} = OS.Path.splitBaseExt
                             (List.last (CommandLine.arguments ()) handle Empty => "XXX")
          val os = TextIO.openOut(base ^ ".trace");
      in  qe_trace := SOME os; os
      end;

(** Code to manage the separate process that runs QEPCAD **)

val qe_proc = ref (NONE : ((TextIO.instream, TextIO.outstream) Unix.proc * TextIO.instream * TextIO.outstream) option);

fun open_qepcad() = case !qe_proc of
    SOME pio => pio
  | NONE =>
      let
        val qexec = case OS.Process.getEnv"qe" of
                     NONE => die "Environment variable qe not set"
                   | SOME s => s ^ "/bin/qepcad"
	val proc = Unix.execute(qexec,["+N18000000","-noecho"]) : (TextIO.instream, TextIO.outstream) Unix.proc
	             handle OS.SysErr _ => die ("Please install a QEPCAD executable at " ^ qexec)
	val (instr,outstr) = Unix.streamsOf proc
	val _ = qepcad_used := true
      in
      	qe_proc := SOME (proc,instr,outstr); (proc,instr,outstr)
      end;

(*We don't want orphaned QEPCAD processes piling up...*)
fun close_qepcad ignore_outcome = case !qe_proc of
    SOME (proc,instr,outstr) =>
      let
	val _ = Unix.kill (proc, Posix.Signal.kill)
	val status = Unix.fromStatus (Unix.reap proc)
      in
	  (if ignore_outcome orelse mem status [Unix.W_EXITED, Unix.W_SIGNALED 9] then ()
	   else if status = Unix.W_SIGNALED sigxcpu
	   then print "Processor time limit exceeded for QEPCAD\n"
	   else print ("****ERROR: exit status = " ^ stringOfStatus status ^ "\n");
	   (* Added by Grant on 15-11-2011: Make !qe_proc NONE for restart,
   	      used for machine learning. *)
	   qe_proc := NONE)
      end
  | NONE => ();

fun first_substring [] line = NONE
  | first_substring (s::ss) line =
      if String.isSubstring s line then SOME s
      else first_substring ss line;

(*Return the first matched string in QEPCAD's output*)
fun strings_in_stream ss is =
   case TextIO.inputLine is of
       NONE => raise Error "QEPCAD has unexpectedly terminated - NB this may be an OS timeout - "
     | SOME line =>
        (chatting 4 andalso chat ("QEPCAD: " ^ line);
         if String.isSubstring "Error" line
         then raise Bug ("QEPCAD ERROR MSG: " ^ line) else ();
         case first_substring ss line of
             SOME s => s
           | NONE => strings_in_stream ss is);  (*keep looking*)

fun await_string_in_stream s is = ignore (strings_in_stream [s] is);

fun out_lines (ost,[]) = TextIO.output (ost, "\n")
  | out_lines (ost,s::ss) =
      (chatting 4 andalso chat s; TextIO.output (ost, s); out_lines (ost,ss));

(* ------------------------------------------------------------------------- *)
(* Variable list.                                                            *)
(* ------------------------------------------------------------------------- *)

fun string_tuple [] = "()"
  | string_tuple ss = "(" ^ String.concatWith "," ss ^ ")";

(* Returns true (for success) iff QEPCAD returns FALSE *)
fun call_qepcad' _ xvars uvars Formula.False = true
  | call_qepcad' _ xvars uvars Formula.True = false
  | call_qepcad' _ [] [] _ = false    (*no variables, so abandon*)
  | call_qepcad' opn xvars uvars fm =
   let
     val varlist = string_tuple (xvars@uvars)
     and qnt = if opn then fexquant xvars else exquant xvars ^ uquant uvars
     val fml = qnt :: fml_lines (fm, ["."])
     val _ = chatting 3 andalso chat ("Calling QEPCAD\n  " ^ String.concat fml)
     val (proc,from_qep,to_qep) = open_qepcad();
     fun respond_to_prompt p ss =
	  (chatting 4 andalso chat ("Prompt: " ^ p);
	   await_string_in_stream p from_qep;
	   out_lines (to_qep,ss))
     val result = (respond_to_prompt "Enter an informal description  between" ["[]"];
                   respond_to_prompt "Enter a variable list" [varlist];
                   respond_to_prompt "Enter the number of free variables" ["0"];
                   respond_to_prompt "Enter a prenex formula" fml;
                   respond_to_prompt "Before Normalization" ["go"];
                   respond_to_prompt "rojection" ["go"];
                   	(*covers "At the end of projection phase" and "Before Projection"*)
                   respond_to_prompt "Before Choice" ["go"];
                   respond_to_prompt "Before Solution" ["solution T"];
                   strings_in_stream ["FALSE","TRUE"] from_qep)
   in
      if write_trace_file then
	  TextIO.output(open_qe_trace(),
			Formula.toString (Formula.listMkExists(map Name.fromString xvars,fm))
			^ ("\n RESULT = " ^ result ^ "\n\n"))
      else ();
      respond_to_prompt "Before Solution" ["continue"];
      let val res = (result = "FALSE")
      in res end
   end;

(* A variant of call_qepcad' for SAT checking using univariate
   relaxations.  Returns TRUE iff QepcadB says the given formula is
   indeed SAT. Expects a quantifier-free formula whose only Skolem
   constant is "x". *)

fun call_qepcad_sat Formula.False = false
  | call_qepcad_sat Formula.True = true
  | call_qepcad_sat fm =
   let
     val fml = "(E x)" :: fml_lines (fm, ["."])
     val _ = chatting 3 andalso
             chat ("Calling QEPCAD with univ_relaxation\n  " ^ String.concat fml)
     val (proc,from_qep,to_qep) = open_qepcad();
     fun respond_to_prompt p ss =
	  (chatting 4 andalso chat ("Prompt: " ^ p);
	   await_string_in_stream p from_qep;
	   out_lines (to_qep,ss))
     val result = (respond_to_prompt "Enter an informal description  between" ["[]"];
                   respond_to_prompt "Enter a variable list" ["(x)"];
                   respond_to_prompt "Enter the number of free variables" ["0"];
                   respond_to_prompt "Enter a prenex formula" fml;
                   respond_to_prompt "Before Normalization" ["go"];
                   respond_to_prompt "rojection" ["go"];
                   	(*covers "At the end of projection phase" and "Before Projection"*)
                   respond_to_prompt "Before Choice" ["go"];
                   respond_to_prompt "Before Solution" ["solution T"];
                   strings_in_stream ["FALSE","TRUE"] from_qep)
   in
       respond_to_prompt "Before Solution" ["continue"];
       let val res = (result = "TRUE")
       in res end
   end;



(* A variant of call_qepcad' used for machine learning data gathering.
   This variant ensures QepcadB is closed after each decision. *)

(*Returns true (for success) iff QEPCAD returns FALSE*)
fun call_qepcad'_ml _ xvars uvars Formula.False = Common.Unsat
  | call_qepcad'_ml _ xvars uvars Formula.True = Common.Sat NONE
  | call_qepcad'_ml _ [] [] _ = Common.Sat NONE   (*no variables, so abandon*)
  | call_qepcad'_ml opn xvars uvars fm =
   let
     val varlist = string_tuple (xvars@uvars)
     and qnt = if opn then fexquant xvars else exquant xvars ^ uquant uvars
     val fml = qnt :: fml_lines (fm, ["."])
     val _ = chatting 3 andalso chat ("Calling QEPCAD'\n  " ^ String.concat fml)
     val (proc,from_qep,to_qep) = open_qepcad();
     fun respond_to_prompt p ss =
	  (chatting 4 andalso chat ("Prompt: " ^ p);
	   await_string_in_stream p from_qep;
	   out_lines (to_qep,ss))
     val result = (respond_to_prompt "Enter an informal description  between" ["[]"];
                   respond_to_prompt "Enter a variable list" [varlist];
                   respond_to_prompt "Enter the number of free variables" ["0"];
                   respond_to_prompt "Enter a prenex formula" fml;
                   respond_to_prompt "Before Normalization" ["go"];
                   respond_to_prompt "rojection" ["go"];
                   	(*covers "At the end of projection phase" and "Before Projection"*)
                   respond_to_prompt "Before Choice" ["go"];
                   respond_to_prompt "Before Solution" ["solution T"];
                   strings_in_stream ["FALSE","TRUE"] from_qep)
   in
       (respond_to_prompt "Before Solution" ["finish"];
(*	let val _ = strings_in_stream ["SPACE."] from_qep
	    val _ = TextIO.inputLine from_qep
	    val time_str = case TextIO.inputLine from_qep of
			       SOME s => s
			     | NONE => ""
	in print ("\n\n QepcadB Time string: " ^ time_str ^ "\n") end; *)
	case result of
	    "TRUE" => Common.Sat NONE
	  | "FALSE" => Common.Unsat
	  | _ => Common.Unknown)
   end;

end;
