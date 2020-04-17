(* ======================================================================== *)
(*       Interface between MetiTarski and Mathematica's MathKernel          *)
(*                                                                          *)
(* by G.O.Passmore, Cambridge Computer Laboratory and LFCS, Edinburgh, 2012 *)
(* Contact: (e) grant.passmore@cl.cam.ac.uk   (w) www.cl.cam.ac.uk/~gp351/. *)
(* ======================================================================== *)

structure Mathematica :> Mathematica =
struct

open Algebra;
open Common;

(* Was Mathematica used in the current MetiTarski seesion? *)

val mathematica_used = ref false;

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

(* A default set of options used for invoking MathKernel inequality
   decision methods *)

val mk_default_options =
    { Exact_Pi = false,
      ARS_Decision = false,
      Brown_Projection = true,
      CAD = true,
      CAD_Combine_Cells = O_True,
      CAD_Extra_Precision = 30.103,
      CAD_Default_Precision = 30.103,
      CAD_Sort_Variables = true,
      Equational_Constraints_CAD = O_Automatic,
      FGLM_Basis_Conversion = false,
      FGLM_Elimination = O_Automatic,
      Generic_CAD = true,
      Groebner_CAD = true,
      Linear_Equations = true,
      Linear_QE = O_True,
      LW_Decision = true,
      LW_Preprocessor = O_Automatic,
      Project_Algebraic = O_Automatic,
      Prove_Multiplicities = O_Automatic,
      Quadratic_QE = O_Automatic,
      QVS_Preprocessor = O_False,
      Reduce_Powers = true,
      Root_Reduced = false,
      Simplex = true,
      Thread_Or = true,
      Zeng_Decision = false};

(* Active Mathematica inequality decision method configuration *)

val mk_active_options =
    ref mk_default_options;

(* val mk_active_options = ref mk_options_2; *)

(* Time limit for each Mathematica decision.  Note that this is on a
   `per decision' basis.  A limit of Time.zeroTime means there is no
   limit. *)

(*val mk_decision_time_limit = (* ref Time.zeroTime; *)
    ref (Time.fromSeconds 60);*)
val mk_decision_time_limit = ref (Time.fromSeconds 60);

(* Note that when interacting with Mathematica's MathKernel, we need
   to always wrap function calls with the Mathematica function
   FullForm[].  For example,

        In[1]:= Discriminant[a x^2 + b x + c, x]

                 2
        Out[1]= b  - 4 a c

   is not easily parsable.  But,

        In[1]:= FullForm[Discriminant[a x^2 + b x + c, x]]

        Out[1]//FullForm= Plus[Power[b, 2], Times[-4, a, c]]

   is a more suitable representation for our needs.

   * A few examples of formulas we need to be able to parse:

      { >   Plus[Times[Rational[-1, 2], Power[b, 3], c],
        >    Times[Rational[1, 2], Power[a, 3], Power[c, 2]],
        >    Times[Rational[3, 2], a, b, Power[c, 2]],
        >    Times[Rational[1, 2], Power[c, 3]]]     ,

        >   Times[Rational[1, 17], Plus[Times[Rational[1, 2], a, Power[x, 2]],
        >     Times[Rational[1, 47], Plus[-10, Times[-1, Power[x, 2]]]],
        >     Times[Rational[11, 3], Power[w, 3], y, z]]]    ,

       Plus[Power[x1, 2], Power[x2, 30], Times[Rational[10, 7], x1, x19, x3]] }.
 *)

(* 27-Feb-2012: Moved lexer and related functions into Common.sml so
   that SMT.sml could use them. *)

(* Datatype for Mathematica expressions we support *)

datatype m_tm = Int of IntInf.int
              | Var of string
              | Plus of m_tm list
              | Times of m_tm list
              | Power of m_tm * int
	      | Rational of IntInf.int * IntInf.int
              | Sin of m_tm
              | Cos of m_tm
              | Sinh of m_tm
              | Cosh of m_tm
              | Abs of m_tm
              | Log of m_tm
              | Tan of m_tm
              | Sqrt of m_tm
              | CubeRoot of m_tm
              | ArcTan of m_tm
              | ArcSin of m_tm
              | ArcCos of m_tm
              | Exp of m_tm
              | UnaryMinus of m_tm
              | Function of m_tm list
              | Slot of int
              | List of m_tm list;

datatype m_fm = Tm of m_tm | True | False | Aborted;

(* Exception for non-parsing *)

exception MATHEMATICA_PARSING of string;

(* Given a list of token strings, construct a parse tree for
    Mathematica terms using the method of recursive descent. *)

fun parse_m_tm_lst l =
    case l of
        "[" :: r =>
        (case parse_m_tm_lst r of
             (tm_lst, "]" :: s) => (tm_lst, s)
           | (_, s :: s') => raise MATHEMATICA_PARSING ("bad term list: " ^ s)
           | _ => raise MATHEMATICA_PARSING "bad term list")
      | _ => case parse_m_tm' l of
                 (tm, r) =>
                 if (hd r) = "," then
                     let val (tm_lst, r) = parse_m_tm_lst (tl r) in
                         ([tm] @ tm_lst, r)
                     end
                 else ([tm], r)

and parse_m_tm' l =
    case l of
        [] => raise MATHEMATICA_PARSING "expected non-empty token list"
      | "Plus" :: r => let val (tm_lst, s) = parse_m_tm_lst r in
                           (Plus tm_lst, s)
                       end
      | "Times" :: r => let val (tm_lst, s) = parse_m_tm_lst r in
                            (Times tm_lst, s)
                        end
      | "Function" :: r => let val (tm_lst, s) = parse_m_tm_lst r in
                            (Function tm_lst, s)
                        end
      | "Slot" :: r => let val (slot_lst, s) = parse_m_tm_lst r in
                           case slot_lst of
                               [Int slot_id] => (Slot (IntInf.toInt slot_id), s)
                             | _ => raise MATHEMATICA_PARSING "bad Slot[_]"
                       end
      | "Power" :: r => let val (tm_lst, s) = parse_m_tm_lst r in
                            case tm_lst of
				[x, Int y] => (Power (x, IntInf.toInt y), s)
                              | _ => raise MATHEMATICA_PARSING "bad Power[_]"
                        end
      | "Rational" :: r => let val (tm_lst, s) = parse_m_tm_lst r in
                               case tm_lst of
                                   [Int x, Int y] => (Rational (x, y), s)
                                 | _ => raise MATHEMATICA_PARSING "bad Rational[_]"
                           end
      | "List" :: r => let val (tm_lst, s) = parse_m_tm_lst r in
                           (List tm_lst, s)
                       end
      | "-" :: r =>
	(case IntInf.fromString (hd r) of
             SOME i => (Int (~ i), (tl r))
	   | NONE => raise MATHEMATICA_PARSING "expected integer")
      | x :: r =>
	(case IntInf.fromString x of
             SOME i => (Int i, r)
           | NONE =>
             if List.all alpha_num (explode x) then (Var x, r)
             else raise MATHEMATICA_PARSING ("bad expression: " ^ (String.concatWith " " l)));

(* Parse a lex'd representation of a Mathematica FullForm term into
   our internal m_tm syntax tree. *)

fun parse_m_tm l = let val (x, y) = parse_m_tm' l in x end;

(* Parse a lex'd repesentation of a Mathematica FullForm formula *)

fun parse_m_fm l =
    case l of
        [] => raise MATHEMATICA_PARSING "expected non-empty token list"
      | ["True"] => True
      | ["False"] => False
      | ["$", "Aborted"] => Aborted
      | _ => Tm (parse_m_tm l);

(* Given a string representation of a Mathematica term, construct a
    Mathematica parse tree of type m_tm.  Note that the Mathematica
    ops Plus and Times are not forced to be binary.  To force this,
    further apply the composition (m_tm_of_mt_tm o mt_tm_of_m_tm). *)

fun m_tm_of_str s = parse_m_tm (lex (explode s));

(* Given a string representation of a Mathematica formula, construct a
   Mathematica parse tree of type m_fm. The above notes on
   m_tm_of_str apply. *)

fun m_fm_of_str s = parse_m_fm (lex (explode s));

(* Convert a constructed Mathematica parse-tree to an MT term.

   Note that many associative Mathematica functions (Plus, Times, ...)
   use a syntax in which they take as parameters simply lists of
   arguments.  But, for MetiTarski terms, we want our function symbols
   to have a fixed arity.  In particular, Plus and Times for MT,
   treated as Term.Fn("+", ...) and Term.Fn("*", ...) are binary
   functions.  So, we need to turn our Mathematica arbitrary-arity
   functions into nestings of binary ones in this conversion below. *)

fun args_to_bin_op (f, args) =
    case args of
        [x, y] => Term.Fn (f, [x, y])
      | x :: xs =>
        Term.Fn (f, [x, args_to_bin_op (f, xs)])
      | _ => raise MATHEMATICA_PARSING "cannot make ops binary in term";

fun mt_tm_of_m_tm t =
    case t of
	Int i => Term.Rat (Rat.rat_of_intinf i)
      | Var s => Term.Fn (s, []) (* Vars become Skolem constants *)
      | Plus tm_lst => args_to_bin_op ("+", List.map mt_tm_of_m_tm tm_lst)
      | Times tm_lst => args_to_bin_op ("*", List.map mt_tm_of_m_tm tm_lst)
      | Power (x, y) => Term.Fn ("^", [mt_tm_of_m_tm x,
                                       Term.Rat (Rat.rat_of_int y)])
      | Rational (p, q) => Term.Rat (Rat.rat_of_quotient (p, q));

(* Convert an MT term into a Mathematica term tree.  Note that we
   construct Mathematica terms in which every op is binary.

   Note: If exact_pi is true, then we treat Term.Fn ("pi",[]) as Pi,
    the real Mathematica representation of pi.

   31-May-2012: Added support for (unary) subtraction. - GP *)

fun m_tm_of_mt_tm t exact_pi =
    case t of
        Term.Rat x => Rational (Rat.quotient_of_rat x)
      | Term.Fn (s, []) => if (exact_pi andalso s = "pi")
                           then Var "Pi" else Var s
      | Term.Fn ("+", [x, y]) => Plus [(m_tm_of_mt_tm x exact_pi),
                                       (m_tm_of_mt_tm y exact_pi)]
      | Term.Fn ("*", [x, y]) => Times [(m_tm_of_mt_tm x exact_pi),
                                        (m_tm_of_mt_tm y exact_pi)]
      | Term.Fn ("/", [x, y]) => Times [(m_tm_of_mt_tm x exact_pi),
                                        Power ((m_tm_of_mt_tm y exact_pi), ~1)]
      | Term.Fn ("-", [x, y]) => Plus [(m_tm_of_mt_tm x exact_pi),
                                       Times [(m_tm_of_mt_tm y exact_pi),
                                              Int ~1]]
      | Term.Fn ("-", [x]) => Times [(m_tm_of_mt_tm x exact_pi),
                                     Int ~1]
      | Term.Fn ("sin", [x]) => Sin (m_tm_of_mt_tm x exact_pi)
      | Term.Fn ("cos", [x]) => Cos (m_tm_of_mt_tm x exact_pi)
      | Term.Fn ("sinh", [x]) => Sinh (m_tm_of_mt_tm x exact_pi)
      | Term.Fn ("cosh", [x]) => Cosh (m_tm_of_mt_tm x exact_pi)
      | Term.Fn ("abs", [x]) => Abs (m_tm_of_mt_tm x exact_pi)
      | Term.Fn ("ln", [x]) => Log (m_tm_of_mt_tm x exact_pi)
      | Term.Fn ("tan", [x]) => Tan (m_tm_of_mt_tm x exact_pi)
      | Term.Fn ("sqrt", [x]) => Sqrt (m_tm_of_mt_tm x exact_pi)
      | Term.Fn ("cbrt", [x]) => CubeRoot (m_tm_of_mt_tm x exact_pi)
      | Term.Fn ("arctan", [x]) => ArcTan (m_tm_of_mt_tm x exact_pi)
      | Term.Fn ("arcsin", [x]) => ArcSin (m_tm_of_mt_tm x exact_pi)
      | Term.Fn ("arccos", [x]) => ArcCos (m_tm_of_mt_tm x exact_pi)
      | Term.Fn ("exp", [x]) => Exp (m_tm_of_mt_tm x exact_pi)
      | Term.Fn ("^", [x, Term.Rat y]) =>
        let val (p, q) = Rat.quotient_of_rat y
	in if (q = 1) then Power (m_tm_of_mt_tm x exact_pi, IntInf.toInt p)
           else raise MATHEMATICA_PARSING "non-integral power" end
      | Term.Var v => Var (Common.varname v)
      | Term.Var _ => raise MATHEMATICA_PARSING ("universal quantification not supported with MT+Mathematica.")
      | _ => raise MATHEMATICA_PARSING ("cannot convert mt_tm to m_tm: " ^ (Term.toString t) ^ ".");

(* Convert a Mathematica term tree into a string representation
   suitable for Mathematica input.  As above, we require that the
   Mathematica ops are used as binary functions.  This can be
   guaranteed by passing the Mathematica term through the composition
   (m_tm_of_mt_tm o mt_tm_of_m_tm). *)

fun intinf_to_str i = if i >= 0 then IntInf.toString i else "-" ^ IntInf.toString (~i);
fun int_to_str i = if i >= 0 then Int.toString i else "-" ^ Int.toString (~i);

fun m_tm_to_str t = case t of
	   Rational (p, 1) => intinf_to_str p
	 | Rational (p, q) => "Rational[" ^ intinf_to_str p ^ "," ^ intinf_to_str q ^ "]"
	 | Int i => intinf_to_str i
         | Var s => s
         | Plus [x, y] => "Plus[" ^ m_tm_to_str x ^ "," ^ m_tm_to_str y ^ "]"
         | Times [x, y] => "Times[" ^ m_tm_to_str x ^ "," ^ m_tm_to_str y ^ "]"
         | Power (x, y) => "Power[" ^ m_tm_to_str x ^ "," ^ int_to_str y ^ "]"
         | UnaryMinus x => "Times[-1," ^ m_tm_to_str x ^ "]"
         | Sin x => "Sin[" ^ m_tm_to_str x ^ "]"
         | Cos x => "Cos[" ^ m_tm_to_str x ^ "]"
         | Sinh x => "Sinh[" ^ m_tm_to_str x ^ "]"
         | Cosh x => "Cosh[" ^ m_tm_to_str x ^ "]"
         | Abs x => "Abs[" ^ m_tm_to_str x ^ "]"
         | Log x => "Log[" ^ m_tm_to_str x ^ "]"
         | Tan x => "Tan[" ^ m_tm_to_str x ^ "]"
         | Sqrt x => "Sqrt[" ^ m_tm_to_str x ^ "]"
         | CubeRoot x => "CubeRoot[" ^ m_tm_to_str x ^ "]"
         | ArcTan x => "ArcTan[" ^ m_tm_to_str x ^ "]"
         | ArcSin x => "ArcSin[" ^ m_tm_to_str x ^ "]"
         | ArcCos x => "ArcCos[" ^ m_tm_to_str x ^ "]"
         | Exp x => "Exp[" ^ m_tm_to_str x ^ "]"
         (* | RootIntervals x => "RootIntervals[{" ^ m_tm_to_str x ^ "}]" *)
         | _ => raise MATHEMATICA_PARSING "cannot convert Mathematica tm to string";

(* The analogue of the above Mathematica tm->str conversion but using
   a more compact output format.

   8-Nov-2012 (grant): Updated to not print unnecessary parentheses.
    Rule: Let t = Op1(Op2(a,b), Op3(c,d)).
          Let prec(Op_i) > prec(Op_j) iff Op_i has higher priority than Op_j.
          Then, for associative operators,
           - omit parens around Op2(a,b) iff prec(Op1) <= prec(Op2), and
           - omit parens around Op3(c,d) iff prec(Op1) <= prec(Op3).

    Example: t = Times(Plus(x,y), z).
      prec(Times) > Prec(Plus), so:
        --> (x + y)*z.
    Example: t = Times(Plus(x,Plus(y,z)), w).
      prec(Times) > prec(Plus), so:
        --> "(" pp(Plus(x,Plus(y,z))) ")" * pp(w)
        --> "(" pp(x) + pp(Plus(y,z)) ")" * pp(w)
        --> "(" x + y + z ")" * w.

    (We currently only do this for Plus and Times.)
*)

fun m_tm_to_str_compact t =
    (* Precedence of operators *)
    let fun prec t =
            case t of
                Plus _ => 1
              | Times _ => 2
              | Power _ => 3
              | _ => 4
        fun paren t x y op_str =
            let val pp_x = if prec(t) <= prec(x) then
                               m_tm_to_str_compact x
                           else "(" ^ m_tm_to_str_compact x ^ ")"
                val pp_y = if prec(t) <= prec(y) then
                               m_tm_to_str_compact y
                           else "(" ^ m_tm_to_str_compact y ^ ")"
            in pp_x ^ op_str ^ pp_y end
    in case t of
	   Rational (p, 1) => intinf_to_str p
	 | Rational (p, q) => "(" ^ intinf_to_str p ^ "/" ^ intinf_to_str q ^ ")"
	 | Int i => intinf_to_str i
         | Var s => s
         | Plus [x, y] => paren t x y "+"
         | Times [x, y] => paren t x y "*"
         | Power (x, y) => "(" ^ m_tm_to_str_compact x ^ " ^ " ^ int_to_str y ^ ")"
         | UnaryMinus x => "(0 - " ^ m_tm_to_str_compact x ^ ")"
         | Sin x => "Sin[" ^ m_tm_to_str_compact x ^ "]"
         | Cos x => "Cos[" ^ m_tm_to_str_compact x ^ "]"
         | Sinh x => "Sinh[" ^ m_tm_to_str_compact x ^ "]"
         | Cosh x => "Cosh[" ^ m_tm_to_str_compact x ^ "]"
         | Abs x => "Abs[" ^ m_tm_to_str_compact x ^ "]"
         | Log x => "Log[" ^ m_tm_to_str_compact x ^ "]"
         | Tan x => "Tan[" ^ m_tm_to_str_compact x ^ "]"
         | Sqrt x => "Sqrt[" ^ m_tm_to_str_compact x ^ "]"
         | CubeRoot x => "CubeRoot[" ^ m_tm_to_str_compact x ^ "]"
         | ArcTan x => "ArcTan[" ^ m_tm_to_str_compact x ^ "]"
         | ArcSin x => "ArcSin[" ^ m_tm_to_str_compact x ^ "]"
         | ArcCos x => "ArcCos[" ^ m_tm_to_str_compact x ^ "]"
         | Exp x => "Exp[" ^ m_tm_to_str_compact x ^ "]"
         (* | RootIntervals x => "RootIntervals[{" ^ m_tm_to_str_compact x ^ "}]" *)
         | _ => raise MATHEMATICA_PARSING "cannot convert Mathematica tm to string"
    end;

(* Given a MetiTarski term, return a string representation of a
   corresponding Mathematica term. *)

fun mt_tm_to_m_tm_str t exact_pi = m_tm_to_str (m_tm_of_mt_tm t exact_pi);

(* And a more compact variant of the above function. *)

fun mt_tm_to_m_tm_str_compact t exact_pi =
    m_tm_to_str_compact (m_tm_of_mt_tm t exact_pi);

(* Open a Mathematica MathKernel process.
   As of September 27th, 2011, we now have our own line-based REPL for Mathematica.
   This makes interacting with Mathematica *much* more efficient!

   The following note is then deprecated, but left here for historical
   reasons:

   Note that unlike with QepcadB, we need to use StreamIO here.  We
   are only able to reuse a little bit of code from QepcadB.sml (this
   reuse happens with the closing and most of the opening of the MK
   proc), as reading and writing for us is quite different due to the
   use of StreamIO.  Also, opening an MK proc requires we do a bit of
   handshaking. *)


(* Old mk_proc for when StreamIO was required

val mk_proc = ref (NONE : ((TextIO.instream, TextIO.outstream) Unix.proc
                           * TextIO.StreamIO.instream * TextIO.StreamIO.outstream) option);

*)

val mk_proc = ref (NONE : ((TextIO.instream, TextIO.outstream) Unix.proc
                           * TextIO.instream * TextIO.outstream) option);

(* Update the MK instream to a new value (used for applicative I/O) *)

fun update_mk_is new_is =
    case !mk_proc of
        SOME m => let val (a, b, c) = m in
                      mk_proc := SOME (a, new_is, c)
                  end
      | NONE => ();

(* Hard-coded MathKernel binary path, only for use while developing
   and testing this module in the SML toplevel. *)

val mk_hc_bin = "/Applications/Mathematica.app/Contents/MacOS/MathKernel";
val use_mk_hc_bin = ref false; (* <- Should be false when building MT binaries *)

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

(* Close MathKernel process *)

fun mk_close ignore_outcome =
    case !mk_proc of
        SOME (proc, instr, outstr) =>
        let
            (* TODO: Consider first trying to quit nicely with Quit[] *)
            val _ = Unix.kill (proc, Posix.Signal.kill)
            val status = Unix.fromStatus (Unix.reap proc)
        in
            (if ignore_outcome orelse Useful.mem status [Unix.W_EXITED, Unix.W_SIGNALED 9] then ()
             else if status = Unix.W_SIGNALED sigxcpu
             then print "Processor time limit exceeded for Mathematica\n"
             else print ("****ERROR: exit status = " ^ stringOfStatus status ^ "\n");
             mk_proc := NONE)
        end
      | NONE => ();

(* In-stream and Out-stream of mk_proc object *)

fun mk_is () =
    case !mk_proc of
        SOME (_, y, _) => SOME y
      | NONE => NONE;

fun mk_os () =
    case !mk_proc of
        SOME (_, _, z) => SOME z
      | NONE => NONE;

(* Finally, with our own custom Mathematica REPL, we can now do
   QepcadB-style line-based reading and writing! *)

fun stream_strings_until_prompt is prompt_str acc =
    case mk_is() of
        SOME is => (case TextIO.inputLine is of
                        NONE => raise Useful.Error "Mathematica has unexpectedly terminated - NB this may be an OS timeout - "
                      | SOME line =>
                        (Useful.chatting 4 andalso Useful.chat ("MathKernel: " ^ line);
                         (* print ("MathKernel: " ^ line); *)
                         if String.isSubstring prompt_str line
                         then  List.rev acc
                         else stream_strings_until_prompt is prompt_str (line :: acc)))
      | NONE => raise Useful.Error "No MathKernel process yet spawned.";

(* Deprecated StreamIO read and write functions:
(* Read as many chars as possible from mk_proc (for now, up to 10,000) *)

local open TextIO.StreamIO in
fun mk_read () =
    case mk_is() of
        SOME is =>
        let val n = case canInput (is, 10000) of
                        SOME n => n
                      | NONE => 0
        in
            if n>0 then
                let val (r : string, new_is) = inputN (is, n)
                    val _ = update_mk_is new_is
                in SOME r end
            else NONE
        end
      | NONE => NONE;
end;

(* Write a string to mk_proc *)

fun mk_write (s) =
    case mk_os() of
        SOME os => TextIO.StreamIO.output (os, s)
      | NONE => ();

(* Write a line to mk_proc *)

fun mk_writeln (s) = mk_write (s ^ "\n");

(* Keep blocking until a string is read which contains a given
   substring. *)

fun block_until_read' s c =
    case mk_read() of
        SOME r =>
        let val c' = c ^ r in
            if String.isSubstring s c' then c'
            else block_until_read' s c'
        end
      | NONE => block_until_read' s c;

fun block_until_read s = block_until_read' s "";
*)

(* Write a line to mk_proc *)

fun mk_writeln (s) =
    case mk_os() of
        SOME os => TextIO.output (os, (s ^ "\n"))
      | NONE => raise Useful.Error "No MathKernel process spawned.";

(* Make Mathematica inequality options string *)

fun mk_opt_str (opt_rec : mk_opts) =
    let val mk_bool_str = (fn x => if x then "True" else "False")
        val mk_tfa_str = (fn x => case x of
                                      O_True => "True"
                                    | O_False => "False"
                                    | O_Automatic => "Automatic")
    in
        String.concat["SetSystemOptions[\"InequalitySolvingOptions\" -> {",
                      "\"ARSDecision\" -> ", (mk_bool_str (#ARS_Decision opt_rec)), ", ",
                      "\"BrownProjection\" -> ", (mk_bool_str (#Brown_Projection opt_rec)), ", ",
                      "\"CAD\" -> ", (mk_bool_str (#CAD opt_rec)), ", ",
                      "\"CADCombineCells\" -> ", (mk_tfa_str (#CAD_Combine_Cells opt_rec)), ", ",
                      "\"CADDefaultPrecision\" -> ", (Real.toString (#CAD_Default_Precision opt_rec)), ", ",
                      "\"CADExtraPrecision\" -> ", (Real.toString (Real.abs (#CAD_Extra_Precision opt_rec))), ", ",
                      "\"CADSortVariables\" -> ", (mk_bool_str (#CAD_Sort_Variables opt_rec)), ", ",
                      (* "\"ContinuedFractionRootIsolation\" -> True, ", *)
                      "\"EquationalConstraintsCAD\" -> ", (mk_tfa_str (#Equational_Constraints_CAD opt_rec)), ", ",
                      "\"FGLMBasisConversion\" -> ", (mk_bool_str (#FGLM_Basis_Conversion opt_rec)), ", ",
                      "\"FGLMElimination\" -> ", (mk_tfa_str (#FGLM_Elimination opt_rec)), ", ",
                      "\"GenericCAD\" -> ", (mk_bool_str (#Generic_CAD opt_rec)), ", ",
                      "\"GroebnerCAD\" -> ", (mk_bool_str (#Groebner_CAD opt_rec)), ", ",
                      "\"LinearDecisionMethodCrossovers\" -> {0,30,20}, ",
                      "\"LinearEquations\" -> ", (mk_bool_str (#Linear_Equations opt_rec)), ", ",
                      "\"LinearQE\" -> ", (mk_tfa_str (#Linear_QE opt_rec)), ", ",
                      "\"LWDecision\" -> ", (mk_bool_str (#LW_Decision opt_rec)), ", ",
                      "\"LWPreprocessor\" -> ", (mk_tfa_str (#LW_Preprocessor opt_rec)), ", ",
                      "\"ProjectAlgebraic\" -> ", (mk_tfa_str (#Project_Algebraic opt_rec)), ", ",
                      "\"ProveMultiplicities\" -> ", (mk_tfa_str (#Prove_Multiplicities opt_rec)), ", ",
                      "\"QuadraticQE\" -> ", (mk_tfa_str (#Quadratic_QE opt_rec)), ", ",
                      "\"QVSPreprocessor\" -> ", (mk_tfa_str (#QVS_Preprocessor opt_rec)), ", ",
                      "\"ReducePowers\" -> ", (mk_bool_str (#Reduce_Powers opt_rec)), ", ",
                      "\"RootReduced\" -> ", (mk_bool_str (#Root_Reduced opt_rec)), ", ",
                      "\"Simplex\" -> ", (mk_bool_str (#Simplex opt_rec)), ", ",
                      "\"ThreadOr\" -> ", (mk_bool_str (#Thread_Or opt_rec)), ", ",
                      (* No internal comma after the final setting! *)
                      "\"ZengDecision\" -> ", (mk_bool_str (#Zeng_Decision opt_rec)),
                      "}];"]
    end;

(* Wenda Li's polynomial real root isolation (Mathematica) code *)

val root_iso_code =
    "isolateRoots[polys_] :=    \n \
\Module[{sortedRoots, sortedRootsEx, minDiff, expr},   \n \
\   expr = Or @@ ((# == 0) & /@ polys);   \n \
\   sortedRoots =    \n \
\    Sort[x /. SemialgebraicComponentInstances[expr, x], Less];   \n \
\   sortedRootsEx = Sort[Append[sortedRoots, 0], Less];   \n \
\   (* minDiff calculates a suitable size for isolation interval such    \n \
\       that those intervals don't overlap and exclude 0 *)   \n \
\   minDiff =   \n \
\    Min[(#[[2]] - #[[1]]) & /@   \n \
\      Transpose[{Drop[N /@ sortedRootsEx, -1],   \n \
\        Drop[N /@ sortedRootsEx, 1]}]];   \n \
\    (If [# \\[Element] Algebraics, {MinimalPolynomial[#],   \n \
\        IsolatingInterval[#, minDiff]}, #]) & /@ sortedRoots   \n \
\   ]\n";

(* A simple handshaking function.  This should be run immediately
   after opening up an MK process.  It just does a simple check to
   make sure the MK is being responsive, and crucially gets the system
   into a state so that all strings read from it will begin with
   "\nOut[...]//FullForm=" and end with "\n\nIn[...]:= ", with the
   '...' being numbers. *)

fun mk_handshake () =
    ((* print ("\n" ^ (mk_opt_str (!mk_active_options)) ^ "\n"); *)
     mk_writeln ("InitTime = TimeUsed[]");

     (* mk_writeln ("FullForm[1+1]");
      block_until_read "FullForm= 2\n\nIn[4]:= " *)

     (* We need to install into Mathematica's runtime Wenda Li's
        polynomial real root isolation code *)

     mk_writeln (root_iso_code);

     (*** Setup our custom Mathematica REPL so we can use line-based I/O ***)
     mk_writeln ("While[True, NV = Input[\"InMT>\\n\"]; Print[NV]; If[NV == Quit, Quit[]]]"));

(* Open a MathKernel process and setup the global mk_proc with I/O streams *)

fun mk_open() = case !mk_proc of
    SOME pio => pio
  | NONE =>
    let val mk_bin_str =
              if !use_mk_hc_bin then mk_hc_bin
              else case OS.Process.getEnv"MATH_KERNEL" of
                  NONE => raise Useful.Error
                              ("Environment variable MATH_KERNEL must " ^
                               "point to Mathematica MathKernel binary")
                | SOME s => s
        val proc = Unix.execute("/bin/bash", ["-c", mk_bin_str ^ " -noinit"]) : (TextIO.instream, TextIO.outstream) Unix.proc
        val (instr, outstr) = Unix.streamsOf proc
        (* val (instr', outstr') = (TextIO.getInstream instr, TextIO.getOutstream outstr) *)
    in
        mk_proc := SOME (proc, instr, outstr);
        mk_handshake();
        mathematica_used := true;
        stream_strings_until_prompt instr "InMT>" [];
        (* ^^^ This ignored all characters in stream until our custom REPL prompt is read. *)
        (proc, instr, outstr)
    end;

(* Extract result token list from Mathematica:

   Due to the handshaking function, we know that all reads from MK
   should be of the following form (giving a concrete example):

      "\nOut[2]//FullForm= Power[Plus[-1, x], 2]\n\nIn[3]:= ".

   Given such a string, we will extract out the result bit, which is:
   "Power[Plus[-1, x], 2]".  We also do some checks to ensure we are
   interpreting the string correctly. *)

(*
local open List in

fun take_between' l from to sub_l count =
    case l of [] => sub_l
            | x :: xs =>
              if (count >= from andalso count <= to) then
                  take_between' xs from to (x :: sub_l) (count + 1)
              else if count > to then sub_l
              else take_between' xs from to sub_l (count + 1);

fun take_between l from to =
    List.rev (take_between' l from to [] 0);

fun mk_result_tokens () =
    let val s = block_until_read ":= "
 (*	val _ = print ("\nread: " ^ s) *)
        val l = lex (explode s)
        val len_l = length l
    in
        if nth (l, 0) = "Out" andalso
           nth (l, 6) = "FullForm" andalso
           nth (l, 7) = "=" andalso
           nth (l, len_l-1) = "=" andalso
           nth (l, len_l-6) = "In" then
            SOME (take_between l 8 (len_l - 7))
        else NONE
    end;
*)

(* September 27, 2011: New machinery for interfacing with
   Mathematica more efficiently, based upon our own Mathematica
   REPL which adds carriage returns after input prompt.
   This makes it so that we need not do our own blocking via
   readStream.

   Our Mathematica REPL is as follows:

   While[True, NV = Input["In>\n"];
               Print[NV]
               If[NV == Quit,
                  Quit[]]]
 *)

fun mk_result_tokens () =
    case mk_is() of
        SOME is =>
        let val s = stream_strings_until_prompt is "InMT>" []
            val s' = String.concat s
            (* val _ = print ("Read: " ^ s' ^ "\n") *)
            val l = lex (explode s')
        in SOME l end
      | NONE => NONE;

(* Send a command string to MK and parse back the result.
   We use the m_fm parser, so this works for also QE results. *)

fun m_fm_of_mk_exec_str s =
    let val _ = mk_writeln s
    in
        case mk_result_tokens() of
            SOME l => SOME (parse_m_fm l)
          | NONE => NONE
    end;

(* Compute a discriminant of an MT polynomial w.r.t. a given variable,
   with the variable given as an MT Skolem constant. *)

fun discriminant p v =
    let val m_p = m_tm_to_str (m_tm_of_mt_tm p false)
        val m_v = m_tm_to_str (m_tm_of_mt_tm v false)
        val m_c = "FullForm[Discriminant[" ^ m_p ^ ", " ^ m_v ^ "]]"
    in
        case m_fm_of_mk_exec_str m_c of
            SOME (Tm m_p') => SOME (mt_tm_of_m_tm m_p')
          | SOME _ => raise MATHEMATICA_PARSING "Term expected"
          | NONE => NONE
    end;

(* Factor a MetiTarski polynomial, returning a factored MT polynomial  *)

fun factor p =
    let val m_p = m_tm_to_str (m_tm_of_mt_tm p false)
        val m_c = "FullForm[Factor[" ^ m_p ^ "]]"
    in
        case m_fm_of_mk_exec_str m_c of
            SOME (Tm m_p') => SOME (mt_tm_of_m_tm m_p')
          | SOME _ => raise MATHEMATICA_PARSING "Term expected"
          | NONE => NONE
    end;


(* Extract all atoms from a formula *)

local open Formula in
  fun atoms' a [] = a
    | atoms' a (Atom a' :: fms) = atoms' (a' :: a) fms
    | atoms' a (Not p :: fms) = atoms' a (p :: fms)
    | atoms' a (And (p,q) :: fms) = atoms' a (p :: q :: fms)
    | atoms' a (Or (p,q) :: fms) = atoms' a (p :: q :: fms)
    | atoms' a (Imp (p,q) :: fms) = atoms' a (p :: q :: fms)
    | atoms' a (Iff (p,q) :: fms) = atoms' a (p :: q :: fms)
    | atoms' a (Forall (_,p) :: fms) = atoms' a (p :: fms)
    | atoms' a (Exists (_,p) :: fms) = atoms' a (p :: fms);

  fun atoms fm = atoms' [] [fm]
end;


(* A private Mathematica-module version of the RealAlg type,
   used only for printing purposes. *)

type m_real_alg = Algebra.poly * Rat.rat * Rat.rat;

(* Convert, e.g.,

     [Plus [Int ~2, Power (Slot 1, 2)]]

   into

     -2 + x^2.

   * We let Slot[k] represent x_[k-1], i.e.,

     val p_x = [(Rat.one, [(0, 1)])] : poly;

 *)

local open Algebra Rat in

fun rat_of_m_numeric_tm q =
    case q of
        Int n => Rat.rat_of_intinf n
      | Rational (a,b) =>  Rat.rat_of_quotient (a,b)
      | _ => raise MATHEMATICA_PARSING "Bad root interval endpoint"

fun poly_pow (p, n) =
    if n < 0 then raise MATHEMATICA_PARSING "Pow with negative expt"
    else if n = 0 then p_one
    else p_mult(p, (poly_pow(p, n-1)))

fun poly_of_m_fun (m : m_tm) =
    case m of
        Int n => poly_of_rat (rat_of_intinf n)
      | Rational (a,b) => poly_of_rat (Rat.rat_of_quotient (a,b))
      | UnaryMinus p => p_neg(poly_of_m_fun p)
      | Plus ps =>
        let val m_ps = List.map poly_of_m_fun ps
        in
            List.foldr p_sum p_zero m_ps
        end
      | Times ps =>
        let val m_ps = List.map poly_of_m_fun ps
        in
            List.foldr p_mult p_one m_ps
        end
      | Power (p, n) =>
        let val m_p = poly_of_m_fun p
        in
            poly_pow (m_p, n)
        end
      | Slot n => [(Rat.one, [(n-1, 1)])] (* : poly *)
      | _ => raise MATHEMATICA_PARSING "Bad polynomial in Mathematica real_alg"

end;

(* Construct m_real_algs from a Mathematica representation *)
(* Example:

  let val tm =
    List
      [Function [Plus [Int ~2, Power (Slot 1, 2)]],
       List [Rational (~725, 512), Rational (~181, 128)]]
  in
   mra_of_tm tm
  end;

*)

fun mra_of_m_tm m =
    case m of
        List([(Function [f]),
              List([q1, q2])])
        => (poly_of_m_fun f,
            rat_of_m_numeric_tm q1,
            rat_of_m_numeric_tm q2)
      | _ => raise MATHEMATICA_PARSING "Bad Mathematica real_alg"

(* Example:

let val tm =
 List
    [List
      [Function [Plus [Int ~2, Power (Slot 1, 2)]],
       List [Rational (~725, 512), Rational (~181, 128)]],
     List
      [Function
        [Plus
          [Int ~1, Times [Int ~4, Slot 1], Times [Int 3, Power (Slot 1, 2)],
           Times [Int ~2, Int 1], Power (Slot 1, 4)]],
       List [Rational (~55, 256), Rational (~27, 128)]],
     List [Function [Plus [Int ~1, Slot 1]], List [Int 1, Int 1]],
     List
      [Function [Plus [Int ~2, Power (Slot 1, 2)]],
       List [Rational (181, 128), Rational (725, 512)]],
     List
      [Function [Plus [Int ~1, Times [Slot 1, Slot 1], Int 3]],
       List [Rational (113, 64), Rational (905, 512)]]]
  in
    mras_of_m_tm tm
 end;

*)

fun mras_of_m_tm (m : m_tm) =
    case m of
        List tms => map mra_of_m_tm tms
      | _ => raise MATHEMATICA_PARSING "Bad list of real_algs"

(* Isabelle/HOL style string representation *)

fun mra_toIsabelleString (r : m_real_alg) =
    case r of
        (p, l, u) => if l = u then ("Rat (" ^ (Rat.toString l) ^ ")")
                     else ("Arep [: " ^ (Algebra.univ_p_toString p) ^
                           " :] (" ^ (Rat.toString l) ^ ") (" ^
                           (Rat.toString u) ^ ")") ;

fun print_root_iso (rs : m_real_alg list) =
    (print "\n -- [Begin univariate CAD sampling]\n     ";
     print (String.concatWith ",\n     " (List.map mra_toIsabelleString rs));
     print "\n -- [End univariate CAD sampling]\n\n");

(* Isolate roots of list of polynomials and print them *)

fun iso_roots_and_print ps =
    let val m_ps = map (fn p => m_tm_to_str (m_tm_of_mt_tm p false)) ps
        val m_ps_str = "{" ^ (String.concatWith ", " m_ps) ^ "}"
        val m_c = "FullForm[isolateRoots[" ^ m_ps_str ^ "]]"
    in
        case m_fm_of_mk_exec_str m_c of
            SOME (Tm m_tm) =>
            let val roots = mras_of_m_tm m_tm
            in print_root_iso roots end
          | SOME _ => raise MATHEMATICA_PARSING "Term expected"
          | NONE => ()
    end;

(* Run Mathematica iso roots code on a top-level quantified formula *)

fun univ_m_root_iso (fm : Formula.formula) =
    let val _ = print("- Mathematica root_iso is working directly upon the input formula.\n")
        val fm_atoms = atoms fm
        val polys = List.map (fn (_, [x,y]) =>
                                 if x = Term.Rat Rat.zero then
                                     y
                                 else if y = Term.Rat Rat.zero then
                                     x
                                 else
                                     Term.Fn ("-", [x, y]))
                             fm_atoms
    in
        iso_roots_and_print polys
    end;


(* (* Given a list of MT polynomials PS and a Mathematica list term of *)
(*     isolated roots of the PS of the form: *)

(*      List[List[List[-3, 0], List[1, 5]], List[[1],[1,2]]], *)

(*    convert it into a list of real_algs of this form: *)

(*      [M_Root (PS[0]) [-3, 0], *)
(*       M_Root (PS[0]) [-1, 5]], *)

(*    etc. When a root/interval belongs to more than one P, we just *)
(*    select the first one. *) *)

(* fun roots_from_intervals ps m = *)
(*     let fun intvl_and_id a b = *)
(*             case a, b of *)
(*                 (List[u, l], List[id :: _]) => ([u, l], id) *)
(*               | (List[q], List[id :: _]) => ([q], id) *)
(*               | _ => raise MATHEMATICA_PARSING "intvl_and_id" *)
(*     in *)
(*         case ... *)

(* Isolate the real roots of a list of polynomials *)

(* fun isolate_real_roots ps = *)
(*     let val m_ps = map (fn p => m_tm_to_str (m_tm_of_mt_tm p false)) ps *)
(*         val m_ps = String.concatWith ", " m_ps *)
(*         val m_c = "FullForm[RootIntervals[{" ^ m_ps ^ "}]]" *)
(*     in *)
(*         case m_fm_of_mk_exec_str m_c of *)
(*             SOME (Tm m) => roots_from_intervals ps m *)
(*           | SOME _ => raise MATHEMATICA_PARSING "Improper root isolation result" *)
(*           | NONE  => NONE *)

(* Given an RCF *sentence*, construct a string representation suitable
   for Mathematica transmission.

   Nov 9th: Updated (Grant) to not print nested Ands and Ors.
*)

local open Formula in
fun mk_qf_fm_str_ fm exact_pi in_and in_or =
    let val m = (fn (x, y) =>
                    ((mt_tm_to_m_tm_str x exact_pi) ^ "," ^ (mt_tm_to_m_tm_str y exact_pi)))
        val n = (fn (x, y, i_a, i_o) =>
                    ((mk_qf_fm_str_ x exact_pi i_a i_o) ^ "," ^ (mk_qf_fm_str_ y exact_pi i_a i_o)))
    in
        case fm of
            False => "False"
          | True => "True"
          | Atom ("=", [x,y]) => "Equal[" ^ m(x,y) ^ "]"
          | Atom (">", [x,y]) => "Greater[" ^ m(x,y) ^ "]"
          | Atom (">=", [x,y]) => "GreaterEqual[" ^ m(x,y) ^ "]"
          | Atom ("<=", [x,y]) => "LessEqual[" ^ m(x,y) ^ "]"
          | Atom ("<", [x,y]) => "Less[" ^ m(x,y) ^ "]"
          | Not(Atom("=", [x,y])) => "Unequal[" ^ m(x,y) ^ "]"
          | Not(Atom(">", [x,y])) => "LessEqual[" ^ m(x,y) ^ "]"
          | Not(Atom(">=", [x,y])) => "Less[" ^ m(x,y) ^ "]"
          | Not(Atom("<=", [x,y])) => "Greater[" ^ m(x,y) ^ "]"
          | Not(Atom("<", [x,y])) => "GreaterEqual[" ^ m(x,y) ^ "]"
          | Not(p) => "Not[" ^ (mk_qf_fm_str_ p exact_pi false false) ^ "]"
          | And(p, q) => if in_and then n(p,q,true,false) else ("And[" ^ n(p,q,true,false) ^ "]")
          | Or(p, q) => if in_or then n(p,q,false,true) else ("Or[" ^ n(p,q,false,true) ^ "]")
          | Imp(p, q) => "Implies[" ^ n(p,q,false,false) ^ "]"
          | Iff(p, q) => "Equivalent[" ^ n(p,q,false,false) ^ "]"
          | _ => raise MATHEMATICA_PARSING "Cannot convert MetiTarski QF matrix to Mathematica syntax"
    end

fun mk_qf_fm_str fm exact_pi = mk_qf_fm_str_ fm exact_pi false

(* A variant of the above _fm_str function producing a more compact
   string.

   8-Nov-2012 (grant): Updated to not print unnecessary parentheses.
   9-Nov-2012 (grant): Updated to print And[a,b,c] instead of And[And[a,b],c],
                                         Or[a,b,c[ instead of Or[Or[a,b],c], etc.

*)

fun mk_qf_fm_str_compact_ fm exact_pi in_and in_or =
    let fun m x = mt_tm_to_m_tm_str_compact x exact_pi
        val n = (fn (x, y, i_a, i_o) =>
                    ((mk_qf_fm_str_compact_ x exact_pi i_a i_o)
                     ^ "," ^ (mk_qf_fm_str_compact_ y exact_pi i_a i_o)))
    in
        case fm of
            False => "False"
          | True => "True"
          | Atom ("=", [x,y]) => m x ^ "==" ^ m y
          | Atom (">", [x,y]) => m x ^ ">" ^ m y
          | Atom (">=", [x,y]) => m x ^ ">=" ^ m y
          | Atom ("<=", [x,y]) => m x ^ "<=" ^ m y
          | Atom ("<", [x,y]) => m x ^ "<" ^ m y
          | Not(Atom("=", [x,y])) => m x ^ "!=" ^ m y
          | Not(Atom(">", [x,y])) => m x ^ "<=" ^ m y
          | Not(Atom(">=", [x,y])) => m x ^ "<" ^ m y
          | Not(Atom("<=", [x,y])) => m x ^ ">" ^ m y
          | Not(Atom("<", [x,y])) => m x ^ ">=" ^ m y
          | Not(p) => "Not[" ^ (mk_qf_fm_str_compact_ p exact_pi false false) ^ "]"
          | And(p, q) => if in_and then n(p,q,true,false) else ("And[" ^ n(p,q,true,false) ^ "]")
          | Or(p, q) => if in_or then n(p,q,false,true) else ("Or[" ^ n(p,q,false,true) ^ "]")
          | Imp(p, q) => "Implies[" ^ n(p,q,false,false) ^ "]"
          | Iff(p, q) => "Equivalent[" ^ n(p,q,false,false) ^ "]"
          | _ => raise MATHEMATICA_PARSING "Cannot convert MetiTarski QF matrix to Mathematica syntax"
    end

fun mk_qf_fm_str_compact fm exact_pi = mk_qf_fm_str_compact_ fm exact_pi false false;

end;

(* Convert a MetiTarski RCF sentence into a Mathematica RCF sentence.
   25-Feb-2012: Adjusted to use the new _compact version of the
   qf_fm_str function, mk_qf_fm_str_compact.*)

fun mk_s_str xvars uvars fm exact_pi =
    let val vs = if exact_pi then (List.filter (fn x => not(x = "pi")) xvars)
                 else xvars
(*	val _ = print ("\n exact_pi=" ^ Bool.toString(exact_pi) ^
                       " vs=" ^ (String.concatWith "," vs) ^ ".\n") *)
        val command_str = String.concat ["Exists[{",(String.concatWith "," xvars),"}, ","ForAll[{", (String.concatWith "," uvars), "}, ",
                       (mk_qf_fm_str_compact fm exact_pi), "]]"]
    (* debug added by JPB *)
    (*val _ = print ("\ncommand_str : \n" ^ command_str ^ "\n") *)
    (* end of debug code *)
    in
        command_str
    end;

(* Convert a MetiTarski RCF sentence into a Mathematica CAD call *)

fun mk_cad_str xvars uvars fm exact_pi =
    String.concat ["CylindricalDecomposition[" ^
                   (mk_s_str xvars uvars fm exact_pi) ^
                   ", " ^ "{" ^ (String.concatWith "," xvars) ^ "}]"];

(* Convert a MetiTarski RCF sentence into a Mathematica RESOLVE call *)

fun mk_resolve_str xvars uvars fm exact_pi =
    String.concat ["Resolve[" ^ (mk_s_str xvars uvars fm exact_pi) ^ ", Reals]"];

(* Code to generate trace output in a separate file: taken from Qepcad.sml *)

val qe_trace = ref (NONE : TextIO.outstream option);
val write_trace_file = true;

fun open_qe_trace() = case !qe_trace of
    SOME os => os
  | NONE =>
      let val {base,...} = OS.Path.splitBaseExt
                              (List.last (CommandLine.arguments ()) handle Empty => "XXX")
          val os = TextIO.openOut(base ^ ".trace");
      in  qe_trace := SOME os; os
      end;

(* Get total CPU time from Mathematica process *)

fun mk_cpu_time() =
    case mk_is() of
        SOME _ => let val _ = mk_writeln("FullForm[Chop[TimeUsed[] - InitTime, 0.0001]]")
                      val t_toks = mk_result_tokens()
                  (* t_toks of the form SOME ["NNNN", ".", "NNNNN", "`"] *)
                  in
                      case t_toks of
                          SOME ["0"] => Time.fromReal 0.0
                        | SOME [l, ".", r, "`"] =>
                          (case Real.fromString (l ^ "." ^ r) of
                               SOME r => Time.fromReal r
                             | NONE => raise MATHEMATICA_PARSING ("Cannot parse CPU time used:"))
                        | SOME [l, ".", r] =>
                          (case Real.fromString (l ^ "." ^ r) of
                               SOME r => Time.fromReal r
                             | NONE => raise MATHEMATICA_PARSING ("Cannot parse CPU time used:"))
                        | _ => raise MATHEMATICA_PARSING "Cannot parse CPU time used:"
                  end
      | NONE => raise MATHEMATICA_PARSING "MathKernel process unexpectedly closed";

(* Given an RCF *sentence*, run Mathematica's RESOLVE function upon
   it, returning true iff Mathematica says the sentence is FALSE. *)

fun mk_s_resolve _ _ Formula.False _ = true
  | mk_s_resolve _ _ Formula.True _ = false
  | mk_s_resolve xvars uvars fm exact_pi =
    let val result = ref false
        val core_str = (mk_resolve_str xvars uvars fm exact_pi)
        val _ = mk_open()
        (* val _ = print ("\n\n*****\n\nSending to Mathematica: \n"
                          ^ (mk_resolve_str xvars [] fm exact_pi) ^ "\n*****\n\n.") *)
    in
        ((case m_fm_of_mk_exec_str
                   (if Time.>(!mk_decision_time_limit, Time.zeroTime) then
                        ("TimeConstrained[FullForm[" ^ core_str ^ "],"
                         ^ (Time.toString (!mk_decision_time_limit)) ^ "]")
                    else ("FullForm[" ^ core_str ^ "]"))
           of
              SOME False => result := true
            | SOME True => result := false
            | _ => result := false);
          (* if write_trace_file then
                 TextIO.output(open_qe_trace(),
                               (core_str ^ "\nREFUTED? = " ^ Bool.toString(!result) ^ "\n"))
             else (); *)
         !result)
    end

(* Given an RCF *sentence*, run Mathematica's RESOLVE function *with a
   given time-limit* upon it, returning true iff Mathematica says the
   sentence is FALSE. *)

fun mk_unsat_timelimit _ Formula.False _ = true
  | mk_unsat_timelimit _ Formula.True _ = false
  | mk_unsat_timelimit [] _ _ = false (* No variables *)
  | mk_unsat_timelimit xvars fm timelimit =
    let val result = ref false
        val core_str = (mk_resolve_str xvars [] fm false)
        val _ = mk_open()
        (* val _ = print ("\n\n*****\n\nSending to Mathematica: \n"
                          ^ (mk_resolve_str xvars [] fm exact_pi) ^ "\n*****\n\n.") *)
    in
        ((case m_fm_of_mk_exec_str
                   (if Time.>(!mk_decision_time_limit, Time.zeroTime) then
                        ("TimeConstrained[FullForm[" ^ core_str ^ "],"
                         ^ (Int.toString timelimit) ^ "]")
                    else ("FullForm[" ^ core_str ^ "]"))
           of
              SOME False => result := true
            | SOME True => result := false
            | _ => result := false);
          (* if write_trace_file then
                 TextIO.output(open_qe_trace(),
                               (core_str ^ "\nREFUTED? = " ^ Bool.toString(!result) ^ "\n"))
             else (); *)
         !result)
    end;

(* A version of MK_S_RESOLVE for univ_relax / SAT filtration.
   This version returns TRUE iff Mathematica shows the formula to be SAT. *)

fun mk_s_resolve_sat Formula.False = false
  | mk_s_resolve_sat Formula.True = true
  | mk_s_resolve_sat fm =
    let val result = ref false
        val core_str = (mk_resolve_str ["x"] [] fm false)
        val _ = mk_open()
    in
        ((case m_fm_of_mk_exec_str
                   (if Time.>(!mk_decision_time_limit, Time.zeroTime) then
                        ("TimeConstrained[FullForm[" ^ core_str ^ "],"
                         ^ (Time.toString (!mk_decision_time_limit)) ^ "]")
                    else ("FullForm[" ^ core_str ^ "]"))
           of
              SOME False => result := false
            | SOME True => result := true
            | _ => result := false);
         !result)
    end;

(* A version of MK_S_RESOLVE for performing machine learning
   experiments. *)

fun ignore_until_prompt () =
    case mk_is() of
        SOME instr => let val _ = stream_strings_until_prompt instr "InMT>" [] in () end
      | NONE => ();

fun mk_reset_time () =
    mk_writeln ("InitTime = TimeUsed[]");

(* Extract all polynomials from a formula and compute some stats *)

local open Algebra MTAlgebra in

fun fm_stats (fm : Formula.formula) =
    let val vh = mk_vv_ht 10
        val ps = polys_of_fm (vh, fm)
        val max_tdeg =
            foldl Int.max 0 (map (fn (p : poly) =>
                                     case p of
                                         m :: ps => m_deg m
                                       | _ => 0)
                                 ps)
        val num_ms =
            foldl (op +) 0 (map List.length ps)
    in
        (max_tdeg, num_ms)
    end;

end;

fun decision_to_str (Sat _) = "Sat"
  | decision_to_str Unsat = "Unsat"
  | decision_to_str Unknown = "Unknown";

(* Convert a top-level TPTP conjecture (list of clauses) to
   Mathematica formula suitable for Reduce[]. *)

fun conj_to_fm (c::[]) = LiteralSet.disjoin c
  | conj_to_fm [] = Formula.True
  | conj_to_fm (c::cs) = Formula.And ((LiteralSet.disjoin c),
                                      conj_to_fm cs);
fun st_to_m_str f exact_pi =
    case f of
        Term.Fn ("sin", [x]) => "Sin[" ^ (st_to_m_str x exact_pi) ^ "]"
      | Term.Fn ("sinh", [x]) => "Sinh[" ^ (st_to_m_str x exact_pi) ^ "]"
      | Term.Fn ("cos", [x]) => "Cos[" ^ (st_to_m_str x exact_pi) ^ "]"
      | Term.Fn ("sinh", [x]) => "Sinh[" ^ (st_to_m_str x exact_pi) ^ "]"
      | Term.Fn ("cosh", [x]) => "Cosh[" ^ (st_to_m_str x exact_pi) ^ "]"
      | Term.Fn ("abs", [x]) => "Abs[" ^ (st_to_m_str x exact_pi) ^ "]"
      | Term.Fn ("ln", [x]) => "Log[" ^ (st_to_m_str x exact_pi) ^ "]"
      | Term.Fn ("tan", [x]) => "Tan[" ^ (st_to_m_str x exact_pi) ^ "]"
      | Term.Fn ("sqrt", [x]) => "Sqrt[" ^ (st_to_m_str x exact_pi) ^ "]"
      | Term.Fn ("cbrt", [x]) => "CubeRoot[" ^ (st_to_m_str x exact_pi) ^ "]"
      | Term.Fn ("arctan", [x]) => "ArcTan[" ^ (st_to_m_str x exact_pi) ^ "]"
      | Term.Fn ("arcsin", [x]) => "ArcSin[" ^ (st_to_m_str x exact_pi) ^ "]"
      | Term.Fn ("arccos", [x]) => "ArcCos[" ^ (st_to_m_str x exact_pi) ^ "]"
      | Term.Fn ("exp", [x]) => "Exp[" ^ (st_to_m_str x exact_pi) ^ "]"
      | Term.Fn ("+", [x,y]) => "(" ^ (st_to_m_str x exact_pi) ^ " + " ^ (st_to_m_str y exact_pi) ^ ")"
      | Term.Fn ("-", [x,y]) => "(" ^ (st_to_m_str x exact_pi) ^ " - " ^ (st_to_m_str y exact_pi) ^ ")"
      | Term.Fn ("-", [x]) => "(-" ^ (st_to_m_str x exact_pi) ^ ")"
      | Term.Fn ("*", [x,y]) => "(" ^ (st_to_m_str x exact_pi) ^ " * " ^ (st_to_m_str y exact_pi) ^ ")"
      | Term.Fn ("/", [x,y]) => "(" ^ (st_to_m_str x exact_pi) ^ " / " ^ (st_to_m_str y exact_pi) ^ ")"
      | Term.Fn ("^", [x,n]) => "(" ^ (st_to_m_str x exact_pi) ^ ")^" ^ (st_to_m_str n exact_pi) ^ " "
      | Term.Rat x => Rat.toString x
      | Term.Fn ("pi", []) => if exact_pi then "Pi" else "pi"
      | Term.Fn (v, []) => v
      | Term.Var v => Common.varname v
      | _ => raise Useful.die ("Mathematica - Do not understand: " ^ (Term.toString f));

fun sf_to_m_str f exact_pi =
    case f of
        Formula.True => "True"
      | Formula.False => "False"
      | Formula.And (p, q) =>
        (sf_to_m_str p exact_pi) ^ " && " ^ (sf_to_m_str q exact_pi)
      | Formula.Or (p, q) =>
        "(" ^ (sf_to_m_str p exact_pi) ^ " || " ^ (sf_to_m_str q exact_pi) ^ ")"
      | Formula.Atom ("=", [x,y]) => "(" ^ (st_to_m_str x exact_pi) ^ " == " ^ (st_to_m_str y exact_pi) ^ ")"
      | Formula.Atom (">", [x,y]) => "(" ^ (st_to_m_str x exact_pi) ^ " > " ^ (st_to_m_str y exact_pi) ^ ")"
      | Formula.Atom (">=", [x,y]) => "(" ^ (st_to_m_str x exact_pi) ^ " >= " ^ (st_to_m_str y exact_pi) ^ ")"
      | Formula.Atom ("<=", [x,y]) => "(" ^ (st_to_m_str x exact_pi) ^ " <= " ^ (st_to_m_str y exact_pi) ^ ")"
      | Formula.Atom ("<", [x,y]) => "(" ^ (st_to_m_str x exact_pi) ^ " < " ^ (st_to_m_str y exact_pi) ^ ")"
      | Formula.Not (Formula.Atom ("<=", [x,y])) =>
        "(" ^ (st_to_m_str x exact_pi) ^ " > " ^ (st_to_m_str y exact_pi) ^ ")"
      | Formula.Not a => "!(" ^ (sf_to_m_str a exact_pi) ^ ")"
      | _ => raise Useful.die ("Mathematica - Do not understand: " ^ (Formula.toString f));

fun mk_sf_reduce_str xvars fm exact_pi =
    String.concat ["Reduce[Exists[{", (String.concatWith "," xvars), "}, ",
                   (sf_to_m_str fm exact_pi), "]]"];

(* Given an RCF+special function *sentence*, run Mathematica's REDUCE
   function upon it, returning true iff Mathematica says the sentence
   is FALSE.  We use this for tautology checking.  *)

fun sf_unsat _ Formula.False _ _ = Common.Unsat
  | sf_unsat _ Formula.True _ _ = Common.Sat NONE
  | sf_unsat [] _ _ _ = Common.Unknown (* No variables *)
  | sf_unsat xvars fm exact_pi time_limit =
    let val _ = mk_open()
    (* val _ = print ("\n\n*****\n\nSending to Mathematica for sf_unsat checking: \n"
                      ^ (mk_sf_reduce_str xvars fm false) ^ "\n*****\n\n.")  *)
    in
        case m_fm_of_mk_exec_str
                 (if Time.>(!mk_decision_time_limit, Time.zeroTime)
                  then ("TimeConstrained[FullForm[" ^
                        (mk_sf_reduce_str xvars fm false) ^ "],"
                        ^ (Time.toString time_limit) ^ "]")
                  else ("FullForm[" ^
                        (mk_sf_reduce_str xvars fm false) ^ "]"))
         of
            SOME False => ( (* print ("\n Mathematica refuted SF formula! \n"); *)
                          Common.Unsat)
          | SOME True => Common.Sat NONE
          | _ => Common.Unknown
    end;

end;




(* An example:

    val p = mt_tm_of_m_tm (m_tm_of_str "Plus[Times[a, Power[x, 2]], Times[b, x], c])");

    // p = ax^2 + bx + c

    val p' = discriminant p (Term.Fn("x" ,[]));

    // p' = SOME b^2 - 4 a c *)


(* An example:

          3       3  2          2    3
       -(b  c)   a  c    3 a b c    c
       ------- + ----- + -------- + --
          2        2        2       2

   (1) We begin with a string given to us by Mathematica's FullForm[%]
        (recall that FullForm inserts ">" symbols at the beginning of newlines):

    val x = ">   Plus[Times[Rational[-1, 2], Power[b, 3], c], >    Times[Rational[1, 2], Power[a, 3], Power[c, 2]], >    Times[Rational[3, 2], a, b, Power[c, 2]], >    Times[Rational[1, 2], Power[c, 3]]]";

   (2) We lex x:

    val lex'd_x = lex (explode x);

   (3) We parse x into a Mathematica parse-tree:

    val parsed_x = parse_m_tm lex'd_x;

   (4) We turn parsed_x into a MetiTarski term:

    val x_as_mt_tm = mt_tm_of_m_tm parsed_x;

   (5) We turn x_as_mt_term back into a Mathematica term:

    val x_as_m_tm = m_tm_of_mt_tm x_as_mt_tm;

   (6) We print x_as_m_tm to a string:

    val s = m_tm_to_string x_as_m_tm;

    This gives us:
      "Plus[Times[Rational[-1, 2], Times[Power[b, 3], c]], Plus[Times[Rational[1, 2], Times[Power[a, 3], Power[c, 2]]], Plus[Times[Rational[3, 2], Times[a, Times[b, Power[c, 2]]]], Times[Rational[1, 2], Power[c, 3]]]]]"

   (7) We send this to Mathematica, asking it to pretty print it:

           3       3  2          2    3
        -(b  c)   a  c    3 a b c    c
       ------- + ----- + -------- + --
           2        2        2       2

    Viola!  *)
