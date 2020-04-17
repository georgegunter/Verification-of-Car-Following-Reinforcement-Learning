(* ======================================================================== *)
(* Some common values useful for RCF related things.                        *)
(*                                                                          *)
(* by G.O.Passmore, Cambridge Computer Laboratory and LFCS, Edinburgh, 2012 *)
(* Contact: (e) grant.passmore@cl.cam.ac.uk   (w) www.cl.cam.ac.uk/~gp351/. *)
(* ======================================================================== *)

structure Common : Common =
struct

(* Signal: subprocess cpu time limit exceeded *)

val sigxcpu = Posix.Signal.fromWord (SysWord.fromInt 24);

val no_underscores = String.translate (fn c => if c = #"_" then "" else str c);

fun varname x = "V" ^ no_underscores (Name.toString x);

(* ------------------------------------------------------------------------- *)
(* Variable list.                                                            *)
(* ------------------------------------------------------------------------- *)

fun string_tuple [] = "()"
  | string_tuple ss = "(" ^ String.concatWith "," ss ^ ")";

(* Model datatype.  Currently models may be:
    - maps of variable strings to floats,
    - maps of variable strings to exact rationals. *)

datatype mt = Real_Model of (string * real) list
	    | Rat_Model of (string * Rat.rat) list;

datatype tv = Sat of mt option | Unsat | Unknown;

(* Exception for judgment *)

exception JudgmentReached of tv;

(* Does a character belong to a certain lexical class? *)

fun matches class c =
    List.exists (fn x => x = c) (explode class);

(* Some basic lexical classes: Note that '>' is a special white-space
    char for Mathematica's FullForm output mode. *)

val white_space = matches " \t\n\r>";
val num = matches "0123456789.";
val alpha_num =
    matches "abcdefghijklmnopqrstuvwxyz_ABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789";

(* Given a list of characters S, snag the longest leading subsequence
   S' of S of a given lex class, returning a pair : string * char list
   (str(S'), rest), s.t. S' @ String.implode(rest) = S. *)

fun lex_snag p cl =
    case cl of
	c :: cs => if p c then
		       let val (s', rest) = lex_snag p cs in
			   (Char.toString(c) ^ s', rest)
		       end
		   else ("", cl)
      | _ => ("", cl);

(* Lex: Map a list of chars into a list of token strings *)

fun lex cl =
    let val (_, cl') = lex_snag white_space cl in
	case cl' of
	    c :: cs => let val p = if alpha_num c then alpha_num
				   else (fn x => false) in
			   let val (tok_str, rest) = lex_snag p cs in
			       (Char.toString(c) ^ tok_str) :: lex rest
			   end
		       end
	  | _ => []
    end;


(* Convert a floating point number to an exact rational.  We use the
   decimal representation provided by the Real structure as a basis
   for this conversion (does this result in an efficiency penalty?).
   The auxiliary function make_numerator computes the numerator of our
   rational representation. *)

fun make_numerator digits =
    let open IntInf
        fun make_numerator' digits pow_of_ten result =
	    case digits of
		[] => result
	      | (x :: xs) =>
		make_numerator' xs (pow_of_ten * 10)
		                (result + (Int.toLarge x * pow_of_ten))
    in make_numerator' (List.rev digits) 1 0 end;

fun rat_of_float r =
    let val {exp, sign, class, digits} = Real.toDecimal r
	fun int_pow x y =
	    case (x,y) of (_, 0) => 1
			| (0, _) => 0
			| (a, 1) => a
			| (a, b) =>
			  if b > 1 then a * (int_pow a (b-1))
			  else raise Useful.Error "rat_of_float/int_pow: negative integer exponent"
	val num = make_numerator digits
	val d =  (List.length digits) - exp
	val num' = if d<0 then num * int_pow 10 (~d)
		   else num
	val den = if d<0 then 1
		  else int_pow 10 ((List.length digits) - exp)
    in if sign then Rat.neg(Rat.rat_of_quotient (num', den)) else
       Rat.rat_of_quotient (num', den) end;


end;
