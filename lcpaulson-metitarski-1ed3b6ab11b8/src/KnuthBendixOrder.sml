(* ========================================================================= *)
(* KNUTH-BENDIX TERM ORDERING CONSTRAINTS                                    *)
(* Copyright (c) 2001 Joe Hurd, distributed under the MIT license            *)

(* ========================================================================= *)

structure KnuthBendixOrder :> KnuthBendixOrder =
struct

open Useful;

(* ------------------------------------------------------------------------- *)
(* Helper functions.                                                         *)
(* ------------------------------------------------------------------------- *)

fun notEqualTerm (x,y) = not (Term.equal x y);

fun firstNotEqualTerm f l =
    case List.find notEqualTerm l of
      SOME (x,y) => f x y
    | NONE => SOME EQUAL;

(* ------------------------------------------------------------------------- *)
(* The weight of all constants must be at least 1, and there must be at most *)
(* one unary function with weight 0.                                         *)
(* ------------------------------------------------------------------------- *)

(*LCP: Many extensions: the notion of subterm coefficient*)
type kbo =
     {weight        : string -> int,
      subterm_coeff : string -> int,
      precedence : Term.function * Term.function -> order};

(* Default weight = uniform *)

val uniformWeight : string -> int = K 1;

(* function to recognize sko variables *)
fun is_sko s = (String.isPrefix "sko" s);

(*LCP: Metis-RCF requires high weights for some functions.
  No benefits seem to accrue from giving weights to lgen or <=. *)
val non_uniformWeight_map =
  StringMap.fromList
   [("ln", 2500),
    ("log", 3000),
    ("exp", 2500),
    ("pow", 5500),
    ("sin", 3500),
    ("cos", 3500),
    ("tan", 3500),
    ("sinh", 2500),
    ("cosh", 2500),
    ("tanh", 2500),
    ("arcsin", 5000),
    ("arccos", 5000),
    ("arctan", 2500),
    ("sqrt", 2500),
    ("cbrt", 2500),
    ("nthrt", 2500),
    ("abs", 20000),  (*gives markedly better results for slowest abs problems*)
    ("floor", 2500),
    (* --------- Bessel Functions of First Kind and integer order --------- *)
    ("j0", 3500),
    ("j1", 3500),
    ("j2", 3500),
    ("j3", 3500),
    ("j4", 3500),
    ("j5", 3500),
    ("j6", 3500),
    ("j7", 3500),
    ("j8", 3500),
    ("j9", 3500),
    ("j10", 3500),
    (* --------------------------------------------------------------------- *)
    ("/", 175),
    ("*",5),
    ("+",5),
    ("-",5),
    ("min",5),
    ("max",5),
    ("^",5),
    (* need to account for top level predicates as well *)
    ("<=",5),
    ("lgen",5),
    ("interval",5)];

fun non_uniformWeight s =
 (* if is_sko s then 5 else *)
  case StringMap.peek non_uniformWeight_map s of
      SOME n => n
    | NONE   => 5;


(*LCP: Extended KBO has a subterm coefficient function. From
  M. Ludwig and U. Waldmann. An extension of the Knuth-Bendix ordering with
  LPO-like properties. In N. Dershowitz and A. Voronkov, editors, LPAR 2007,
  Springer LNCS 4790, pages 348Ð362.*)
val subterm_coeff_map =
  StringMap.fromList
   [("ln", 100),
    ("log", 100),  (*Needed to match that of ln.*)
    ("exp", 105),
    ("pow", 10000),
    ("sin", 100),
    ("cos", 100),
    ("tan", 100),
    ("arcsin", 200),  (*The larger number allows for the coefficient of sqrt.*)
    ("arccos", 200),
    ("arctan", 100),
    ("sinh", 100),
    ("cosh", 100),
    ("tanh", 100),
    ("sqrt", 100),
    ("cbrt", 100),
    ("nthrt", 100),
    (* -------- Bessel Functions of First Kind and integer order ------- *)
    ("j0", 100),
    ("j1", 100),
    ("j2", 100),
    ("j3", 100),
    ("j4", 100),
    ("j5", 100),
    ("j6", 100),
    ("j7", 100),
    ("j8", 100),
    ("j9", 100),
    ("j10", 100),
    (* ----------------------------------------------------------------- *)
    ("/",1),
    ("*",1),
    ("+",1),
    ("-",1),
    ("abs",1),
    ("floor",1),
    ("min",1),
    ("max",1),
    ("^",1),
    (* need to account for top level predicates as well *)
    ("<=",1),
    ("lgen",1),
    ("interval",1)];

fun subterm_coeff s =
(*  if is_sko s then 1 else *)
  case StringMap.peek subterm_coeff_map s of
      SOME n => n
    | NONE => ((* print s; *)(* 1 changed to 100 then 1000 for user functions *)1000);

(* Default precedence = by arity *)

val arityPrecedence : Term.function * Term.function -> order =
    fn ((f1,n1),(f2,n2)) =>
       case Int.compare (n1,n2) of
         LESS => LESS
       | EQUAL => Name.compare (f1,f2)
       | GREATER => GREATER;

(* The default order *)

(*LCP: Metis-RCF requires high weights for some functions.*)
val default : kbo = {weight = non_uniformWeight,
                     subterm_coeff = subterm_coeff,
                     precedence = arityPrecedence};

(* ------------------------------------------------------------------------- *)
(* Term weight-1 represented as a linear function of the weight-1 of the     *)
(* variables in the term (plus a constant).                                  *)
(*                                                                           *)
(* Note that the conditions on weight functions ensure that all weights are  *)
(* at least 1, so all weight-1s are at least 0.                              *)
(* ------------------------------------------------------------------------- *)

fun addVars (Term.Var v, s) = NameSet.add s v
  | addVars (Term.Rat _, s) = s
  | addVars (Term.Fn (_,ts), w) = foldl addVars w ts;

fun vars t = addVars (t, NameSet.empty);

(* ------------------------------------------------------------------------- *)
(* The Knuth-Bendix term order.                                              *)
(* ------------------------------------------------------------------------- *)

fun compare {weight,subterm_coeff,precedence} =
    let

      fun addWt (Term.Var _, w) = w+1
        | addWt (Term.Rat _, w) = w+1
        | addWt (Term.Fn (f,[]), w) = w + 5 (* use lower default for constants *)
        | addWt (Term.Fn (f,ts), w) = w + weight f + (subterm_coeff f * foldl addWt 0 ts)

      fun wt t = addWt (t,0)

      fun coeffsum pv t =
        let fun addCoeffs (Term.Var v, w) = if pv v then w+1 else w
              | addCoeffs (Term.Rat _, w) = w
              | addCoeffs (Term.Fn (f,ts), w) = w + (subterm_coeff f * foldl addCoeffs 0 ts)
        in  addCoeffs (t,0)  end

      fun vars_less (tm1, vars1) (tm2,vars2) =
	    NameSet.null vars1  orelse  (*purely for speed: worth 5-10% overall*)
	    (NameSet.subset vars1 vars2 andalso
	     coeffsum (K true) tm1 <= coeffsum (fn v => NameSet.member v vars1) tm2)

      fun weightCmp tm1 tm2 =
          let
            fun precedenceCmp (Term.Fn (f1,a1)) (Term.Fn (f2,a2)) =
		 (case precedence ((f1, length a1), (f2, length a2)) of
		    LESS => if vars_less (tm1, vars tm1) (tm2, vars tm2)
                            then SOME LESS else NONE
		  | EQUAL => firstNotEqualTerm weightCmp (zip a1 a2)
		  | GREATER => if vars_less (tm2, vars tm2) (tm1, vars tm1)
                               then SOME GREATER else NONE)
	      | precedenceCmp (Term.Rat r1) (Term.Rat r2) = SOME (Rat.compare (r1,r2))
	      | precedenceCmp (Term.Rat _) (Term.Fn _) = SOME LESS
	      | precedenceCmp (Term.Fn _) (Term.Rat _) = SOME GREATER
	      | precedenceCmp _ _ = NONE
          in
            case Int.compare (wt tm1, wt tm2) of
                LESS =>
                    if vars_less (tm1, vars tm1) (tm2, vars tm2)
                    then SOME LESS else NONE
              | EQUAL => precedenceCmp tm1 tm2
              | GREATER =>
                    if vars_less (tm2, vars tm2) (tm1, vars tm1)
                    then SOME GREATER else NONE
          end

    in
      fn (tm1,tm2) => weightCmp tm1 tm2
    end;

(*MetisTrace7
val compare = fn kbo => fn (tm1,tm2) =>
    let
      val () = Print.trace Term.pp "KnuthBendixOrder.compare: tm1" tm1
      val () = Print.trace Term.pp "KnuthBendixOrder.compare: tm2" tm2
      val result = compare kbo (tm1,tm2)
      val () =
          case result of
            NONE => trace "KnuthBendixOrder.compare: result = Incomparable\n"
          | SOME x =>
            Print.trace Print.ppOrder "KnuthBendixOrder.compare: result" x
    in
      result
    end;
*)

end
