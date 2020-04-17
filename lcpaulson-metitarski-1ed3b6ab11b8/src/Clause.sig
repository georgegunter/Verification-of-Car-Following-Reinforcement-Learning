(* ========================================================================= *)
(* CLAUSE = ID + THEOREM                                                     *)
(* Copyright (c) 2001 Joe Hurd, distributed under the MIT license            *)

(* ========================================================================= *)
(* Extra function subsumesAtSplitLevel added by JPB 31/1/11                  *)
(* ========================================================================= *)

signature Clause =
sig

(* ------------------------------------------------------------------------- *)
(* A type of clause.                                                         *)
(* ------------------------------------------------------------------------- *)

datatype literalOrder =
    NoLiteralOrder
  | UnsignedLiteralOrder
  | PositiveLiteralOrder

type parameters =
     {ordering : KnuthBendixOrder.kbo,
      orderLiterals : literalOrder,
      orderTerms : bool}

type clauseId = int

type clauseInfo = {parameters : parameters, id : clauseId, thm : Thm.thm}

type clause


val useSOS : bool ref  (* Determines whether or not Set Of Support constraints are applied *)

val useParamodulation : bool ref (* Determines if full paramodulation, rather than demodulation is used *)

(* ------------------------------------------------------------------------- *)
(* Basic operations.                                                         *)
(* ------------------------------------------------------------------------- *)

val inSOS : clause -> bool

val default : parameters

val newId : unit -> clauseId

val mk : clauseInfo -> clause

val dest : clause -> clauseInfo

val id : clause -> clauseId

val thm : clause -> Thm.thm

val equalThms : clause -> clause -> bool

val literals : clause -> Thm.clause

val isGround : clause -> bool

val isTautology : clause -> bool

val isContradiction : clause -> bool

val clauseDistance : clause -> Thm.clauseDistance

val setClauseDistance : Thm.clauseDistance -> clause -> clause

val setClauseListDistance : Thm.clauseDistance -> clause list -> clause list

val clauseLabel : clause -> Thm.clauseLabel

val clauseLabelLength : clause -> int

val updateLabel : clause -> Thm.clauseLabel -> clause

val getLevel : clause -> int

val addLevelToLabel : int -> clause -> clause

val labelsDifferent : clause -> clause -> bool

val rightCaseSplit : clause -> Thm.thm -> Thm.thm -> clause

(* ------------------------------------------------------------------------- *)
(* The term ordering is used to cut down inferences.                         *)
(* ------------------------------------------------------------------------- *)

val largestLiterals : clause -> LiteralSet.set

val largestEquations :
    clause -> (Literal.literal * Rewrite.orient * Term.term) list

val largestSubterms :
    clause -> (Literal.literal * Term.path * Term.term) list

val allSubterms : clause -> (Literal.literal * Term.path * Term.term) list

(* ------------------------------------------------------------------------- *)
(* Subsumption.                                                              *)
(* ------------------------------------------------------------------------- *)

val subsumes : clause Subsume.subsume -> clause -> (bool * clause Subsume.subsume)

(* ------------------------------------------------------------------------- *)
(* Simplifying rules: these preserve the clause id.                          *)
(* ------------------------------------------------------------------------- *)

val freshVars : clause -> clause

val simplify : clause -> clause option

val reduce : Units.units -> clause -> clause

val rewrite : Rewrite.rewrite -> clause -> clause

(* ------------------------------------------------------------------------- *)
(* Inference rules: these generate new clause ids.                           *)
(* ------------------------------------------------------------------------- *)

val arith : clause -> clause

val factor : clause -> clause list

val resolve : clause * Literal.literal -> clause * Literal.literal -> clause

val paramodulate :
    clause * Literal.literal * Rewrite.orient * Term.term ->
    clause * Literal.literal * Term.path * Term.term -> clause

val negateClauseIfGround : clause -> Thm.thm -> (clause list) option


(* ------------------------------------------------------------------------- *)
(* Pretty printing.                                                          *)
(* ------------------------------------------------------------------------- *)

val showId : bool ref

val pp : clause Print.pp

val toString : clause -> string

end
