(* ========================================================================= *)
(* A LOGICAL KERNEL FOR FIRST ORDER CLAUSAL THEOREMS                         *)
(* Copyright (c) 2001 Joe Hurd, distributed under the MIT license            *)

(* ========================================================================= *)
(* Added functions for use with clause labels JPB *)

signature Thm =
sig

(* ------------------------------------------------------------------------- *)
(* An abstract type of first order logic theorems.                           *)
(* ------------------------------------------------------------------------- *)

type thm

(* ------------------------------------------------------------------------- *)
(* Theorem destructors.                                                      *)
(* ------------------------------------------------------------------------- *)

type clause = LiteralSet.set

type SOS = bool

type clauseDistance = real

type clauseLabel = int list

datatype inferenceType =
    Axiom
  | Assume
  | Subst
  | Factor
  | Resolve
  | Refl
  | Equality
  | Arith
  | Decision
  | Split
  | Cases
  | CaseSplit (* JPB *)

type inference = inferenceType * thm list

val filename : string ref (* used in Error reports *)

val inSOS : thm -> bool

val setSOS : thm -> thm

val clearSOS : thm -> thm

val isDecision : thm -> bool

val clauseDistance : thm -> clauseDistance

val setClauseDistance : clauseDistance -> thm -> thm

val clauseLabel : thm -> clauseLabel

val clause : thm -> clause

val inference : thm -> inference

val parents : thm -> thm list

val setParents : thm -> thm list -> thm

(* hidden lits from case splitting *)

val restoreHiddenLits : thm -> (Literal.literal IntMap.map) -> thm

(* Tautologies *)

val isTautology : thm -> bool

(* Contradictions *)

val isContradiction : thm -> bool

(* Unit theorems *)

val destUnit : thm -> Literal.literal

val isUnit : thm -> bool

(* Unit equality theorems *)

val destUnitEq : thm -> Term.term * Term.term

val isUnitEq : thm -> bool

(* Literals *)

val member : Literal.literal -> thm -> bool

val negateMember : Literal.literal -> thm -> bool

(* ------------------------------------------------------------------------- *)
(* A total order.                                                            *)
(* ------------------------------------------------------------------------- *)

val compare : thm * thm -> order

val equal : thm -> thm -> bool

(* ------------------------------------------------------------------------- *)
(* Free variables.                                                           *)
(* ------------------------------------------------------------------------- *)

val freeIn : Term.var -> thm -> bool

val freeVars : thm -> NameSet.set

(* ------------------------------------------------------------------------- *)
(* Pretty-printing.                                                          *)
(* ------------------------------------------------------------------------- *)

val ppInferenceType : inferenceType Print.pp

val inferenceTypeToString : inferenceType -> string

val pp : thm Print.pp

val toString : thm -> string

val inferenceToString : (inferenceType * thm list) -> string

val labelToString : clauseLabel -> string

val extendedToString : thm -> string

(* ------------------------------------------------------------------------- *)
(* Primitive rules of inference.                                             *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(* ----- axiom C                                                             *)
(*   C                                                                       *)
(* ------------------------------------------------------------------------- *)

val axiom : clause -> thm
val conjecture : clause -> thm
val split : clause -> thm list -> thm
val cases : clause -> thm list -> thm
val caseSplit : clause -> thm list -> thm
val leftCaseSplit : clause -> thm list -> thm
val rightCaseSplit : thm -> thm -> thm -> thm
val mergeCaseSplit : thm -> thm -> thm
val negCaseSplit : clause -> thm -> thm


(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(* ----------- assume L                                                      *)
(*   L \/ ~L                                                                 *)
(* ------------------------------------------------------------------------- *)

val assume : Literal.literal -> thm

(* ------------------------------------------------------------------------- *)
(*    C                                                                      *)
(* -------- subst s                                                          *)
(*   C[s]                                                                    *)
(* ------------------------------------------------------------------------- *)

val subst : Subst.subst -> thm -> thm

(* ------------------------------------------------------------------------- *)
(*   L \/ C    ~L \/ D                                                       *)
(* --------------------- resolve L                                           *)
(*        C \/ D                                                             *)
(*                                                                           *)
(* The literal L must occur in the first theorem, and the literal ~L must    *)
(* occur in the second theorem.                                              *)
(* ------------------------------------------------------------------------- *)

val resolve : Literal.literal -> thm -> thm -> thm

(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(* --------- refl t                                                          *)
(*   t = t                                                                   *)
(* ------------------------------------------------------------------------- *)

val refl : Term.term -> thm

(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(* ------------------------ equality L p t                                   *)
(*   ~(s = t) \/ ~L \/ L'                                                    *)
(*                                                                           *)
(* where s is the subterm of L at path p, and L' is L with the subterm at    *)
(* path p being replaced by t.                                               *)
(* ------------------------------------------------------------------------- *)

val equality : Literal.literal -> Term.path -> Term.term -> thm

(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(* Arithmetic simplification of certain literals                             *)
(*                                                                           *)
(* ------------------------------------------------------------------------- *)

val arith_with_flag : thm -> thm * bool
val arith : thm -> thm

(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(* Creating a clause with the help of a decision procedure                   *)
(*                                                                           *)
(* ------------------------------------------------------------------------- *)

val decision : clause -> thm list -> thm

(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(* Merging clauseLabels - these should be ordered int lists (sets with       *)
(* no repeated elements).                                                    *)
(*                                                                           *)
(* ------------------------------------------------------------------------- *)

val mergeLabels : clauseLabel -> clauseLabel -> clauseLabel

val mergeTheoremListLabels : thm list -> clauseLabel

val updateLabel : clauseLabel -> thm -> thm

val getLevel : thm -> int

val addLevelToLabel : int -> thm -> thm
val removeTopLevelFromLabel : thm -> thm

val labelsDifferent : thm -> thm -> bool
end
