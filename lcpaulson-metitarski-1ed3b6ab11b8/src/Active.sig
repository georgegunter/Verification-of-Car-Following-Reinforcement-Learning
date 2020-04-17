(* ========================================================================= *)
(* THE ACTIVE SET OF CLAUSES                                                 *)
(* Copyright (c) 2001 Joe Hurd, distributed under the MIT license            *)

(* ========================================================================= *)

signature Active =
sig

(* ------------------------------------------------------------------------- *)
(* A type of active clause sets.                                             *)
(* ------------------------------------------------------------------------- *)

type simplify =
     {subsume : bool,
      reduce : bool,
      rewrite : bool}

type parameters =
     {clause : Clause.parameters,
      prefactor : simplify,
      postfactor : simplify}

(* expanded by JPB from
   type active
to the following to allow access to internals from SplitStack.sml 8/2/11 *)
datatype active = Active of
      {parameters : parameters,
       clauses : Clause.clause IntMap.map,
       units : Units.units,
       rewrite : Rewrite.rewrite,
       subsume : Clause.clause Subsume.subsume,
       literals : (Clause.clause * Literal.literal) LiteralNet.literalNet,
       equations :
         (Clause.clause * Literal.literal * Rewrite.orient * Term.term)
         TermNet.termNet,
       subterms :
         (Clause.clause * Literal.literal * Term.path * Term.term)
         TermNet.termNet,
       allSubterms : (Clause.clause * Term.term) TermNet.termNet}

val extractDeleted : active -> active * ((Clause.clause * Clause.clause) list)

val getAllClauses : active -> Clause.clause list

(* ------------------------------------------------------------------------- *)
(* Basic operations.                                                         *)
(* ------------------------------------------------------------------------- *)

val emptyExisting : active -> active

val default : parameters

val size : active -> int

val saturation : active -> Clause.clause list

val redundant : active -> Clause.clause list

(* ------------------------------------------------------------------------- *)
(* Create a new active clause set and initialize clauses.                    *)
(* ------------------------------------------------------------------------- *)

val new :
    parameters -> {axioms : Thm.thm list, conjecture : Thm.thm list} ->
    active * {axioms : Clause.clause list, conjecture : Clause.clause list}

(* ------------------------------------------------------------------------- *)
(* Add a clause into the active set and deduce all consequences.             *)
(* ------------------------------------------------------------------------- *)

val add : active -> Clause.clause -> active * Clause.clause list

(* ------------------------------------------------------------------------------------------------ *)
(* version of add divided into three parts (like Gaul) to allow case splitting after simplification *)
(* ------------------------------------------------------------------------------------------------ *)
val simplify : active -> Clause.clause -> active * Clause.clause option
val factorOnly : active -> Clause.clause -> active * Clause.clause list
val addAndFactor : active -> Clause.clause -> active * Clause.clause list

(* ------------------------------------------------------------------------- *)
(* Pretty printing.                                                          *)
(* ------------------------------------------------------------------------- *)

val pp : active Print.pp

val max_splits_r : int ref  (*LCP: for case splitting*)


(* --------------------------------------------- *)
(* Case split if possible (backtracking version) *)
(* --------------------------------------------- *)
val caseSplitClause  : Clause.clause -> (Clause.clause * Clause.clause) option

(* ----------------------------------------------------------------- *)
(* Add a negated left split clause to appropriate bits of active set *)
(* ----------------------------------------------------------------- *)
val addNegatedLeftSplit : active -> Clause.clause list -> active


(* ----------------------------------------------------------------- *)
(* Function to check for quotient, equality and square splits - made *)
(* external to allow it to be called before case splitting.          *)
(* ----------------------------------------------------------------- *)
val canBQsplit : Clause.clause -> bool


end
