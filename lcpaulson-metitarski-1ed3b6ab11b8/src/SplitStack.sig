(* ========================================================================= *)
(* Routines for operating the Split Stack                                    *)
(* This version 13.1.11                                                      *)
(* ========================================================================= *)

signature SplitStack =
sig

(* ---------------------------------------- *)
(* types of deleted clauses and split stack *)
(* ---------------------------------------- *)

type deletedClauses = (Thm.clauseLabel * Clause.clause) list

(* the set B of blocked clauses can contain zero (if it is a right branch), *)
(* one (just the right branch clause) or two (right branch clause plus the  *)
(* negated left branch clause if it is ground).                             *)
(* For simplicity the two clauses will be separate entries.                 *) 

type stackEntry

type splitStack

datatype proofState = ProofState of { active : Active.active,
                        waiting : Waiting.waiting,
                        deleted : deletedClauses,
                        stack : splitStack,
                        restored : Clause.clause list,
                        hidden : Literal.literal IntMap.map} (* hidden literals from case splits *)


val breadthFirstProof : bool ref
val replayProofDecisions : bool ref

val newStack : unit -> splitStack
val newDeletedClauses : unit -> deletedClauses

val stackDepth : splitStack -> int
val transferDeletedClauses : proofState -> proofState

val restoreKeptDeletedClauses : deletedClauses -> (Clause.clause list) -> (int list) -> deletedClauses * (Clause.clause list)

val fullyExpandThm : Thm.thm -> (Literal.literal IntMap.map) -> Thm.thm

val stackToLabel : splitStack -> Thm.clauseLabel

(* update the split stack for a new case split - the actual splitting *)
(* of the clauses is done prior to this function being called e.g. in *)
(* the module Active.sml.                                             *)
(* The left clause is returned with an updated label and the right    *)
(* clause is added to the stack as a blocked clause.                  *)

val caseSplit : (Clause.clause * Clause.clause * Clause.clause * splitStack) -> (Clause.clause * splitStack)

                
(* clause thm is a conflicting clause i.e. the empty clause but it has a label*)
(* containing at least one undeleted split (otherwise it would not have been  *)
(* passed by the function Waiting.removeIfValid) - therefore backtracking is  *)
(* required.                                                                  *)  
val backtrack : Clause.clause -> proofState -> (Clause.clause * proofState)

(* function to filter clause list - aimed at algebraic_clauses list *)
val filterClauseList : Clause.clause list -> splitStack -> Clause.clause list

(* function to add deleted clauses to deleted clause list *)
val addToDeletedClauses : Clause.clause * Clause.clause -> deletedClauses -> splitStack -> deletedClauses

(* unforced backtrack to release clauses when e.g. waiting is empty *)
val unforcedBacktrack : proofState -> proofState

val dumpClauses : Active.active -> Waiting.waiting -> string -> unit

val returnParents : splitStack -> (Clause.clause) list

end
