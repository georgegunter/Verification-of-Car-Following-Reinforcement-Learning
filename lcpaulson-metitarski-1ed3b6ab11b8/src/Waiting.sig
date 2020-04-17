(* ========================================================================= *)
(* THE WAITING SET OF CLAUSES                                                *)
(* Copyright (c) 2001 Joe Hurd, distributed under the MIT license            *)

(* ========================================================================= *)
(* Modified to allow lazy deleting of clauses no longer valid because of     *)
(* dependence on a split that has been deleted.         JPB 1.2.11           *)
(* ========================================================================= *)
(* modified 22.3.11 to allow clauses to be added to the front of the Queue   *)

signature Waiting =
sig

(* ------------------------------------------------------------------------- *)
(* The parameters control the order that clauses are removed from the        *)
(* waiting set: clauses are assigned a weight and removed in strict weight   *)
(* order, with smaller weights being removed before larger weights.          *)
(*                                                                           *)
(* The weight of a clause is defined to be                                   *)
(*                                                                           *)
(*   d * s^symbolsWeight * v^variablesWeight * l^literalsWeight * m          *)
(*                                                                           *)
(* where                                                                     *)
(*                                                                           *)
(*   d = the derivation distance of the clause from the axioms               *)
(*   s = the number of symbols in the clause                                 *)
(*   v = the number of distinct variables in the clause                      *)
(*   l = the number of literals in the clause                                *)
(*   m = the truth of the clause wrt the models                              *)
(* ------------------------------------------------------------------------- *)

type weight = real

type modelParameters =
     {model : Model.parameters,
      initialPerturbations : int,
      maxChecks : int option,
      perturbations : int,
      weight : weight}

type parameters =
     {symbolsWeight : weight,
      variablesWeight : weight,
      literalsWeight : weight,
      labelWeight : weight,
      models : modelParameters list}

(* ------------------------------------------------------------------------- *)
(* A type of waiting sets of clauses.                                        *)
(* ------------------------------------------------------------------------- *)

type waiting

type distance = real

(* type deletedSplits *)

(* ------------------------------------------------------------------------- *)
(* Basic operations.                                                         *)
(* ------------------------------------------------------------------------- *)

val default : parameters

val new :
    parameters ->
    {axioms : Clause.clause list,
     conjecture : Clause.clause list} -> waiting

val size : waiting -> int

val pp : waiting Print.pp

(* ------------------------------------------------------------------------- *)
(* Adding new clauses.                                                       *)
(* ------------------------------------------------------------------------- *)

val set_maxweight : int -> unit  (*LCP*)
val maxweight_used : real ref    (*LCP*)
val maxweight : weight ref
val maxweightSet : bool ref
val SOSweightFactor : weight ref

val add : waiting -> distance * Clause.clause list -> waiting

val addToFrontOfQueue : Clause.clause -> waiting -> waiting

(* ------------------------------------------------------------------------- *)
(* Removing the lightest clause.                                             *)
(* ------------------------------------------------------------------------- *)

val remove : waiting -> ((real * (distance * Clause.clause)) * waiting) option
                         (*LCP*)

val removeIfValid : waiting -> ((real * (distance * Clause.clause)) * waiting) option
  (* removes the next clause that does not depend on a deleted split  JPB *)

val deleteClauses : int -> waiting -> waiting 


(* DEBUG CODE *)
val printDeletedSplits : waiting -> string -> waiting

end
