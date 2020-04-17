(* ========================================================================= *)
(* SUBSUMPTION CHECKING FOR FIRST ORDER LOGIC CLAUSES                        *)
(* Copyright (c) 2001 Joe Hurd, distributed under the MIT license            *)

(* ========================================================================= *)
(* Modified by JPB 22.2.11 to allow for the saving of deleted clauses within *)
(* the subs structure.                                                       *)
(* ------------------------------------------------------------------------- *)

signature Subsume =
sig

(* ------------------------------------------------------------------------- *)
(* A type of clause sets that supports efficient subsumption checking.       *)
(* ------------------------------------------------------------------------- *)

type 'a subsume

val new : unit -> 'a subsume

val size : 'a subsume -> int

val insert : 'a subsume -> Thm.clause * 'a -> 'a subsume

val filter : ('a -> bool) -> 'a subsume -> 'a subsume

val pp : 'a subsume Print.pp

val toString : 'a subsume -> string

(* functions to store and retrieve a list of subsuming and subsumed clauses *)

val updateDeleted : 'a subsume ->  (Thm.clause * Subst.subst * 'a) -> 'a -> 'a subsume
 
val extractDeleted : 'a subsume * (('a * 'a) list) -> 'a subsume * (('a * 'a) list)

val addDeleted : 'a subsume * (('a * 'a) list) -> 'a subsume

val added : 'a subsume -> 'a list
(* ------------------------------------------------------------------------- *)
(* Subsumption checking.                                                     *)
(* ------------------------------------------------------------------------- *)

val subsumes :
    (Thm.clause * Subst.subst * 'a -> bool) -> 'a subsume -> Thm.thm -> 'a ->
    ((Thm.clause * Subst.subst * 'a) option) * ('a subsume)

val isSubsumed : 'a subsume -> Thm.thm -> 'a -> bool * ('a subsume)

val strictlySubsumes :  (* exclude subsuming clauses with more literals *)
    (Thm.clause * Subst.subst * 'a -> bool) -> 'a subsume -> Thm.thm -> 'a ->
    ((Thm.clause * Subst.subst * 'a) option * 'a subsume)

val isStrictlySubsumed : 'a subsume -> Thm.thm -> 'a -> bool * ('a subsume)

(* ------------------------------------------------------------------------- *)
(* Single clause versions.                                                   *)
(* ------------------------------------------------------------------------- *)

val clauseSubsumes : Thm.clause -> Thm.clause -> Subst.subst option

val clauseStrictlySubsumes : Thm.clause -> Thm.clause -> Subst.subst option

end
