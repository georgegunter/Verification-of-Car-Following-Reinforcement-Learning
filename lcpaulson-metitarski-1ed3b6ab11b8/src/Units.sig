(* ========================================================================= *)
(* A STORE FOR UNIT THEOREMS                                                 *)
(* Copyright (c) 2001 Joe Hurd, distributed under the MIT license            *)

(* ========================================================================= *)

signature Units =
sig

(* ------------------------------------------------------------------------- *)
(* A type of unit store.                                                     *)
(* ------------------------------------------------------------------------- *)

type unitThm = Literal.literal * Thm.thm

type units

(* ------------------------------------------------------------------------- *)
(* Basic operations.                                                         *)
(* ------------------------------------------------------------------------- *)

val empty : units

val size : units -> int

val toString : units -> string

val pp : units Print.pp

(* ------------------------------------------------------------------------- *)
(* Add units into the store.                                                 *)
(* ------------------------------------------------------------------------- *)

val add : units -> unitThm -> units

val addList : units -> unitThm list -> units

(* ------------------------------------------------------------------------- *)
(* Matching.                                                                 *)
(* ------------------------------------------------------------------------- *)

val match : units -> Literal.literal -> (unitThm * Subst.subst) option

(* ------------------------------------------------------------------------- *)
(* Reducing by repeated matching and resolution.                             *)
(* ------------------------------------------------------------------------- *)

val reduce : units -> Rule.rule

(* ---------------------------------------------------------------- *)
(* Filtering function to allow the removal of units on backtracking *)
(* ---------------------------------------------------------------- *)
val filter : units -> (unitThm -> bool) -> units

end
