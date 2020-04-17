(* ========================================================================= *)
(* THE RESOLUTION PROOF PROCEDURE                                            *)
(* Copyright (c) 2001 Joe Hurd, distributed under the MIT license            *)

(* ========================================================================= *)

signature Resolution =
sig

(* ------------------------------------------------------------------------- *)
(* A type of resolution proof procedures.                                    *)
(* ------------------------------------------------------------------------- *)

type parameters =
     {active : Active.parameters,
      waiting : Waiting.parameters}

type resolution

val maxStackDepth : int ref (* maximum depth for the case splitting stack *)
val set_maxalg : int -> unit (* max number of symbols in an algebraic clause *)
val rerunWithHighMaxAlg : bool -> unit (* set rerun with high value of maxalg on waiting empty *)
val setMaxRunOutsideSOS : int -> unit (* maximum run of non SOS given clauses allowed before giving up *)
val allow_sf_in_algebraic_clauses : bool ref (* allow special functions in algebraic_clauses (as well as Given Clause) *)

(* ------------------------------------------------------------------------- *)
(* Basic operations.                                                         *)
(* ------------------------------------------------------------------------- *)

val default : parameters

val new :
    parameters -> {axioms : Thm.thm list, conjecture : Thm.thm list} ->
    resolution

val active : resolution -> Active.active

val waiting : resolution -> Waiting.waiting

val pp : resolution Print.pp

(* ------------------------------------------------------------------------- *)
(* The main proof loop.                                                      *)
(* ------------------------------------------------------------------------- *)

datatype decision =
    Contradiction of Thm.thm
  | Satisfiable of Thm.thm list

datatype state =
    Decided of decision
  | Undecided of resolution

val iterate : resolution -> state

val loop : resolution -> decision

end
