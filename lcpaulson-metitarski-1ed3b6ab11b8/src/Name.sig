(* ========================================================================= *)
(* NAMES                                                                     *)
(* Copyright (c) 2001 Joe Hurd, distributed under the MIT license            *)

(* ========================================================================= *)

signature Name =
sig

(* ------------------------------------------------------------------------- *)
(* A type of names.                                                          *)
(* ------------------------------------------------------------------------- *)

type name = string (*LCP*)

(* ------------------------------------------------------------------------- *)
(* A total ordering.                                                         *)
(* ------------------------------------------------------------------------- *)

val compare : name * name -> order

val equal : name -> name -> bool

(* ------------------------------------------------------------------------- *)
(* Fresh names.                                                              *)
(* ------------------------------------------------------------------------- *)

val newName : unit -> name

val newNames : int -> name list

val variantPrime : (name -> bool) -> name -> name

val variantNum : (name -> bool) -> name -> name

(* ------------------------------------------------------------------------- *)
(* Parsing and pretty printing.                                              *)
(* ------------------------------------------------------------------------- *)

val pp : name Print.pp

val toString : name -> string

val fromString : string -> name

end
