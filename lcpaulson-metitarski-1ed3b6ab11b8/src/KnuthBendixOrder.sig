(* ========================================================================= *)
(* THE KNUTH-BENDIX TERM ORDERING                                            *)
(* Copyright (c) 2001 Joe Hurd, distributed under the MIT license            *)

(* ========================================================================= *)

signature KnuthBendixOrder =
sig

(* ------------------------------------------------------------------------- *)
(* The weight of all constants must be at least 1, and there must be at most *)
(* one unary function with weight 0.                                         *)
(* ------------------------------------------------------------------------- *)

(*LCP: Many extensions: the notion of subterm coefficient*)
type kbo =
     {weight        : string -> int,
      subterm_coeff : string -> int,
      precedence : Term.function * Term.function -> order};

val default : kbo

val compare : kbo -> Term.term * Term.term -> order option

end
