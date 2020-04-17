signature Poly =
sig

val delFirstTerm : Term.term * Term.term list -> Term.term list

val is_natural : Term.term -> bool
val isInt : IntInf.int -> Term.term -> bool
val zero : Term.term
val one : Term.term
val minusone : Term.term
val mk_sum : Term.term * Term.term -> Term.term
val mk_prod : Term.term * Term.term -> Term.term
val mk_quo : Term.term * Term.term -> Term.term
val list_prod : Term.term list -> Term.term
val simp_mk_neg : Term.term -> Term.term
val metis_poly_lits : Literal.literal list -> Literal.literal list

val ground_only : bool ref
val unsafe_divisors : bool ref
val is_algebraic : bool -> Term.term -> bool
val is_strictly_algebraic : bool -> Term.term -> bool
val is_algebraic_literal : bool -> Literal.literal -> bool
val is_strictly_algebraic_literal : bool -> Literal.literal -> bool
val is_special_function : string -> bool
val algebraic_ops : string list
val allow_special_functions : bool ref
val allow_nested_special_functions : bool ref

end
