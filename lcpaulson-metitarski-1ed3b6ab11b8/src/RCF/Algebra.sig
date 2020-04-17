(* ======================================================================== *)
(*             Basic Multivariate Polynomial Algebra over Q[\vec{x}]        *)
(*                                                                          *)
(*  by G.O.Passmore, LFCS, Univ. Edinburgh and Clare Hall, Univ. Cambridge  *)
(* Contact: (e) grant.passmore@cl.cam.ac.uk   (w) www.cl.cam.ac.uk/~gp351/. *)
(* ======================================================================== *)

signature Algebra = 
sig

(* Var ID type *)

type var_id;

(* Var-power type *)

type vp;

(* Power-product type *)

type pp;

(* Monomial type *)

type mono;

(* Polynomial type *)

type poly;

(* Is a monomial zero? *)

val m_zero : mono -> bool;

(* Monomial multiplication *)

val m_mult : mono * mono -> Rat.rat * vp list;

(* Monomial, Polynomial multiplication *)

val mp_mult : mono * poly -> poly;

(* Monomial negation *)

val m_neg : mono -> Rat.rat * pp;

(* Multivariate total degree of monomial *)

val m_deg : mono -> int;

(* Degree reverse lexicographic ordering on monomials *)

val m_lt : mono * mono -> bool;

(* Convert monomial to polynomial *)

val poly_of_mono : mono -> poly;

(* Convert Rat.rat to polynomial *)

val poly_of_rat : Rat.rat -> poly;

(* Make a polynomial monic (in the context of an implicit = 0) *)

val p_monic : poly -> poly;

(* Compute the LCM of two power-products in canonical form *)

val pp_lcm : pp * pp -> pp;

(* Divide one power-product by another *)

val pp_div : pp * pp -> pp;

(* Does one power-product divide another? *)

val pp_divides : pp * pp -> bool;

(* Given a polynomial, return its head power-product. *)

val p_hpp : poly -> pp;

(* Given a polynomial, return its head monomial. *)

val p_hm : poly -> mono;

(* Divide one monomial by another *)

val m_div : mono * mono -> mono;

(* Polynomial + *)

val p_sum : poly * poly -> poly;

(* Polynomial unary - *)

val p_neg : poly -> poly;

(* Polynomial subtraction *)

val p_sub : poly * poly -> poly;

(* Polynomial multiplication *)

val p_mult : poly * poly -> poly;

(* Are two polynomials equal? *)

val p_eq : poly * poly -> bool;

(* Polynomial multivariate total degree *)

val p_deg : poly -> int;

(* Polynomial leading coefficient *)

val p_lc : poly -> Rat.rat;

(* Polynomial constant coefficient *)

val p_cc : poly -> Rat.rat;

(* Evaluation of monomial w.r.t. a var_id specializaiton *)

val m_eval : mono * var_id * Rat.rat -> mono;

(* Evaluation of polynomial w.r.t. a var_id specializaiton *)

val p_eval : poly * var_id * Rat.rat -> poly;

(* Substitution of a polynomial into another polynomial,
   w.r.t. a var_id substitution target. *)

val p_subst : poly * var_id * poly -> poly;

(* Given p(x), compute p(-x) *)

val p_subst_neg_x : poly -> poly;

(* Make a `univariate' poly univariate in a given variable *)

val mk_univ_in : poly * var_id -> poly;

(* Sum the absolute values of a polynomial's coefficeints *)

val p_sum_abs_coeffs : poly -> Rat.rat;

(* Compute the max of all absolute values in all coefficients *)

val p_max_abs_coeffs : poly -> Rat.rat;

(* Make a polynomial integral without modifying roots *)

val p_integral : poly -> poly;

(* Power-product to string *)

val pp_toString : (int * int) list -> string;

(* Monomial to string *)

val m_toString : mono -> string;

(* Polynomial to string *)

val p_toString : mono list -> string;

(* Polynomial to string, LaTeX friendly*)

val p_toStringLatex : mono list -> string;

(* Univariate polynomial to string (Isabelle/HOL style) *)

val univ_p_toString : mono list -> string;

(* Zero polynomial *)

val p_zero : poly;

(* One polynomial *)

val p_one : poly;

(* Hashing *)

val hash_poly : poly -> word;

val hash_polys : poly list -> word;


end;
