(* ======================================================================== *)
(*       Arithmetic in the (Ordered) Field of Real Algebraic Numbers        *)
(*                                                                          *)
(*  by G.O.Passmore, LFCS, Univ. Edinburgh and Clare Hall, Univ. Cambridge  *)
(* Contact: (e) grant.passmore@cl.cam.ac.uk   (w) www.cl.cam.ac.uk/~gp351/. *)
(* ======================================================================== *)

signature RealAlg =
sig

(* An opaque type of real algebraic numbers *)

type real_alg;

(* A purported real algebraic number is not unique and thus can't be
   represented. *)

exception Non_unique of string;

(* Is a real_alg known to be a rational? Note, at any given time, it's
   possible that a real_alg is rational but we don't `know' it yet. *)

val known_rat : real_alg -> bool;

(* Given a polynomial p and a pair of rationals l <= u, construct a
   representation for a real algebraic number r s.t. p(r) = 0 and r is
   the unique root of p in the real interval [l, u]. *)

val mk_real_alg :
    Algebra.poly -> Rat.rat -> Rat.rat -> Rat.rat option -> real_alg;

(* Given a rational, construct a real_alg representing it *)

val real_alg_of_rat : Rat.rat -> real_alg;

(* Sign of a real algebraic number *)

val sign : real_alg -> Sturm.sign;

(* Sign of a polynomial at a given real algebraic number *)

val sign_at : Algebra.poly -> real_alg -> Sturm.sign;

(* Negate a real algebraic number (additive inverse) *)

val neg : real_alg -> real_alg;

(* Add two real algebraic numbers *)

val add : real_alg * real_alg -> real_alg;

(* Multiply two real algebraic numbers *)

val mult : real_alg * real_alg -> real_alg;

(* Compute alpha^n for alpha : real_alg and n : nat *)

val pow : real_alg * int -> real_alg;

(* Compute an interval representation for a real algebraic number *)

val intvl_rep :
    real_alg -> Algebra.poly * Rat.rat * Rat.rat * (Rat.rat option);

(* Given a list of polynomials ps, compute a complete set of sample
   points from the CAD of R^1 induced by ps. *)

val univ_cad_sample : Algebra.poly list -> real_alg list;

(* String representation of a real algebraic number *)

val toString : real_alg -> string;

(* Isabelle/HOL-style string representation of RAG *)

val toIsabelleString : real_alg -> string;

(* A LaTeX-friendly string representation *)

val toStringLatex : real_alg -> string;

(* Is a real_alg actually a rational or integer?  We provide a
   classification function to determine the smallest class of numbers
   (either IsInt, IsRat or IsReal) to which the real_alg belongs. *)

datatype num_type = IsInt | IsRat | IsReal;

val num_type_of : real_alg -> int -> num_type;

(* A type for real algebraic r_cells *)

datatype r_cell = Alg_pt of real_alg  (* [r] for r \in R_alg *)
                | OIntvl of real_alg * real_alg (* [a,b] for a < b in R_alg *)
                | LInf of real_alg    (* (-inf, r) with r \in R_alg  *)
                | RInf of real_alg    (* (r, +inf) with r \in R_alg  *);

(* A string representation of an r-cell *)

val r_cell_to_string : r_cell -> string;

(* Given a list of polynomials ps, compute an r_cell decomposition
   of R^n induced by ps. This is described in Passmore's paper
   "Decidability of univariate real algebra with predicates for
    rational and integer powers" *)

val r_cell_decomposition : Algebra.poly list -> r_cell list;

end
