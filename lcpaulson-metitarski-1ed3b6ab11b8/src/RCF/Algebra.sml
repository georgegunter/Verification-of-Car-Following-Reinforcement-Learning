(* ======================================================================== *)
(*             Basic Multivariate Polynomial Algebra over Q[\vec{x}]        *)
(*                                                                          *)
(*  by G.O.Passmore, LFCS, Univ. Edinburgh and Clare Hall, Univ. Cambridge  *)
(* Contact: (e) grant.passmore@cl.cam.ac.uk   (w) www.cl.cam.ac.uk/~gp351/. *)
(* ======================================================================== *)

structure Algebra : Algebra =
struct

(* Var ID type *)

type var_id = int;

(* Var-power type *)

type vp = var_id * int;

(* Power-product type *)

type pp = vp list;

(* Monomial type *)

type mono = Rat.rat * pp;

(* Polynomial type *)

type poly = mono list;

(* Hashing *)

fun hash_vp (v, p) = Polyhash.hashw (Word.fromInt v, Word.fromInt p);

val hash_pp = foldl (fn ((v,p),w) => Word.xorb (hash_vp (v,p), w)) 0w0;

fun hash_m ((c, pp) : mono) : word =
    Polyhash.hashw(Rat.hashw (c, 0w0), hash_pp pp);

val hash_poly = foldl (fn (m,w) => Word.xorb (hash_m m, w)) 0w0;

val hash_polys = foldl (fn (p,w) => Word.xorb (hash_poly p, w)) 0w0;

(* Given two power-products in canonical form (ordered with their
   var_id's descending), return their product in canonical form. *)

fun pp_mult' (pp : pp, pp' : pp, result : pp) =
    case (pp, pp') of
	([], a) => (List.rev result) @ a
      | (a, []) => (List.rev result) @ a
      | (((vid, pow) :: s), (((vid', pow') :: s'))) =>
	if (vid = vid') then
	    pp_mult' (s, s', (vid, pow + pow') :: result)
	else if (vid > vid') then
	    pp_mult' (s, pp', (vid, pow) :: result)
	else pp_mult' (pp, s', (vid', pow') :: result);

fun pp_mult (pp : pp, pp' : pp) = pp_mult' (pp, pp', []);

(* Multiply monomials *)

fun m_mult (m : mono, m' : mono) =
    case (m, m') of
	((c, pp), (c', pp')) =>
	(Rat.mult (c, c'), pp_mult(pp, pp'));

(* Negate a monomial *)

fun m_neg (m : mono) =
    case m of
	(c, pp) => (Rat.neg c, pp);

(* Multivariate total degree of a power-product *)

fun pp_deg' (pp : pp, result) =
    case pp of
	[] => result
      | (_, pow) :: s => pp_deg' (s, pow + result);

fun pp_deg (pp : pp) = pp_deg' (pp, 0);

(* Multivariate total degree of a monomial *)

fun m_deg ((_, p) : mono) = pp_deg p;

(* Deg-diff: The first place in which two monomials disagree *)

fun m_deg_diff' (pp : pp, pp' : pp) =
    case (pp, pp') of
	([], []) => NONE
      | ([], (_, p) :: _) => SOME (0, p)
      | ((_, p) :: _, []) => SOME (p, 0)
      | ((v, p) :: s, (v', p') :: s') =>
	if (v > v') then SOME (p, 0) else
	if (v < v') then SOME (0, p') else
	if not(p = p') then SOME (p, p') else
	m_deg_diff' (s, s');

fun m_deg_diff (m : mono, m' : mono) =
    case (m, m') of
	((_, pp), (_, pp')) =>
	if (pp = pp') then NONE else
	m_deg_diff' (pp, pp');

(* Lexicographic ordering on monomials *)

fun m_lt_lex (m : mono, m' : mono) =
    case m_deg_diff (m, m') of
	SOME (i, j) => i < j
      | NONE => false;

(* Graded reverse lexicographic ordering on monomials *)

fun m_lt_degrevlex (m : mono, m' : mono) =
    let val (deg_m, deg_m') = (m_deg m, m_deg m')
    in
	(deg_m < deg_m') orelse
	((deg_m = deg_m') andalso
	 case m_deg_diff (m, m') of
	     SOME (i, j) => i > j
	   | NONE => false)
    end;

(* ************************************************************ *)
(* Set monomial order here. Choice is currently between Lex and *)
(* DegRevLex.                                                   *)
(*                                                              *)
(* val m_lt = m_lt_degrevlex;                                   *)
(*                                                              *)
(* Note that Lex should currently be used for real algebraic    *)
(*   number computations.                                       *)

val m_lt = m_lt_lex;

(* ************************************************************ *)

(* Turn a rational into a monomial *)

fun mono_of_rat (q : Rat.rat) =
    (q, []) : mono;

(* Turn a monomial into a polynomial *)

fun poly_of_mono (m : mono) =
    case m of
	(c, _) =>
	if c = Rat.zero then [] else [m];

(* Turn a rational into a polynomial *)

fun poly_of_rat (q : Rat.rat) = poly_of_mono (mono_of_rat q);

(* Is a monomial's coefficent 0? *)

fun m_zero (m : mono) =
    case m of (c, _) => Rat.eq (c, Rat.zero);

(* Zero polynomial *)

val p_zero = poly_of_rat Rat.zero;

(* One polynomial *)

val p_one = poly_of_rat Rat.one;

(* Is a polynomial a zero polynomial? *)

fun p_isZero p =
    case p of [m] => m_zero m
	    | _ => false;

(* Given two polynomials in canonical form (ordered in descending
   order w.r.t. m_lt), return a new polynomial which is their sum also
   expressed in canonical form. *)

fun p_sum' (p : poly, p' : poly, result : poly) =
    case (p, p') of
	([], s) => if not(p_isZero(s)) then (List.rev result) @ s : poly
		   else (List.rev result)
      | (s, []) => if not(p_isZero(s)) then (List.rev result) @ s
		   else (List.rev result)
      | (m :: s, m' :: s') =>
	case (m, m') of
	    ((c, pp), (c', pp')) =>
	    if (pp = pp') then
		let val d = Rat.add(c, c') in
		    if Rat.eq(d, Rat.zero) then
			p_sum' (s, s', result)
		    else p_sum' (s, s', (Rat.add(c, c'), pp) :: result)
		end
	    else if m_lt(m', m) then
		p_sum' (s, p', if not(m_zero(m)) then m :: result else result)
	    else p_sum' (p, s', if not(m_zero(m')) then m' :: result else result)

fun p_sum (p : poly, p' : poly) = p_sum' (p, p', [] : poly);

(* Negate a polynomial in canonical form *)

fun p_neg (p : poly) = List.map m_neg p;

(* Subtract two polynomials in canonical form *)

fun p_sub (p : poly, p' : poly) =
    p_sum (p, p_neg p') : poly;

(* Multiply a monomial and a polynomial, both in canonical form *)

fun mp_mult' (m : mono, p : poly, result : poly) =
    case p of
	[] => result
      | (m' :: s') =>
	let val x = m_mult(m, m') in
	    mp_mult' (m, s', p_sum(poly_of_mono(x), result))
	end;

fun mp_mult (m : mono, p : poly) = mp_mult' (m, p, []) : poly;

(* Multiply two polynomials, both in canonical form *)

fun p_mult' (p : poly, p' : poly, result : poly) =
    case (p, p') of
	([], _) => result
      | (m :: s, p') =>
	p_mult'(s, p', p_sum(result, mp_mult(m, p')));

fun p_mult (p : poly, p' : poly) =
    if List.length(p) <= List.length(p') then
	p_mult' (p, p', []) else p_mult' (p', p, []) : poly;

(* Raise a polynomial to a given non-negative power *)

fun p_pow (p : poly, n : int) =
    if n < 0 then raise Useful.Error "Polynomial raised to negative power."
    else if n = 0 then p_one
    else if n = 1 then p
    else p_mult(p, p_pow(p, n-1));

(* Make a polynomial monic (used when it is implicitly = 0) *)

fun p_monic (p : poly) =
    let val (c, _) = List.hd p
	val c' = ((Rat.inv c), []) : mono
    in mp_mult (c', p) end;

(* Compute the LCM of two power-products in canonical form *)

fun pp_lcm' (pp : pp, pp' : pp, result : pp) : pp =
    case (pp, pp') of
	([], pp') => (List.rev result) @ pp'
      | (pp, []) => (List.rev result) @ pp
      | ((v, pow) :: r, (v', pow') :: r') =>
	if (v > v') then
	    pp_lcm' (r, pp', (v, pow) :: result)
	else if (v < v') then
	    pp_lcm' (pp, r', (v', pow') :: result)
	else if (pow > pow') then
	    pp_lcm' (r, r', (v, pow) :: result)
	else pp_lcm' (r, r', (v', pow') :: result);

fun pp_lcm (pp : pp, pp' : pp) = pp_lcm' (pp, pp', []) : pp;

(* Divide a pp by another, breaking if division would be unclean.
   Again, we utilise the fact that the pps are in canonical form. *)

fun pp_div' (pp : pp, pp' : pp, result : pp) : pp =
    case (pp, pp') of
	([], []) => (List.rev result)
      | ([], _) => raise Useful.Error "Unclean power-product division"
      | (pp, []) => (List.rev result) @ pp
      |  ((v, pow)::r, (v', pow')::r') =>
	 if v' > v then raise Useful.Error "Unclean power-product division"
	 else if v > v' then pp_div' (r, pp', (v, pow) :: result)
	 else if pow > pow' then pp_div' (r, r', (v, (pow - pow')) :: result)
	 else if pow = pow' then pp_div' (r, r', result)
	 else raise Useful.Error "Unclean power-product division";

fun pp_div (pp : pp, pp' : pp) : pp = pp_div' (pp, pp', [] : pp) : pp;

(* Divide one monomial by another, breaking if the division
   would be unclean. *)

fun m_div (m : mono, m' : mono) =
    case (m, m') of
	((c, pp), (c', pp')) =>
	(Rat.mult (c, Rat.inv(c')),
	 pp_div (pp, pp'));

(* Does one power-product, pp, divide another one, pp'? *)

fun pp_divides (pp : pp, pp' : pp) =
    case (pp, pp') of
	([], _) => true
      | (_, []) => false
      | ((v, pow)::r, (v', pow')::r') =>
	if (v > v') then false else
	if (v = v') then
	    (pow <= pow' andalso pp_divides (r, r'))
	else pp_divides (pp, r');

(* Given a polynomial, return its head monomial. *)

fun p_hm (p : poly) : mono =
    case p of
	[] => (Rat.zero, [])
      | (c, pp) :: _ => (c, pp);

(* Given a polynomial, return its head power-product. *)

fun p_hpp (p : poly) : pp = case p of [] => [] | (_, pp) :: _ => pp;

(* Given a polynomial, return its multivariate total degree *)

fun p_deg (p : poly) : int = m_deg (p_hm p);

(* Given a polynomial, return its leading coefficient *)

fun p_lc (p : poly) : Rat.rat =
    case (p_hm p) of
	(c, _) => c;

(* Given a polynomial, return its constant coefficient *)

fun p_cc (p : poly) : Rat.rat =
    case p of
	[] => Rat.zero
      | _ => case (hd (rev p)) of
		 (c, pp) =>
		 if pp = [] then c else Rat.zero;

(* Are two monomials equal? *)

fun m_eq (m, m') =
    case (m, m') of
	((c, pp), (c', pp')) =>
	Rat.eq (c, c') andalso pp = pp';

(* Are two polynomials equal? *)

fun p_eq (p, p') =
    List.length p = List.length p'
    andalso ListPair.all m_eq (p, p');

(* Given a var_id i, a rational value q, and a pp/mono/poly p,
   evaluate p with var[i] specialized to q. *)

fun pp_eval (pp : pp, (c', pp') : mono, i : var_id, q : Rat.rat) : mono =
    case pp of
	[] => (c', List.rev pp')
      | ((v, p) :: vps) =>
	if (v = i) then
	    pp_eval (vps,
		     (Rat.mult(c', Rat.exp(q, Rat.rat_of_int p)), pp'),
		     i,
		     q)
	else pp_eval (vps, (c', ((v, p) :: pp')), i, q);

fun m_eval (m : mono, i : var_id, q : Rat.rat) =
    case m of
	(c, pp) => pp_eval (pp, (mono_of_rat c), i, q);

fun p_eval (p : poly, i : var_id, q : Rat.rat) =
    List.foldl (fn (m, p) => p_sum(poly_of_mono(m_eval(m, i, q)), p)) p_zero p;

(* Given a var_id i, a polynomial q, and a pp/mono/poly p, compute the
   polynomial p[q/var(i)], i.e., the polynomial given by substituting
   q for var(i) in the polynomial p. *)

fun pp_subst (pp : pp, i : var_id, q : poly, new_poly : poly) =
    case pp of
	[] => new_poly
      | ((v, pow) :: vps) =>
	if (v = i) then
	    pp_subst(vps,
		     i,
		     q,
		     (p_mult(p_pow(q, pow), new_poly)))
	else let val new_factor = poly_of_mono(Rat.one, [(v, pow)])
		 val new_poly' = p_mult(new_factor, new_poly)
	     in
		 pp_subst(vps, i, q, new_poly')
	     end;

fun m_subst (m : mono, i: var_id, q : poly) =
    case m of
	(c, pp) => pp_subst(pp, i, q, (poly_of_rat c));

fun p_subst (p : poly, i : var_id, q : poly) =
    List.foldl (fn (m, p) => p_sum(m_subst(m, i, q), p)) p_zero p;

(* Given a `univariate' polynomial encoded as a general polynomial,
   p(x), compute p(-x). *)

fun p_subst_neg_x p =
    case p of [] => []
	    | [(_, [])] => p
	    | (c, [(var, pow)]) :: ps =>
	      if (pow mod 2) = 0 then
		  (c, [(var, pow)]) :: (p_subst_neg_x ps)
	      else (Rat.neg c, [(var, pow)]) :: (p_subst_neg_x ps)
	    | _ => raise Useful.Error "Only univariate polynomials supported."

(* Given a `univariate' polynomial encoded as general polynomial,
   make it univariate in the given variable symbol. Note, we do
   not check to see if the source polynomial is really univariate.
   Rather, we just check to make sure that every monomial has
   a powerproduct of length at most one. This is fine for all of
   our uses of this function. *)

fun mk_univ_in (p : poly, i : var_id) =
    case p of
	[] => p_zero
      | [(c, [])] => (poly_of_rat c)
      | (c, [(_, p)]) :: ms =>
	p_sum((poly_of_mono (c, [(i, p)])), mk_univ_in(ms, i))
      | _ => raise Useful.Error ("mk_univ_in: Poly has pp of length > 1!");

(* Compute the sum of the absolute values of all coefficients *)

fun p_sum_abs_coeffs (p : poly) =
    let fun rat_abs q = if (Rat.ge0 q) then q else (Rat.neg q)
    in
	foldl (fn ((c, _) : mono, q : Rat.rat) =>
		  Rat.add(rat_abs c, q))
	      Rat.zero
	      p
    end;

(* Compute the max of all absolute values in all coefficients *)

fun p_max_abs_coeffs (p : poly) =
    let fun rat_abs q = if (Rat.ge0 q) then q else (Rat.neg q)
        fun rat_max a b = if Rat.le (b, a) then a else b
    in
        foldl (fn ((c, _) : mono, q : Rat.rat) =>
                  rat_max (rat_abs c) q)
              Rat.zero
              p
    end;

(* Make a polynomial have integer coefficients while still retaining
   its same set of real roots. We do this by multiplying through by
   the denominators of each rational coefficient. *)

fun p_integral p =
    let fun big_c p u =
	    case p of
		[] => u
	      | ((c, _) :: ms) =>
		let val (a,b) = Rat.quotient_of_rat c
		in if b <> 1 then
		       big_c ms (b*u)
		   else big_c ms u
		end
	val c = big_c p 1
    in
	if c <> 1 then
	    p_mult(poly_of_rat (Rat.rat_of_intinf c), p)
	else
	    p
    end;

(* Power-product to string *)

fun pp_toString (pp : pp) =
    case pp of
	[] => ""
      | ((v, p) :: s) => "x" ^ Int.toString(v)
			 ^ (if not(p = 1) then ("^" ^ Int.toString(p)) else "")
			 ^ (if null(s) then "" else (" " ^ pp_toString(s)));

(* LaTeX printing for univariate polynomials *)

fun pp_toStringLatex (pp : pp) =
    case pp of
	[] => ""
      | ((v, p) :: s) => "x"
			 ^ (if not(p = 1) then ("^" ^ Int.toString(p)) else "")
			 ^ (if null(s) then "" else (" " ^ pp_toString(s)));

(* Monomial to string *)

fun m_toString (m : mono) =
    case m of
	(c, pp) =>
	let val pp_null = null(pp) in
	    (if Rat.eq(c, Rat.one) andalso not(pp_null) then ""
	     else (Rat.toString(c) ^ (if pp_null then "" else " ")))
	    ^ pp_toString(pp)
	end;

fun m_toStringLatex (m : mono) =
    case m of
	(c, pp) =>
	let val pp_null = null(pp) in
	    (if Rat.eq(c, Rat.one) andalso not(pp_null) then ""
	     else (Rat.toString(c) ^ (if pp_null then "" else " ")))
	    ^ pp_toStringLatex(pp)
	end;


(* Polynomial to string *)

fun p_toString (p : poly) =
    case p of
	[] => ""
      | (m :: s) => m_toString(m) ^
		    (if null(s) then "" else (" + " ^ p_toString(s)));

fun p_toStringLatex (p : poly) =
    case p of
	[] => ""
      | (m :: s) => m_toStringLatex(m) ^
		    (case s of
		         [] => ""
		       | (c, pp) :: ms =>
			 if Rat.lt (c, Rat.zero) then
			     (" " ^ p_toString(s))
			 else
			     (" + " ^ p_toString(s)));


(* Univariate poly to string, using Isabelle/HOL notation.
   E.g., (x*x - 2) --> "[:-2,0,1:]". *)

fun univ_p_toString (p : poly) =
    let val deg = p_deg p
	fun f p d =
	    if d > deg then [] else
	    if p = [] then "0" :: (f p (d+1)) else
	    let val ((c, pp) :: ms) = p
		val mono_deg = pp_deg pp in
		if mono_deg = d then
		    ((Rat.toString c) :: (f ms (d+1)))
		else (* mono_deg > d *)
		    "0" :: (f p (d+1))
	    end
	val p' = List.rev p in
	String.concatWith ", " (f p' 0)
    end;

end
