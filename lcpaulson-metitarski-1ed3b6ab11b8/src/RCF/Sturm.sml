(* ======================================================================== *)
(*                    Sturm Chains and Real Root Isolation                  *)
(*                                                                          *)
(*  by G.O.Passmore, LFCS, Univ. Edinburgh and Clare Hall, Univ. Cambridge  *)
(* Contact: (e) grant.passmore@cl.cam.ac.uk   (w) www.cl.cam.ac.uk/~gp351/. *)
(* ======================================================================== *)

structure Sturm : Sturm =
struct

open Algebra;
open Groebner;

(* Cache of computed Sturm sequences *)

exception STURM_HASH;

fun hash_poly_pair (p, q) =
    Word.xorb (hash_poly p, hash_poly q);

fun mk_sturm_cache (n) =
    Polyhash.mkTable (Word.toIntX o hash_poly_pair, (op =))
		     (n, STURM_HASH);

val sturm_cache = mk_sturm_cache 1000;

(* Cache of polynomial root isolation *)

exception POLY_ROOTS_HASH;

fun mk_roots_cache (n) =
    Polyhash.mkTable (Word.toIntX o hash_poly, (op =))
		     (n, POLY_ROOTS_HASH);

val roots_cache = mk_roots_cache 100;

(* Sign datatype *)

datatype sign = NEG | ZERO | POS;

(* Compute sign of a rational *)

fun sign_of_rat q =
    case Rat.compare(q, Rat.zero) of
	General.GREATER => POS
      | General.EQUAL => ZERO
      | General.LESS => NEG;

(* Univariate polynomial derivative *)

fun d_dx [] = p_zero
  | d_dx [(_, [])] = p_zero
  | d_dx ((c, [(v, p)]) :: ps) =
    let val cp = Rat.mult(c, Rat.rat_of_int p)
	val p' = p-1
	val m = if p' = 0 then (cp, []) else (cp, [(v, p')])
    in p_sum (poly_of_mono m, d_dx ps)
    end
  | d_dx _ = raise Useful.Error "Only univariate derivatives supported.";

(* Univariate polynomial gcd *)

fun gcd f g =
    if g = Algebra.p_zero then f else
    let val (_, r) = Groebner.p_div f [g]
    in gcd g r end;

(* Make a univariate polynomial square-free. *)

fun square_free p =
    let val g = gcd p (d_dx p)
	val (a, _) = Groebner.p_div p [g]
	val q = Array.sub (a, 0)
    (* Make sure we haven't flipped the sign *)
	val p_sign = sign_of_rat (p_lc p)
	val q_sign = sign_of_rat (p_lc q)
    in if p_sign = q_sign then q else p_neg q end;

(* Are two univariate polynomials coprime? *)

fun coprime f g =
    (gcd f g) = p_one;

(* Negated polynomial remainder sequence *)

fun neg_prs p q seq =
    let val (_, r) = Groebner.p_div p [q]
	val r_neg = Algebra.p_neg r
    in if (r = Algebra.p_zero) then
	   List.rev seq
       else neg_prs q r_neg (r_neg :: seq)
    end;

(* Sturm chain (between p and dp/dx) *)

fun sturm_chain p =
    let val p_0 = square_free p
	val p_0' = d_dx p_0
    in
	case Polyhash.peek sturm_cache (p_0, p_0') of
	    SOME sc =>
	    let val _ = () (* print ("Found Sturm chain in sturm_cache!\n") *)
	    in sc end
	 |  NONE =>
	    let val sc = neg_prs p_0 p_0' [p_0', p_0]
		val _ = Polyhash.insert sturm_cache ((p_0, p_0'), sc)
	    in sc end
    end

(* General Sturm chain (between p and q) *)

fun gen_sturm_chain p q =
    let val p_0 = square_free p
	(* val p_0' = square_free q  -- Does not need to be square-free! *)
    in
	case Polyhash.peek sturm_cache (p_0, q) of
	    SOME sc =>
	    let val _ = () (* print ("Found Sturm chain in sturm_cache!\n") *)
	    in sc end
	 |  NONE =>
	    let val sc = neg_prs p_0 q [q, p_0]
		val _ = Polyhash.insert sturm_cache ((p_0, q), sc)
	    in sc end
    end;

(* Knuth's upper-bound for positive roots of a polynomial.

   Given p = Sum_{i=0}^n a_i*x^i in Q[x], all positive roots of p are
   bounded above by:

     2*max{kth_root(-a_{n-k}/a_n) | 1 <= k <= n, a_{n-k}<0}.

   We make use of floating point rounding mode setting to assure we
   (at worst) overestimate the upper-bound. As a side-effect, we set
   the floating point rounding mode to IEEEReal.TO_POSINF via
   IntvlsFP.set_rm. Note that MetiTarski (in particular, the IntvlsFP
   module) is robust w.r.t this side-effect. *)

fun knuth_bound p =
    let val p = Algebra.p_monic p
	val a_n = IntvlsFP.rat_to_fp_hi (Algebra.p_lc p)
	val n = Algebra.p_deg p
	fun kth_root_expr a_n_minus_k k =
	    if (a_n_minus_k < 0.0) then
		Math.pow(~a_n_minus_k/a_n, 1.0/k) else 0.0
	(* Compute max{kth_root(-a_{n-k}/a_n) | ...} for Knuth bound *)
	fun max_tm p cur_max =
	    (case p of
		 [] => cur_max
	       | [(c, [])] =>
		 let val rat_c = IntvlsFP.rat_to_fp_hi c
		 in
		     Real.max(cur_max, kth_root_expr rat_c (Real.fromInt n))
		 end
	       | (c, [(_, pow)]) :: ps =>
		 let val rat_c = IntvlsFP.rat_to_fp_hi c
		     val k' = kth_root_expr rat_c (Real.fromInt (n - pow))
		 in
		     if (k' > cur_max) then max_tm ps k'
		     else max_tm ps cur_max
		 end
	      | _ => raise Useful.Error "Only univariate polynomials supported.")
    in
	IntvlsFP.set_rm(IntvlsFP.HI);
	2.0 * (max_tm p 0.0)
    end;

(* Compute an interval with rational (integral) endpoints containing
   all real roots of a polynomial. We convert all roots into positive
   roots (by considering p(x) and p(-x) separately), and use Knuth's
   bound for computing an upper-bound of all positive roots, negating
   the result as appropriate. We return the interval as a pair of
   rational endpoints (lb,ub) : Rat.rat * Rat.rat. *)

fun root_bounds p =
    let	val ub = knuth_bound p
	val lb = ~(knuth_bound (Algebra.p_subst_neg_x p))
	val l = (Real.toLargeInt IEEEReal.TO_NEGINF lb)
	val r = (Real.toLargeInt IEEEReal.TO_POSINF ub)
    in (Rat.rat_of_intinf (l - 1), (* We widen by +- 1 *)
	Rat.rat_of_intinf (r + 1))
    end;

(* Given a sequence of signs, compute the number of `sign changes'
   occurring in the sequence, ignoring ZEROes. *)

fun num_sign_changes seq =
    let fun num_sign_changes' seq n last =
	    case seq of
		[] => n
	      | ZERO :: rst => num_sign_changes' rst n last
	      | s :: rst => if s<>last andalso last<>ZERO then
				num_sign_changes' rst (n+1) s
			    else
				num_sign_changes' rst n s
    in
	case seq of
	    [] => 0
	  | s :: rst => num_sign_changes' rst 0 s
    end;

(* Given a polynomial p in Q[x] and rational endpoints lb <= ub,
   compute the number of real roots of p in the half-open interval
   (lb, ub]. *)

fun num_roots_in_ho_intvl p lb ub =
    let val sc = sturm_chain p
	val sc_lb = map (fn p => sign_of_rat(p_lc(p_eval(p, 0, lb)))) sc
	val sc_ub = map (fn p => sign_of_rat(p_lc(p_eval(p, 0, ub)))) sc
	val num_lb = num_sign_changes sc_lb
	val num_ub = num_sign_changes sc_ub
    in
	num_lb - num_ub
    end;

(* Given a triple (p, lb, ub), compute the number of real roots
   of p in the *closed* interval [lb, ub] *)

fun num_roots_in_cl_intvl p intvl =
    let val (lb, ub) = intvl
	val k = num_roots_in_ho_intvl p lb ub
	val e = if p_eval(p, 0, lb)=p_zero then 1 else 0
    in k+e end;

(* Midpoint of two rationals a, b *)

fun rat_mid a b =
    Rat.mult (Rat.add(a, b), Rat.inv (Rat.rat_of_int 2));

(* Given a polynomial p, isolate all of its real roots.
   Note that a root may be counted twice if it occurs
   as a midpoint in the bisection. Subsequent functions
   will remove duplicates (e.g., RealAlg.remove_dups). *)

fun isolate_roots p =
    if p_deg(p) = 0 then
	if (p = p_zero) then [(Rat.zero, Rat.zero)] else []
    else
	case Polyhash.peek roots_cache p of
	    SOME rs => (* let val _ = print ("Found roots in roots_cache!\n") in *)
			   rs
		       (* end *)
	  | NONE =>
	    let val p = square_free p
		val p = Algebra.p_monic p
		val (lb, ub) = root_bounds p
		fun isolate_roots' p lb ub =
		    let
			(* val _ = print ("- Isolating roots of " ^ (p_toString p) ^ *)
			(* 		   " in [" ^ (Rat.toString lb) ^ ", " *)
			(* 		   ^ (Rat.toString ub) ^ "].\n") *)
			val k = num_roots_in_cl_intvl p (lb, ub)
		    in
			if k = 0 then
			    ((* print ("   No roots in [" ^ (Rat.toString lb) ^ ", "
		    		^ (Rat.toString ub) ^ "].\n"); *)
			      [])
			else if k = 1 then
			    ((* print ("   Isolated root in [" ^ (Rat.toString lb) ^ ", "
		    		^ (Rat.toString ub) ^ "].\n"); *)
			      [(lb, ub)])
			else
			    let val m = rat_mid lb ub
			    in (isolate_roots' p lb m) @ (isolate_roots' p m ub)
			    end
		    end
	    val rs = isolate_roots' p lb ub
	    val _ = Polyhash.insert roots_cache (p, rs)
	    in
		rs
	    end;

(* Given a p lb, ub s.t. p has exactly one root in [lb,ub],
   `refine' the interval (halving the size) if possible.
   *Note, we're relying on [lb,ub] being *closed*. *)

fun refine_root p intvl =
    let val (lb, ub) = intvl in
	if lb=ub then (lb, ub) else
	let val m = rat_mid lb ub
	in if p_eval(p, 0, m) = p_zero then
	       (m, m)
	   else if p_eval(p, 0, lb) = p_zero then
	       (lb, lb)
	   else if p_eval(p, 0, ub) = p_zero then
	       (ub, ub)
	   else if (num_roots_in_cl_intvl p (lb, m)) > 0 then
	       (lb, m)
	   else (m, ub)
	end
    end;

(* Given a polynomial p, isolate all its real roots, ensuring that
   there is no overlap between any of the isolating intervals *)

fun isolate_roots_no_overlap p =
    let val rs = isolate_roots p in
	map (fn i => refine_root p i) rs
    end;

(* Examples

val p = [((Rat.one), [(0, 4)]), (Rat.one, [(0, 3)]), (Rat.neg Rat.one, [(0, 1)]), (Rat.neg Rat.one, [])] : poly;
p_toString p;
val it = "x0^4 + x0^3 + -1 x0 + -1": string

map p_toString (sturm_chain p);
val it =
   ["x0^4 + x0^3 + -1 x0 + -1", "4 x0^3 + 3 x0^2 + -1",
    "3/16 x0^2 + 3/4 x0 + 15/16", "-32 x0 + -64", "-3/16"]: string list

val q = [((Rat.rat_of_int 100), [(0, 4)]), (Rat.one, [(0, 3)]), (Rat.neg Rat.one, [(0, 1)]), (Rat.neg Rat.one, [])] : poly;
p_toString q;

val p = [(Rat.one, [(0, 2)]), (Rat.rat_of_int ~2, [])] : poly;
p_toString p;
val it = "x0^2 + -2": string

root_bounds p;
val it = (Rat (false, 3, 1), Rat (true, 3, 1)): Rat.rat * Rat.rat

num_roots_in_intvl p (Rat.rat_of_int ~3) Rat.zero;
val it = 1: int

num_roots_in_intvl p (Rat.rat_of_int ~3) (Rat.rat_of_int 2);
val it = 2: int

num_roots_in_intvl p Rat.zero Rat.zero;
val it = 0: int

isolate_roots p;
val it =
   [(Rat (false, 3, 1), Rat (true, 0, 1)),
    (Rat (true, 0, 1), Rat (true, 3, 1))]: (rat * rat) list

val q = [(Rat.one, [(0, 2)]), (Rat.rat_of_int ~16, [])];
isolate_roots q

(* x0^5 + x0^4 + -13 x0^3 + -6 x0^2 + 22 x0 + 15 *)

val bad = [(Rat.one, [(0, 5)]),
           (Rat.one, [(0, 4)]),
           (Rat.rat_of_int ~13, [(0, 3)]),
           (Rat.rat_of_int ~6, [(0, 2)]),
           (Rat.rat_of_int 22, [(0, 1)]),
           (Rat.rat_of_int 15, [])] : poly;

(* x0^2 + 200/147 x0 *)

val bad_2 = [(Rat.one, [(0, 2)]), (Rat.rat_of_quotient(200, 147), [(0, 1)])];

(* x0^2 + -2 x0 *)

val bad_3 = [(Rat.one, [(0, 2)]), (Rat.rat_of_int ~2, [(0, 1)])];



Strange error:
 metit --tptp .. --verbose 1 --univ_cert_rcf exp-problem-1.tptp


*)

end
