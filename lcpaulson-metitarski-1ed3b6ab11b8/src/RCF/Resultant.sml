(* ======================================================================== *)
(*      Bivariate Polynomial Resultants via a Modular Euclidean Method      *)
(*                                                                          *)
(*  by G.O.Passmore, LFCS, Univ. Edinburgh and Clare Hall, Univ. Cambridge  *)
(* Contact: (e) grant.passmore@cl.cam.ac.uk   (w) www.cl.cam.ac.uk/~gp351/. *)
(* ======================================================================== *)

structure Resultant : Resultant =
struct

(* Note on convention: We write Resultant_x(p,q) when computing a
   resultant of p,q in R[x], for some ring R.

   Thus, Resultant_x : R[x] * R[x] -> R, so that the indeterminate x
   is eliminated. For our bivariate resultants below, R = Q[y]. *)

open Algebra;
open Groebner;

(* Modulus of two (univariate) polynomials *)

fun p_mod p q =
    if p_eq(p, p_zero) then p_zero
    else if p_eq(q, p_one) then p_zero
    else
	(* TODO: Get rid of stupid boxing of q below *) 
	case (p_div p [q]) of 
	    (_, m) => m;

(* Compute (-1)^(a * b) for a,b in Nat *)

fun sign_prod a b =
    if ((a mod 2) = 0 orelse (b mod 2) = 0) then
	1 
    else ~1;

(* Univariate resultants via modified Euclidean algorithm (O(d^2)) *)

fun univ_resultant' f f' r = 
    if p_deg(f') > 0 then
	let val f'' = p_mod f f'
	    (* val _ = print("f'' = " ^ (p_toString f'') ^ "\n") *)
	    val d_f = p_deg(f)
	    val d_f' = p_deg(f')
	    val d_f'' = p_deg(f'')
	    val m = Rat.mult(Rat.rat_of_int(sign_prod d_f d_f'), 
			     Rat.exp(p_lc(f'), Rat.rat_of_int (d_f - d_f'')))
	    val r' = Rat.mult(m, r)
	in univ_resultant' f' f'' r' end
    else 
	if p_eq(f', p_zero) then
	    Rat.zero
	else
	    Rat.mult(r, Rat.exp(p_lc(f'), Rat.rat_of_int (p_deg f))); 

fun univ_resultant f g = univ_resultant' f g Rat.one;

(* Given f, g in Q[x,y] s.t. max(deg(f), deq(g)) <= d, compute (d^2 +
   1) rational values c_i for y s.t. HM(f)[c_i/x] and HM(g)[c_i/x] do
   not vanish.

   The variable x's var_id given as v_id_x. *)

fun non_vanishing_pts' k i hm_f hm_g pts v_id_x u =
    if (i >= k) then pts
    else 
	let val c = u (* Would be interesting to try a `random' rational *)
	    val hm_f_c = m_eval(hm_f, v_id_x, c)
	    val hm_g_c = m_eval(hm_g, v_id_x, c)
	    val next_u = Rat.add(u, Rat.one)
	in
	    if not(m_zero(hm_f_c) orelse m_zero(hm_g_c))
	    then
		let val _ = Array.update(pts, i, c)
		in 
		    non_vanishing_pts' k (i+1) hm_f hm_g pts v_id_x next_u
		end
	    else non_vanishing_pts' k i hm_f hm_g pts v_id_x next_u
	end;

fun non_vanishing_pts f g =
    let val d = Int.max(p_deg(f), p_deg(g))
	val k = d*d + 1
	val hm_f = p_hm f
	val hm_g = p_hm g
	val var_id_x = 0 : Algebra.var_id
	val a = Array.array (k, Rat.one)
    in 
	non_vanishing_pts' k 0 hm_f hm_g a var_id_x Rat.one
    end;

(* Given f,g in Q[x,y] of total degree at most d, compute
    Resultant_x(f(c, y), g(c, y)) in Q[y] for (d^2 + 1) rational
    values of c which do not cancel a leading term of f or g.

    Note that we return a pair of the form

      ((s_1, ..., s_k), (v_1, ..., v_k)), 

           s.t.

       Resultant_y(f(s_i, y), g(s_i, y)) = v_i. *)

fun biv_to_univ_res_pts f g =
    let val sample_pts = non_vanishing_pts f g
	val value_pts = Array.array (Array.length sample_pts, Rat.one)
	val _ = Array.copy {di=0, src=sample_pts, dst=value_pts}
	val var_id_x = 0 : Algebra.var_id
	fun local_res pt =
	    let val f_c = p_eval(f, var_id_x, pt)
		val g_c = p_eval(g, var_id_x, pt)
		val r_c = univ_resultant f_c g_c
	    in 
		r_c
	    end
	val _ = Array.modify local_res value_pts
    in (sample_pts, value_pts) end;

(* Compute the bivariate resultant of f and g through a modular
   Euclidean method, using Lagrange interpolation to stitch up the
   solutions. Note that f,g in Q[x,y], and the resultant we compute,
   Resultant_x(f,g), lives in Q[y] (we're eliminating x). *)

fun biv_resultant f g =
    let val (s_pts, v_pts) = biv_to_univ_res_pts f g
	val poly_y = [(Rat.one, [(1, 1)])] : Algebra.poly
	fun y_minus_q q = p_sum (poly_y, (poly_of_rat (Rat.neg q)))
	(* Prod_{j != i} (y - s_j) *)
	fun i_interp_num i j k = 
	    if j >= k then p_one else
	    let val m = if j<>i then 
			    (y_minus_q (Array.sub(s_pts, j))) else p_one 
	    in p_mult(m, (i_interp_num i (j+1) k)) end
	(* Prod_{j != i} (s_i - s_j) *)
	fun i_interp_den i j k =
	    if j >= k then Rat.one else
	    let val m = if j<>i then
			    (Rat.add(Array.sub(s_pts, i), (Rat.neg (Array.sub(s_pts, j)))))
			else Rat.one
	    in Rat.mult(m, (i_interp_den i (j+1) k)) end
	(* Sum_{i=0}^{k-1} (i_interp_num i)/(i_interp_den i) *)
	fun sum i k =
	    if i >= k then p_zero else
	    let val v_i = poly_of_rat (Array.sub(v_pts, i))
		val n_i = i_interp_num i 0 k
		val d_i = Algebra.poly_of_rat (Rat.inv (i_interp_den i 0 k))
		val r_i = Algebra.p_mult (n_i, d_i)
		val e_i = Algebra.p_mult (v_i, r_i)
	    in 
		Algebra.p_sum (e_i, sum (i+1) k)
	    end
	val k = Array.length s_pts
    in
	sum 0 k
    end;

end

(* Examples:

val p = [((Rat.rat_of_int 2), [(0, 2)]), (Rat.one, [(0, 1)]), (Rat.one, [])] : poly;
p_toString p;
val it = "2 x0^2 + x0 + 1": string

val q = [((Rat.rat_of_int 2), [(0, 3)]), (Rat.one, [(0, 1)]), (Rat.one, [])] : poly;
p_toString q;
val it = "2 x0^3 + x0 + 1": string

Rat.toString (univ_resultant p q);
val it = "16": string

Rat.toString (univ_resultant q p);
val it = "16": string

Rat.toString (univ_resultant p (p_mult(p, q)));
val it = "0": string

val f_c = [(Rat.one, [(1, 2)]), (Rat.rat_of_int ~2, [(1, 1)]), (Rat.neg Rat.one, [])];
val g_c = [(Rat.one, [(1, 2)]), (Rat.rat_of_int ~3, [])];

Rat.toString(univ_resultant f_c g_c);
val it = "-8": string

Rat.toString(univ_resultant g_c f_c);
val it = "-8": string

val f_c' = [(Rat.one, [(0, 2)]), (Rat.rat_of_int ~2, [(0, 1)]), (Rat.neg Rat.one, [])];
val g_c' = [(Rat.one, [(0, 2)]), (Rat.rat_of_int ~3, [])];

Rat.toString(univ_resultant f_c' g_c');
Rat.toString(univ_resultant g_c' f_c');

val r = p_sum(p, [(Rat.rat_of_int 5, [(1, 2)])]);
p_toString r;
val it = "5 x1^2 + 2 x0^2 + x0 + 1": string

p_toString(p_eval(p, 0, Rat.rat_of_int 10));
val it = "211": string

p_toString(p_eval(r, 0, Rat.rat_of_int 10));
val it = "5 x1^2 + 211": string

val p = [(Rat.one, [(0, 2)]), (Rat.rat_of_int ~2, [])] : poly;
p_toString p;
val it = "x0^2 + -2": string

val q = [(Rat.one, [(0, 2)]), (Rat.rat_of_int ~3, [])] : poly;
p_toString q;
val it = "x0^2 + -3": string

(* Compute f(x-y), where x0=x, x1=y, f=(x^2 - 2) *)
val r = [(Rat.one, [(0, 1)])] : poly;
val r' = [(Rat.neg Rat.one, [(1, 1)])] : poly;
val r = p_sum(r, r') : poly;
val r = p_mult(r,r) : poly;
val r = p_sum(r, poly_of_rat (Rat.rat_of_int ~2));

p_toString r;
val it = "x1^2 + -2 x1 x0 + x0^2 + -2": string

val q' = [(Rat.one, [(1, 2)]), (Rat.rat_of_int ~3, [])] : poly;
p_toString q';
val it = "x1^2 + -3": string

biv_to_univ_res_pts r q';

val res = biv_resultant r q';
p_toString res;
val it = "x1^4 + -10 x1^2 + 1": string

*)
