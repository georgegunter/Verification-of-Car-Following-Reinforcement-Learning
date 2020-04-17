(* ======================================================================== *)
(*        Groebner basis computation using Buchberger's Algorithm           *)
(*                                                                          *)
(* by G.O.Passmore, Cambridge Computer Laboratory and LFCS, Edinburgh, 2011 *)
(* Contact: (e) grant.passmore@cl.cam.ac.uk   (w) www.cl.cam.ac.uk/~gp351/. *)
(* ======================================================================== *)

structure Groebner :> Groebner =
struct

open Algebra;
open List;

(* Given two algebraic polys in canonical form, 
   compute their S-polynomial w.r.t. the active monomial ordering. *)

fun s_poly p q =
    let val (monic_p, monic_q) = (p_monic p, p_monic q)
	val (lm_p, lm_q) = (List.hd monic_p, List.hd monic_q)
	val (hpp_p, hpp_q) = 
	    case (lm_p, lm_q) of ((_, pp), (_, pp')) => (pp, pp')
	val L = pp_lcm (hpp_p, hpp_q)
	val dm_p = (Rat.one, pp_div (L, hpp_p)) : mono
	val dm_q = (Rat.one, pp_div (L, hpp_q)) : mono
	val s_p = mp_mult (dm_p, monic_p)
	val s_q = mp_mult (dm_q, monic_q)
    in 
	p_sub (s_p, s_q)
    end;

(* Given a polynomial h and an array of polynomials fs_arr, compute
   the least index i s.t. LPP(fs_arr[i]) | LPP(h), if such an i
   exists.  We return SOME i | NONE.  Note: the auxiliary div_idx' has
   a different signature, involving only LPP(h). *)

fun div_idx' hpp_h fs_arr i l =
    if (i > l - 1) then NONE
    else let val f_i = Array.sub (fs_arr, i)
	     val pp_i = p_hpp f_i
	 in case pp_divides (pp_i, hpp_h) of
		true => SOME i
	      | _ => div_idx' hpp_h fs_arr (i + 1) l end;

fun div_idx h fs_arr = 
    div_idx' (p_hpp h) fs_arr 0 (Array.length fs_arr);

(* Multivariate polynomial division: the work-horse of Groebner reduction. *)

fun p_div' h fs_arr us_arr r =
    if h = p_zero orelse h = [] then (us_arr, r) else
    case div_idx h fs_arr of
	SOME i => 
	let val f_i = Array.sub (fs_arr, i)
	    val u_i = Array.sub (us_arr, i)
	    val m = m_div (p_hm h, p_hm f_i)
	    val _ = Array.update (us_arr, 
				  i, 
				  (p_sum (u_i, (poly_of_mono m))))
	    val h' = p_sub (h, (mp_mult(m, f_i)))
	in p_div' h' fs_arr us_arr r end
      | NONE =>
	let val r' = p_sum (r, (poly_of_mono (p_hm h)))
	    val h' = List.tl h
	in p_div' h' fs_arr us_arr r' end; 

fun p_div f fs = 
    let val fs_arr = Array.fromList fs
	val us_arr = Array.array (List.length(fs), p_zero)
    in p_div' f fs_arr us_arr p_zero end;

(* Construct a list of indices of S-polynomials which need
   to be processed.  Given n, we construct the set (list) of
   pairs of natural numbers of the form:

     {(x,y) | 0 <= x < y < n}. 

   This gives unique commuting binary combinations, i.e., 
    (length (idx_pairs n)) = ``n choose 2.''  

   This is useful if we use an array-based representation of a growing
    Groebner basis. *)

(* *** idx_pairs is currently deprecated ***

fun idx_pairs' i j b r =
    if j = b then r
    else if i < j then 
	idx_pairs' (i + 1) j b ((i, j) :: r)
    else idx_pairs' 0 (j + 1) b r;

fun idx_pairs n = idx_pairs' 0 1 n [];

*)

(* Given a list, return a list of pairs of all unique commuting binary
   combinatons.  This is useful if we use a list-based representation
   of a growing Groebner basis. *)

fun uc_pairs f =
    case f of
	[] => []
      | (x :: xs) => foldl (fn (y, l) => (x, y) :: l)
			   (uc_pairs xs)
			   xs;

(* Buchberger's algorithm for Groebner basis construction. *)

fun buchberger' gs s_pairs =
    case s_pairs of 
	[] => gs
      | ((p, p') :: ps) =>
	let val q = s_poly p p' 
	    val (_, q') = p_div q gs
	    val (c, pp) = p_hm q'
	in
	    if not(Rat.eq(c, Rat.zero)) andalso pp = [] 
	    then [p_one] 
	    else
		if p_eq (q', p_zero)
		then buchberger' gs ps else
		buchberger' (q' :: gs) 
			    ((map (fn x => (q', x)) gs) @ s_pairs)
	end;

fun buchberger fs = buchberger' fs (uc_pairs fs);

(* Reduce a GBasis *)

fun gb_reduce gs =
    let val set_gs = ref (Useful.setify gs)
	fun to_remove fs f =
	    exists (fn p => pp_divides (p_hpp p, p_hpp f)) fs
	val _ = map (fn p => 
			let val gs_without_p = filter (fn x => not(x = p)) (!set_gs)
			in if to_remove gs_without_p p
			   then set_gs := gs_without_p else () end)
		    (!set_gs)
	val _ = set_gs := map p_monic (!set_gs)
	val _ = set_gs := map (fn p => case p_div p (filter (fn x => not(x = p)) (!set_gs))
					of (_, r) => r) (!set_gs)
	(* val _ = (print ("\n Reduced GB: \n"); map (fn p => print ((p_toString p) ^ "\n")) (!set_gs)) *)
    in !set_gs end;

(* Examples:

   // f_1 = 2 x1 _ x0 + 1

    val f_1 = [((Rat.rat_of_int 2), [(1, 1)]), (Rat.one, [(0, 1)]), (Rat.one, [])] : poly;

   // f = x1^2 x0 + 4 x1 x0 - 3 x0^2

    val f = [(Rat.one, [(1, 2), (0, 1)]), ((Rat.rat_of_int 4), [(1, 1), (0, 1)]), ((Rat.rat_of_int ~3), [(0, 2)])] : poly;   

   // p_div f [f_1]

   > p_toString (case p_div f [f_1] of (_, r) => r);
   > val it = "1/4 x0^3 + -9/2 x0^2 + -7/4 x0": string


>  val p = [(Rat.one, [(1,1),(0,1)]), (Rat.one, [])] : poly;
val p = [(Rat (true, 1, 1), [(1, 1), (0, 1)]), (Rat (true, 1, 1), [])]: poly
>  val q = [(Rat.one, [(2,1),(0,1)]), (Rat.one, [])] : poly;
val q = [(Rat (true, 1, 1), [(2, 1), (0, 1)]), (Rat (true, 1, 1), [])]: poly
> buchberger [p,q];
val it =
   [[(Rat (false, 1, 1), [(1, 1)]), (Rat (true, 1, 1), [(2, 1)])],
    [(Rat (true, 1, 1), [(1, 1), (0, 1)]), (Rat (true, 1, 1), [])],
    [(Rat (true, 1, 1), [(2, 1), (0, 1)]), (Rat (true, 1, 1), [])]]:
   Algebra.poly list
> map p_toString (buchberger [p,q]);
val it = ["-1 x1 + x2", "x1 x0 + 1", "x2 x0 + 1"]: string list

*)

end;

