(* ======================================================================== *)
(*       Arithmetic in the (Ordered) Field of Real Algebraic Numbers        *)
(*                                                                          *)
(*  by G.O.Passmore, LFCS, Univ. Edinburgh and Clare Hall, Univ. Cambridge  *)
(* Contact: (e) grant.passmore@cl.cam.ac.uk   (w) www.cl.cam.ac.uk/~gp351/. *)
(* ======================================================================== *)

structure RealAlg : RealAlg =
struct

open Algebra;
open Groebner;
open Resultant;
open Sturm;

(* Exception: Described real algebraic number is not unique. *)

exception Non_unique of string;

(* Interval representation of a real algebraic number              *)
(* Note: We now also tag it if it's known to be an exact rational. *)
(*       This is the (Rat.rat option) component of the type.       *)

type real_alg = Algebra.poly * Rat.rat * Rat.rat * (Rat.rat option);

(* Is a real_alg known to be a rational? Note, at any given time, it's
   possible that a real_alg is rational but we don't `know' it yet. *)

fun known_rat a =
    case a of
        (_, _, _, SOME _) => true
      | _  => false;

(* Polynomial `x' (actually, `x0') *)

val p_x = [(Rat.one, [(0, 1)])] : poly;

(* A unique real_alg representation of zero: (x, 0, 0). *)

val zero = (p_x, Rat.zero, Rat.zero, SOME Rat.zero) : real_alg;

(* Given a poly p in Q[x], and l, u in Q, construct a real algebraic
   number representation of the form (p, l, u). We normalize the
   representation to ensure (i) p is square-free, (ii) p truly has
   exactly one real root in [l, u], and (iii) that [l, u] contains
   zero iff (p, l, u) represents 0.  In this final case, we return
   RealAlg.zero, so that a constructed real_alg value r represents
   zero iff r = RealAlg.zero. *)

fun mk_real_alg p l u q =
    if l=u then (p, l, u, SOME l)
    else
    let val p = Sturm.square_free p
        val p = Algebra.p_monic p
        val k = Sturm.num_roots_in_cl_intvl p (l, u) in
        if k<>1 then
            raise Non_unique ("Poly (" ^ (p_toString p) ^ ") " ^
                              "does not have exactly one root in " ^
                              "the interval [" ^ (Rat.toString l) ^ ", " ^
                              (Rat.toString u) ^ "].")
        else
            if (Rat.le(l, Rat.zero) andalso Rat.le(Rat.zero, u))
            then
                (* [l, u] contains 0 *)
                case (p_div p [p_x]) of
                    (_, m) =>
                    if m = p_zero then
                        (* (p, l, u) represents 0 *)
                        zero
                    else
                        (* Normalize the interval so that it doesn't
                           contain zero.  We use a simple (O(n^2))
                           scheme based on Cauchy's and Landau's
                           bounds on non-zero roots. Note that we
                           could also do this iteratively via interval
                           refinement, avoiding the use of these root
                           bounds. Note, we must make the polynomial
                           integral first, else the bounds are
                           nonsense. *)

                        let val p = Algebra.p_integral p
                            val d = Rat.add(Rat.one, Algebra.p_max_abs_coeffs p)
                            (* e = 1/(1 + (Max_{i=0}^n |a_i|)) *)
                            val e = Rat.inv d
                            val e' = Rat.neg e
                            val f = (fn q => fn p =>
                                        Sturm.sign_of_rat(p_lc(p_eval(p, 0, q))))
                            val sc = Sturm.sturm_chain p
                            val sc_l = map (f l) sc
                            val sc_e' = map (f e') sc
                            val n_l = Sturm.num_sign_changes sc_l
                            val n_e' = Sturm.num_sign_changes sc_e'
                        in
                            if n_l > n_e' then
                                (* negative root in [l, e'] *)
                                (p, l, e', q)
                            else
                                (* positive root in [e, u] *)
                                (p, e, u, q)
                        end
            else
                (* Since we're not representing 0, we'll ensure the
                   polynomial `x' is not a factor. *)
                let val (fs, m) = Groebner.p_div p [p_x]
                in
                    if m = p_zero then
                        (Array.sub(fs, 0), l, u, q)
                    else
                        (p, l, u, q) : real_alg
                end
    end;

(* Compute an interval representation of a real algebraic number.
   Currently, this is just the identity function. But, as we support
   other notations for real_alg's, this will get more elaborate, e.g.,
   converting between positional and interval representation. *)

fun intvl_rep (r : real_alg) = r;

(* String representation of a real algebraic number *)

fun toString (r : real_alg) =
    case r of
       (p, l, u, NONE) => ("RealRoot(" ^ (Algebra.p_toString p) ^
                         ", [" ^ (Rat.toString l) ^ ", " ^
                         (Rat.toString u) ^ "])")
     | (p, l, u, SOME q) => ("RealRoot(" ^ (Algebra.p_toString p) ^
                             ", [" ^ (Rat.toString l) ^ ", " ^
                             (Rat.toString u) ^ "]) = Rat " ^ (Rat.toString q));

(* String representation for LaTeX printing *)

fun toStringLatex (r : real_alg) =
    case r of
       (p, l, u, NONE) => ("\\realroot{" ^ (Algebra.p_toStringLatex p) ^
                         "}{" ^ (Rat.toString l) ^ "}{" ^
                         (Rat.toString u) ^ "}")
     | (p, l, u, SOME q) => (Rat.toString q);


(* Isabelle/HOL style string representation *)

fun toIsabelleString (r : real_alg) =
    case r of
        (p, l, u, SOME q) => ("Rat (" ^ (Rat.toString q)^")")
      | (p, l, u, NONE) => ("Arep [: " ^ (Algebra.univ_p_toString p) ^
                            " :] (" ^ (Rat.toString l) ^ ") (" ^
                            (Rat.toString u) ^ ")") ;

(* Midpoint of two rationals a, b *)

fun rat_mid a b =
    Rat.mult (Rat.add(a, b), Rat.inv (Rat.rat_of_int 2));

(* Given a rational, construct a real_alg representing it.  Note, we
   no longer need to add a little wiggle room for the interval! *)

fun real_alg_of_rat q =
    let val p = [(Rat.one, [(0, 1)]), (Rat.neg q, [])]
    in mk_real_alg
           p
           q
           q
           (SOME q)
    end;

(* Given two real algebraic numbers alpha, beta, a polynomial f, and
   an arithmetic operation on intervals intvl_op, continue refining
   the intervals for alpha and beta until f has precisely one root in
   intvl_op(intvl(alpha), intvl(beta)). *)

fun refine_with_op (alpha, beta : real_alg, f : poly, intvl_op) =
    let val f = Sturm.square_free f
        val (p1, l1, u1, _) = alpha
        val (p2, l2, u2, _) = beta
        val cur_intvl = intvl_op((l1, u1), (l2, u2))
        val k = Sturm.num_roots_in_cl_intvl f cur_intvl
    in
        if k<>1 then
            let val (l1', u1') = Sturm.refine_root p1 (l1, u1)
                val (l2', u2') = Sturm.refine_root p2 (l2, u2)
            in
                refine_with_op((p1, l1', u1', NONE),
                               (p2, l2', u2', NONE),
                               f,
                               intvl_op)
            end
        else
            cur_intvl
    end;

(* Given an interval representation for a real algebraic number alpha,
   compute a representation for -alpha. *)

fun neg alpha =
    if alpha = zero then zero
    else
        let val (p, l, u, q) = alpha
            val neg_q = case q of SOME q => SOME (Rat.neg q)
                                | NONE => NONE
        in
            mk_real_alg (Algebra.p_subst_neg_x p) (Rat.neg u) (Rat.neg l) neg_q
        end;

(* Given interval representations for two real algebraic numbers alpha
   and beta, compute an interval representation for (alpha + beta). *)

fun add (alpha, beta) =
    if alpha = zero then beta
    else if beta = zero then alpha
    else
        case (alpha, beta) of
            ((_,_,_, SOME q1),
             (_,_,_, SOME q2)) => real_alg_of_rat (Rat.add (q1, q2))
          | _ =>
            let val (p1, _, _, _) = alpha
                val (p2, _, _, _) = beta
                val x_minus_y = [(Rat.one, [(0, 1)]),
                                 (Rat.neg Rat.one, [(1, 1)])] : poly
                val y = [(Rat.one, [(1, 1)])] : poly
                val p1_x_minus_y = Algebra.p_subst(p1, 0, x_minus_y)
                val p2_y = Algebra.p_subst(p2, 0, y)
                val res = Resultant.biv_resultant p1_x_minus_y p2_y
                (* Note: res in Q[y]. We must convert to Q[x]. *)
                val f = mk_univ_in(res, 0)
                (* Now, f has (alpha + beta) as a root. But, we must still
               compute an interval [l, u] s.t. (alpha + beta) is f's only
               root in [l, u]. *)
                val (l, u) =
                    refine_with_op(alpha,
                                   beta,
                                   f,
                                   (fn ((l1, u1),
                                        (l2, u2)) =>
                                       (Rat.add(l1, l2),
                                        Rat.add(u1, u2))))
            in mk_real_alg f l u NONE end;

(* Given interval representations for two real algebraic numbers alpha
   and beta, compute an interval representation for (alpha * beta). *)

fun y_degp_p_x_over_y p =
    let val d = p_deg p
        fun f m =
            let val d_m = m_deg m
                val n = d - d_m
                (* y_pow_n = y^n : mono *)
                val y_pow_n = (Rat.one, [(1, n)]) : mono
            in if n > 0 then m_mult (m, y_pow_n) else m end
    in List.foldr (fn (x,y) => p_sum (poly_of_mono x, y))
                  p_zero
                  (map f p)
    end;;

fun rat_min xs = #1 (Useful.minimum Rat.compare xs);
fun rat_max xs = #1 (Useful.maximum Rat.compare xs);

fun mult (alpha, beta) =
    if alpha = zero then zero
    else if beta = zero then zero
    else
        case (alpha, beta) of
            ((_,_,_, SOME q1),
             (_,_,_, SOME q2)) => real_alg_of_rat (Rat.mult (q1, q2))
          | _ =>
            let val (p1, _, _, _) = alpha
                val (p2, _, _, _) = beta
                (* y^{deg(p1)} * p1(x/y) *)
                val p1_lifted = y_degp_p_x_over_y p1
                val y = [(Rat.one, [(1, 1)])] : poly
                val p2_y = Algebra.p_subst(p2, 0, y)
                val res = Resultant.biv_resultant p1_lifted p2_y
                (* Note: res in Q[y]. We must convert to Q[x]. *)
                val f = mk_univ_in(res, 0)
                (* Now, f has (alpha * beta) as a root. But, we must still
               compute an interval [l, u] s.t. (alpha * beta) is f's only
               root in [l, u]. *)
                val (l, u) =
                    refine_with_op(alpha,
                                   beta,
                                   f,
                                   (fn ((l1, u1),
                                        (l2, u2)) =>
                                       let val lst = [Rat.mult(l1,l2),
                                                      Rat.mult(l1,u2),
                                                      Rat.mult(u1,l2),
                                                      Rat.mult(u1,u2)]
                                       in
                                           (rat_min lst,
                                            rat_max lst)
                                       end))
            in mk_real_alg f l u NONE end;

(* Compute alpha^n for n : Nat *)

fun pow (alpha, n) =
    case n of
        0 => real_alg_of_rat (Rat.one)
      | 1 => alpha
      | 2 => mult(alpha,alpha)
      | _ => let val q = Int.quot(n,2)
                 val r = Int.rem(n,2)
                 val m = pow(alpha,q)
             in
                 if r=0 then mult(m,m)
                 else mult(mult(m,m),alpha)
             end;

(* Given a real algebraic number alpha and a polynomial g(x), compute
   the sign of g(alpha). *)

fun sign_at g alpha =
    let val (p, l, u, q) = alpha in
        case q of
            SOME q => Sturm.sign_of_rat(p_lc(p_eval(g, 0, q)))
          | NONE =>
            let val p'g = Algebra.p_mult(Sturm.d_dx p, g)
                val sc = Sturm.gen_sturm_chain p p'g
                val f = (fn q => fn p =>
                            Sturm.sign_of_rat(p_lc(p_eval(p, 0, q))))
                val sc_l = map (f l) sc
                val sc_u = map (f u) sc
                val n = (Sturm.num_sign_changes sc_l) - (Sturm.num_sign_changes sc_u)
            in
                if n<0 then Sturm.NEG
                else if n=0 then Sturm.ZERO
                else Sturm.POS
            end
    end;


(* Given a real algebraic number alpha, compute its sign. By virtue of
   the fact that our intervals only contain zero precisely when the
   real algebraic number is RealAlg.zero, we can read the sign
   directly from one side of the interval boundary. *)

fun sign alpha =
    if alpha = zero then Sturm.ZERO
    else
        let val (_, l, _, _) = alpha in
            if Rat.gt0 l then Sturm.POS
            else Sturm.NEG
        end;

(* Intersect two intervals *)

fun intersect (l1,u1) (l2,u2) =
    let fun q_max x y =
            if Rat.le (y,x) then x else y
        fun q_min x y =
            if Rat.le (x,y) then x else y
    in
        (q_max l1 l2,
         q_min u1 u2)
    end;

(* Is an interval empty? *)

fun empty (l,u) = Rat.lt (u, l);

(* Are two different real_alg's actually equal? *)

fun eq alpha beta =
    let val (p1, l1, u1, _) = alpha
        val (p2, l2, u2, _) = beta
        (* val _ = print ("Checking eq of " ^ (toString alpha)
                           ^ ", " ^ (toString beta) ^ ").\n") *)
        val new_i = intersect (l1,u1) (l2,u2)
    in
        if Rat.lt (u1, l2) then false
        else
            (* sign (add (alpha, (neg beta))) = Sturm.ZERO *)
            (Sturm.num_roots_in_cl_intvl p1 new_i) = 1
            andalso
            (Sturm.num_roots_in_cl_intvl p2 new_i) = 1
            andalso
            (* This is stupidly inefficient! I must think of a better way... *)
            (Sturm.num_roots_in_cl_intvl (p_mult (p1, p2)) new_i) = 1
    end;

(* Separate two roots of two different polynomials,
   making sure their intervals have no overlap. *)

fun separate_roots p1 (l1,u1) p2 (l2,u2) =
    if empty(intersect (l1,u1) (l2,u2)) then ((l1,u1),(l2,u2))
    else let val a' = refine_root p1 (l1,u1)
             val b' = refine_root p2 (l2,u2)
         in separate_roots p1 a' p2 b' end;

(* Given a list of polynomials, compute all of their roots and
   represent them as real algebraic numbers. We make pains to ensure
   that no root appears more than once, even though each real_alg may
   be represented in infinitely many ways (as we don't require
   defining polynomials to be minimal). The output is always sorted
   (from left to right). *)

fun roots_of_polys ps =
    let fun roots_of_polys' ps rs =
            case ps of
                [] => rs
              | (p::ps) =>
                let val p' = Sturm.square_free p
                    val roots = Sturm.isolate_roots_no_overlap p'
                    val sps = map (fn (l, u) => mk_real_alg p' l u NONE)
                                  roots
                in
                    roots_of_polys' ps (sps @ rs)
                end
        (* val ps = Sturm.mk_coprime ps *)
        val rs = roots_of_polys' ps []
        fun cmp ((_, _, u1, _), (_, l2, _, _)) = Rat.compare (u1, l2)
        val rs' = Useful.sort cmp rs
        fun remove_dups rs =
            case rs of
                [] => []
              | [r] => [r]
              | (r1 :: r2 :: rst) =>
                if eq r1 r2 then
                    ((* print "removing duplicate root!\n"; *)
                      remove_dups (r1 :: rst))
                else r1 :: (remove_dups (r2 :: rst))
        fun separate_roots (p1,l1,u1,q1) (p2,l2,u2,q2) =
            if empty(intersect (l1,u1) (l2,u2)) then
                (if Rat.lt (u1,l2) then
                     ((p1,l1,u1,q1),(p2,l2,u2,q2))
                 else
                     ((p2,l2,u2,q2),(p1,l1,u1,q1)))
            else let val (l_a,u_a) = refine_root p1 (l1,u1)
                     val (l_b,u_b) = refine_root p2 (l2,u2)
                 in separate_roots (p1,l_a,u_a,q1) (p2,l_b,u_b,q2) end
        fun separate_in_sequence rs =
            case rs of [] => []
                     | [r] => [r]
                     | r1 :: r2 :: rst =>
                       let val (r1', r2') = separate_roots r1 r2 in
                           r1' :: (separate_in_sequence (r2' :: rst))
                       end
        fun separate_until_sorted rs =
            let val rs' = separate_in_sequence rs
                val rs'' = Useful.sort cmp rs'
            in if rs'' = rs then rs
               else (* Through separation, we've learned that our roots
                       were not in the correct order! So, we must separate
                       and try again. *)
                   separate_until_sorted rs''
            end
    in
        let val out = separate_until_sorted (remove_dups rs')
        (* val _ = print "\n *** Done with roots_of_polys" *)
        in
            out
        end
    end

(* Check to make sure all polys in a list are univariate in x0 *)

fun check_univ ps =
    let fun check_univ_m (m : mono) =
            case m of (_, pp) => List.all (fn (v,p) => v=0) pp
        val check_univ_p = List.all check_univ_m
        val ps_univ = List.all check_univ_p ps
    in
        if not(ps_univ) then
            raise (Useful.Error
                       "Only univariate polynomials supported (CertRCF).\n")
        else ()
    end;

(* Construct a CAD of R^1 induced by polynomials ps *)

fun univ_cad_sample ps =
    let (* val P = foldl Algebra.p_mult p_one ps
           val P' = Algebra.p_monic (Sturm.square_free P) *)
        (* val roots = Sturm.isolate_roots_no_overlap P' *)
        (* val sps = map (fn (l, u) => mk_real_alg P' l u NONE)
                      roots *)
        val _ = check_univ ps
        val ps = Useful.setify ps
        val sps' = roots_of_polys ps
        fun clean_multiple_zs sps z_found clean_sps =
            case sps of [] => clean_sps
                      | alpha :: rst =>
                        if alpha = zero then
                            if z_found then
                                clean_multiple_zs rst z_found clean_sps
                            else
                                clean_multiple_zs rst true (alpha :: clean_sps)
                        else
                            clean_multiple_zs rst z_found (alpha :: clean_sps)
    in
        if sps' = [] then [zero]
        else
            let val (_, l, _, _) = (hd sps')
                val c_sps = ref [real_alg_of_rat
                                     (Rat.rounddown(Rat.add(l, Rat.neg Rat.one)))]
                fun sample_sectors alphas =
                    case alphas of [] => ()
                                 | [(p, l, u, q)] =>
                                   (c_sps := (p, l, u, q) :: (!c_sps);
                                    c_sps := (real_alg_of_rat
                                                  (Rat.roundup(Rat.add(u, Rat.one))))
                                             :: (!c_sps))
                                 | ((p1, l1, u1, q1) :: (p2, l2, u2, q2) :: rst) =>
                                   (c_sps := (p1,l1,u1,q1) :: (!c_sps);
                                    c_sps := (real_alg_of_rat (rat_mid u1 l2)) :: (!c_sps);
                                    (sample_sectors ((p2,l2,u2,q2) :: rst)))
            in
                sample_sectors sps';
                let val out = clean_multiple_zs (!c_sps) false [] in
                    (print "\n -- [Begin univariate CAD sampling]\n     ";
                     print (String.concatWith ",\n     " (List.map toIsabelleString out));
                     print "\n -- [End univariate CAD sampling]\n\n";
                     out)
                end
            end
    end;

(* A type for real algebraic r_cells *)

datatype r_cell = Alg_pt of real_alg  (* [r] for r \in R_alg *)
                | OIntvl of real_alg * real_alg (* [a,b] for a < b in R_alg *)
                | LInf of real_alg    (* (-inf, r) with r \in R_alg  *)
                | RInf of real_alg    (* (r, +inf) with r \in R_alg  *);

fun r_cell_to_string c =
    case c of
        Alg_pt a => ("$[" ^ (toStringLatex a) ^ "]$")
      | OIntvl (a,b) => ("$\\interval[open]{" ^ (toStringLatex a) ^ "}{" ^ (toStringLatex b) ^ "}$")
      | LInf a => ("$\\interval[open]{-\\infty}{" ^ (toStringLatex a) ^ "}$")
      | RInf a => ("$\\interval[open]{" ^ (toStringLatex a) ^ "}{+\\infty}$");

(* The entire real line as an r_cell decomposition *)

val all_r = [LInf zero, Alg_pt zero, RInf zero];

fun itemize strs =
    if strs = [] then "(empty)"
    else
	("\\begin{itemize}\n \\item "
	 ^ (String.concatWith ", \n \\item " strs) ^
	 ".\n\\end{itemize}\n\n");

fun enumerate strs =
    if strs = [] then "(empty)"
    else
	("\\begin{enumerate}\n \\item "
	 ^ (String.concatWith ", \n \\item " strs) ^
	 ".\n\\end{enumerate}\n\n");

(* Given a set of polynomials, decompose R^n into a set of r_cells
   induced by the roots of the polynomials. *)

fun r_cell_decomposition ps =
    let val _ = check_univ ps
	(* We include x as a poly, to ensure splitting of 1-cells at 0. *)
        val ps = Useful.setify (p_x :: ps)
        val sps = roots_of_polys ps
    in
        if sps = [] then
            (print "\n -- [Begin r-cell decomposition]\n     ";
             print (String.concatWith ",\n     " (List.map r_cell_to_string all_r));
             print "\n -- [End r-cell decomposition]\n\n";
	     all_r)
        else
            let val c_l = (hd sps)
                val cells = ref [LInf c_l]
                fun build_cells ss =
                    case ss of [] => ()
                            | [a] => (cells := (Alg_pt a) :: (!cells);
                                      cells := (RInf a) :: (!cells))
                            | a::b::rst => (cells := (Alg_pt a) :: (!cells);
					    if (sign a = sign b orelse
						((sign a = NEG andalso sign b = ZERO) orelse
						 (sign a = ZERO andalso sign b = POS)))
					    then
						cells := (OIntvl (a,b)) :: (!cells)
					    else
						(* In this case, we need to split (a,b) at 0 *)
						(cells := (OIntvl (a, zero)) :: (!cells);
						 cells := (Alg_pt zero) :: (!cells);
						 cells := (OIntvl (zero, b)) :: (!cells));
                                            build_cells (b::rst))
                val _ = build_cells sps
                val r_cells = rev (!cells)
            in
                (print (enumerate (List.map r_cell_to_string r_cells));
                 r_cells)
            end
    end;

(* Is a real_alg actually a rational or integer?  We return the
   smallest class of numbers (either IsInt, IsRat or IsReal) to which
   the real_alg belongs. *)

datatype num_type = IsInt | IsRat | IsReal;

fun range n =
    case n of
        0 => []
      | n => range(n-1) @ [n];

fun factors n =
    List.filter (fn v => (n mod v) = 0) (range n);

fun cartesian [] = []
  | cartesian ([x]) = map (fn e => [e]) x
  | cartesian (x::xs) =
    let val tailCross = cartesian xs
    in foldr (fn (x',result) =>
                 foldr (fn (tc,l) => (x'::tc) :: l ) result tailCross) [] x
    end;

fun possible_rat_roots p =
    let fun get_int q =
            case Rat.dest_integer q of
                SOME n => n
              | NONE => raise (Useful.Error "Possible_rat_roots: Poly must be in Z[x]")
        val cc = IntInf.abs (get_int(p_cc p))
        val lc = IntInf.abs (get_int(p_lc p))
        val cc_fs = factors cc
        val lc_fs = factors lc
        val pairs = cartesian [cc_fs, lc_fs]
        val pos_rats =
            Useful.setify (map (fn x =>
                                   Rat.rat_of_quotient (hd x, hd (tl x))) pairs)
        val neg_rats = map Rat.neg pos_rats
    in
        Useful.union pos_rats neg_rats
    end;

fun rat_in_intvl l u q =
    Rat.le (l, q) andalso Rat.le (q, u);

fun rat_is_root p q =
    (p_eval (p, 0, q) = p_zero);

(* Determine the numerical type of a real_alg.  The second parameter,
   n : int, is only for LaTeX printing purposes.  In our current LaTeX
   printing uses, we assume the value of $\alpha$ has already been
   printed. *)

fun num_type_of ((p, l, u, q) : real_alg) (pow_to_print : int) =
    let val a_str = if pow_to_print > 1 then
			("\\alpha^" ^ (Int.toString pow_to_print))
		    else "\\alpha"
	val _ = print ("  We shall determine the numerical type of $"
		       ^ a_str ^ "$.\n")
	val _ = print ("  Let $p(x) = " ^ (Algebra.p_toStringLatex p) ^ "$.\n")
	val (t, v) =
	    case q of
		(* Do we already know it's a rational? *)
		SOME q => if Rat.is_integer q then (IsInt, SOME q)
			  else (IsRat, SOME q)
	      (* Else, we must investigate. *)
	      | NONE =>
		let val p = Algebra.p_integral p
		    val qs = possible_rat_roots p
		    (* Filter out rationals outside of [l,u] *)
		    val qs = List.filter (rat_in_intvl l u) qs
		    val _ = print ("     By RRT and the root interval, we reduce the set"
				       ^ " of possible rational values for $" ^ a_str ^ "$ to \n ")
		    val _ = print ("     $\\{" ^
				   (String.concatWith ", " (List.map Rat.toString qs))
				   ^ "\\}$.\n")
		    (* Filter out rationals that aren't roots *)
		    val qs = List.filter (rat_is_root p) qs
		    val _ = if length qs = 0 then
				print "     But none of these are roots of $p(x)$.\n"
			    else ()
		in case qs of
		       [] => (IsReal, NONE)
		     | [q] => if Rat.is_integer q
			      then (IsInt, SOME q) else (IsRat, SOME q)
		     | _ => raise (Useful.Error "num_type_of: unreachable 1")
		end
	val _ = print ((case (t, v) of
			    (IsReal, _) => "  Thus, $" ^ a_str ^ " \\in (\\mathbb{R}\\setminus\\mathbb{Q})"
			  | (IsRat, SOME q) => "  Thus, we see $" ^ a_str ^ " =" ^ (Rat.toString q) ^
					       " \\in (\\mathbb{Q}\\setminus\\mathbb{Z})"
			  | (IsInt, SOME q) => "  Thus, we see $" ^ a_str ^ " =" ^ (Rat.toString q) ^
					       " \\in \\mathbb{Z}"
			  | _ => raise (Useful.Error "num_type_of: unreachable 2"))
		       ^ "$.\n")
    in t end


(* Examples:

open Algebra;
open RealAlg;

val p = [(Rat.one, [(0, 2)]), (Rat.rat_of_int ~2, [])] : poly;
p_toString p;
val it = "x0^2 + -2": string

val cs = r_cell_decomposition [p];

 -- [Begin univariate r-cell decomposition]
     ]-inf, RealRoot(x0^2 + -2, [-2, -1/3])[,
     [RealRoot(x0^2 + -2, [-2, -1/3])],
     ]RealRoot(x0^2 + -2, [-2, -1/3]), RealRoot(x0^2 + -2, [1/3, 2])[,
     [RealRoot(x0^2 + -2, [1/3, 2])]
 -- [End univariate r-cell decomposition]

val cs =
   [LInf
     ([(Rat (true, 1, 1), [(0, 2)]), (Rat (false, 2, 1), [])],
      Rat (false, 2, 1), Rat (false, 1, 3), NONE),
    Alg_pt
     ([(Rat (true, 1, 1), [(0, 2)]), (Rat (false, 2, 1), [])],
      Rat (false, 2, 1), Rat (false, 1, 3), NONE),
    OIntvl
     (([(Rat (true, 1, 1), [(0, 2)]), (Rat (false, 2, 1), [])],
       Rat (false, 2, 1), Rat (false, 1, 3), NONE),
      ([(Rat (true, 1, 1), [(0, 2)]), (Rat (false, 2, 1), [])],
       Rat (true, 1, 3), Rat (true, 2, 1), NONE)),
    Alg_pt
     ([(Rat (true, 1, 1), [(0, 2)]), (Rat (false, 2, 1), [])],
      Rat (true, 1, 3), Rat (true, 2, 1), NONE)]: r_cell list


...BEAUTIFUL!


(FIXED)BUG?:
 SZS status Error for atan-vega-1-weak.tptp
 Exception Non_unique raised by metit program.
  file = atan-vega-1-weak.tptp
  Non_unique "Poly (x0^11 + 41/3 x0^9 + 106/5 x0^7 + -106/5 x0^5 + -41/3 x0^3 + -1 x0) does not have exactly one root in the interval [5/16, 5/8]."

 *Q: This exception is correct (there is no root in that interval) - But why are we looking for one?


open Algebra;
open RealAlg;

(FIXED)BUG: sign_at(x0^2 + -2,RealRoot(x0 + -2, [2, 2])) = ZERO.

Let's investigate...

val p = [(Rat.one, [(0, 2)]), (Rat.rat_of_int ~2, [])] : poly;
p_toString p;
val it = "x0^2 + -2": string

val q = [(Rat.one, [(0, 1)]), (Rat.rat_of_int ~2, [])] : poly;
val alpha = mk_real_alg q (Rat.rat_of_int 2) (Rat.rat_of_int 2) NONE;
sign_at p alpha;
 --> yields ZERO. I think this is because the endpoints are EQUAL.
     Let's refine... (FIXED)
val beta = mk_real_alg q (Rat.rat_of_int 1) (Rat.rat_of_int 2) NONE;
sign_at p beta;
 --> yields POS. So, that's the point. We can't allow equal endpoints.
 (* FIXED! We now recognize l=u in mk_real_alg! *)


val alpha = mk_real_alg p Rat.zero (Rat.rat_of_int 5) NONE;
val alpha =
  ([(Rat (true, 1, 1), [(0, 2)]), (Rat (false, 2, 1), [])],
   Rat (true, 0, 1), Rat (true, 5, 1)): real_alg


val p = [(Rat.one, [(0, 2)]), (Rat.rat_of_int ~2, [])] : poly;
p_toString p;
val it = "x0^2 + -2": string

val alpha = mk_real_alg p Rat.zero (Rat.rat_of_int 5) NONE;
val alpha =
  ([(Rat (true, 1, 1), [(0, 2)]), (Rat (false, 2, 1), [])],
   Rat (true, 0, 1), Rat (true, 5, 1)): real_alg

toString(alpha);
val it = "RealRoot(x0^2 + -2, [0,5])": string

val beta = mk_real_alg p Rat.zero Rat.zero;
Exception-
   NotUnique
  "Poly (x0^2 + -2) does not have exactly one root in the interval [0,0]."
   raised

val beta = mk_real_alg p (Rat.rat_of_int ~2) Rat.zero;
val beta =
   ([(Rat (true, 1, 1), [(0, 2)]), (Rat (false, 2, 1), [])],
    Rat (false, 2, 1), Rat (true, 0, 1)): real_alg

toString(beta);
val it = "RealRoot(x0^2 + -2, [-2,0])": string

val gamma = add(alpha, beta);
val gamma =
   ([(Rat (true, 1, 1), [(0, 3)]), (Rat (false, 8, 1), [(0, 1)])],
    Rat (false, 2, 1), Rat (true, 3, 2)): real_alg

toString(gamma);
val it = "RealRoot(x0^3 + -8 x0, [-2,3/2])": string

val q = [(Rat.one, [(0, 2)]), (Rat.rat_of_int ~3, [])] : poly;
p_toString q;
val it = "x0^2 + -3": string

val sigma = mk_real_alg q (Rat.one) (Rat.rat_of_int 10);
toString sigma;
val it = "RealRoot(x0^2 + -3, [1,10])": string

val gamma = add(alpha, sigma);

val r = [(Rat.one, [(0, 1)])] : poly;
p_toString r;

val beta = real_alg_of_rat (Rat.neg (Rat.rat_of_quotient (~19, 20)));
sign_at p beta;

*)

end
