(* ======================================================================== *)
(*       Connection between MetiTarski formulas and polynomial algebra      *)
(*                                                                          *)
(* by G.O.Passmore, Cambridge Computer Laboratory and LFCS, Edinburgh, 2011 *)
(* Contact: (e) grant.passmore@cl.cam.ac.uk   (w) www.cl.cam.ac.uk/~gp351/. *)
(* ======================================================================== *)

structure MTAlgebra : MTAlgebra =
struct

open Algebra;

(* Note: We use integers for our variables instead of strings as in
   Term.Fn("x",[]).  Because of this, we will need a mapping between
   strings and ints, to translate between ``vars'' in MT polynomials
   and vars in our canonical form polynomials.  We use a hash-table
   for this translation (see type mt_var_vid_ht).

   Crucially, our variable ordering is setup so that that v_i > v_j
   iff i < j, where v_i is the variable with var_id i.
   So, v_0 > v_1 > v_2, ..., etc.

   This makes it easy for us to add new variables on the fly (e.g., as
   in our Tiwari-style GB-based Real Nullstellensatz search procedure)
   with the new variables being smaller in the active ordering, making
   it possible for GB reductions to project upon them.

   For monomials, we store power-products with their var-power pairs
   in ascending order w.r.t. the variable ordering.  This means that
   the numerical var_id's in power-products will be descending, since
   these var_id's correspond to the subscripts of variables.

   This is done for efficiency reasons, to allow us to easily compute
   the graded reverse lexicographic ordering on monomials, without
   needed to perform a list reverse operation before each
   comparison. *)

type mt_var_vid_ht = (string, var_id) Polyhash.hash_table;

(* Given an MT var string, get its corresponding var_id *)

fun var_id_of (vh : mt_var_vid_ht, v) =
    case Polyhash.peek vh v of
        SOME vid => vid
      | NONE => let val vid = Polyhash.numItems(vh)
                    val _ = Polyhash.insert vh (v, vid)
                in vid end;

(* Given a var_id, return a polynomial consisting just of it *)

fun poly_of_var_id (v : var_id) = [(Rat.one, [(v, 1)])] : poly;

(* No underscores in our variable strings *)

val nou = String.translate (fn c => if c = #"_" then "" else str c);

(* Expand a polynomial p^n into sum of monomials normal form *)

fun expand_p_exp' (p : Algebra.poly, n : int, r : Algebra.poly) =
    if n < 0 then
        raise Useful.Error
                  "Algebraic polynomials may have only natural number exponents."
    else if n = 0 then r
    else expand_p_exp' (p, n - 1, p_mult(r, p));

fun expand_p_exp (p : Algebra.poly, n : int) =
    expand_p_exp' (p, n, Algebra.p_one);

(* Convert a MT polynomial term into canonical sparse
   sum of monomials form.  Note, we handle also variables
   of form Term.Var here, due to the fact that these can
   actually be later existentially quantified by MT when
   handed to CAD. *)

fun poly_of_tm (vh : mt_var_vid_ht, tm) =
    case tm of
        Term.Rat q => poly_of_rat(q)
      | Term.Fn(s, []) => poly_of_var_id(var_id_of(vh, nou s))
      | Term.Var(s) => poly_of_var_id(var_id_of(vh, "V" ^ nou s))
      | Term.Fn("+", [x, y]) => p_sum ((poly_of_tm(vh, x)), (poly_of_tm(vh, y)))
      | Term.Fn("-", [x, y]) => p_sub ((poly_of_tm(vh, x)), (poly_of_tm(vh, y)))
      | Term.Fn("-", [x]) => p_neg (poly_of_tm(vh, x))
      | Term.Fn("*", [x, y]) => p_mult ((poly_of_tm(vh, x)), (poly_of_tm(vh, y)))
      | Term.Fn("^", [x, Term.Rat n]) =>
        (case Rat.dest_integer n of
	     SOME i => expand_p_exp ((poly_of_tm(vh, x)), IntInf.toInt i)
           | NONE => raise Useful.Error "Cannot convert Term to SM poly: non-integral exponent.")
      | _ => raise Useful.Error "Cannot convert Term to SM poly.";

(* Setup hash table for MT<->SM var string / var id conversion *)

exception VAR_ID_NOT_FOUND;

fun mk_vv_ht (n) : mt_var_vid_ht =
    Polyhash.mkTable (Polyhash.hash_string, (op =))
                     (n, VAR_ID_NOT_FOUND);

(* Extract SM polynomial from MT atom *)

fun poly_of_atom (vh : mt_var_vid_ht, a : Atom.atom) =
    case a of
        (_, [x, y]) => p_sub(poly_of_tm(vh, x), poly_of_tm(vh, y))
      | _ => raise Useful.Error "Unsupported atom in MTAlg.";

(* Extract list of SM polynomials from MT Formula *)

fun polys_of_fm (vh : mt_var_vid_ht, fm : Formula.formula) =
    case fm of
        Formula.Atom a => [poly_of_atom(vh, a)]
      | Formula.Not f => polys_of_fm(vh, f)
      | Formula.And (f, f') => Useful.union (polys_of_fm(vh, f))
                                            (polys_of_fm(vh, f'))
      | Formula.Or(f, f') => Useful.union (polys_of_fm(vh, f))
                                          (polys_of_fm(vh, f'))
      | Formula.Imp(f, f') => Useful.union (polys_of_fm(vh, f))
                                           (polys_of_fm(vh, f'))
      | Formula.Iff(f, f') => Useful.union (polys_of_fm(vh, f))
                                           (polys_of_fm(vh, f'))
      | Formula.Forall(_, f) => polys_of_fm(vh, f)
      | Formula.Exists(_, f) => polys_of_fm(vh, f)
      | _ => [];

(* Given a quantifier-free univariate MetiTarski formula F and a real
   algebraic number alpha, decide the truth of F at alpha. *)

fun eval_fm_at_sp (fm : Formula.formula) (alpha : RealAlg.real_alg) (print_log : bool) =
    let fun eval_atom_at_sp a alpha vh =
            let val p = poly_of_atom (vh, a)
                val s' = RealAlg.sign_at p alpha
                val s'_str = case s' of
                                 Sturm.NEG => "NEG"
                               | Sturm.POS => "POS"
                               | Sturm.ZERO => "ZERO"
                val _ = if print_log then
                            print (" -- sign_at(" ^ (Algebra.p_toString p) ^ ", " ^ (RealAlg.toString alpha) ^ ") = " ^ s'_str ^ ".\n")
                        else ()
            in case a of
                   (">=", _) => s' = Sturm.POS orelse s' = Sturm.ZERO
                 | (">", _) => s' = Sturm.POS
                 | ("=", _) => s' = Sturm.ZERO
                 | ("<", _) => s' = Sturm.NEG
                 | ("<=", _) => s' = Sturm.NEG orelse s' = Sturm.ZERO
                 | _ => raise Useful.Error ("eval_atom_at_sp: Cannot evaluate atom: "
                                            ^ Atom.toString a)
            end
        fun eval_fm_at_sp' fm alpha vh =
            case fm of
                Formula.True => true
              | Formula.False => false
              | (Formula.Atom a) => eval_atom_at_sp a alpha vh
              | (Formula.And (fm1, fm2)) =>
                (eval_fm_at_sp' fm1 alpha vh) andalso (eval_fm_at_sp' fm2 alpha vh)
              | (Formula.Or (fm1, fm2)) =>
                (eval_fm_at_sp' fm1 alpha vh) orelse (eval_fm_at_sp' fm2 alpha vh)
              | (Formula.Imp (fm1, fm2)) =>
                (eval_fm_at_sp' (Formula.Or (Formula.Not fm1, fm2)) alpha vh)
              | (Formula.Not fm1) =>
                not (eval_fm_at_sp' fm1 alpha vh)
              | _ => raise Useful.Error ("eval_fm_at_sp: Cannot evaluate formula: "
                                         ^ Formula.toString fm)
        val vh = mk_vv_ht 10
        val result = eval_fm_at_sp' fm alpha vh
        val _ = if print_log then
                    (print (" -- Evaluation of Formula.formula upon a RealAlg.real_alg:\n");
                     print ("    Formula: " ^ (Formula.toString fm) ^ "\n");
                     print ("      alpha: " ^ (RealAlg.toString alpha) ^ "\n");
                     print ("        aka: " ^ (RealAlg.toIsabelleString alpha) ^ "\n");
                     print ("     Result: " ^ (Bool.toString result) ^ "\n"))
                else ()
    in result end;

end
