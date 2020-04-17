(* ======================================================================== *)
(*      A decision procedure for univariate real algebra extended with      *)
(*               predicates for rational and integer powers.                *)
(*                                                                          *)
(* by G.O.Passmore, Aesthetic Integration, London and Clare Hall, Cambridge *)
(* Contact: (e) grant.passmore@cl.cam.ac.uk   (w) www.cl.cam.ac.uk/~gp351/. *)
(* ======================================================================== *)

(* Gamma saturation *)

datatype qi_pred = IntPow of int
                 | RatPow of int
                 | NotIntPow of int
                 | NotRatPow of int;

datatype qi_table = Inconsistent of (qi_pred list)
                  | Consistent of (int * (qi_pred list))
                  | Unknown of qi_pred list;

(* LaTeX-friendly string representations *)

fun qi_pred_to_string' p v =
    let fun x_pow n =
            case n of
                0 => "1"
              | 1 => v
              | n => if n < 9 then
                         (v ^ "^" ^ (Int.toString n))
                     else
                         (v ^ "^{" ^ (Int.toString n) ^ "}")
    in
        case p of
            RatPow n => "(" ^ ((x_pow n) ^ " \\in \\mathbb{Q}") ^ ")"
          | IntPow n => "(" ^ ((x_pow n) ^ " \\in \\mathbb{Z}") ^ ")"
          | NotRatPow n => "(" ^ ((x_pow n) ^ " \\not\\in \\mathbb{Q}") ^ ")"
          | NotIntPow n => "(" ^ ((x_pow n) ^ " \\not\\in \\mathbb{Z}") ^ ")"
    end;

fun qi_pred_to_string p = qi_pred_to_string' p "x";

fun qi_pred_to_string_alpha p = qi_pred_to_string' p "\\alpha";

fun qi_preds_to_string ps =
    String.concatWith " \\wedge " (List.map qi_pred_to_string ps);

(* Comparison of qi_preds, used for sorting.

   Note, as an optimization:

     We want (x^n in Z) to come before (x^n in Q), and
             (x^n not in Q) to come before (x^n not in Z).

   This is to minimize redundant work, and ultimately keep our proof
     output minimal - e.g., if we prove (x^n in Z), then we know (x^n
     in Q) and need not (re-)prove it!  *)

fun cmp_preds (p1,p2) =
    let val f = IntInf.compare
        fun g n m v = if n=m then v else f (n,m)
    in
        case (p1,p2) of
            (IntPow n, IntPow m) => f (n,m)
          | (IntPow n, RatPow m) => g n m LESS
          | (IntPow n, NotIntPow m) => g n m LESS
          | (IntPow n, NotRatPow m) => g n m LESS
          | (RatPow n, IntPow m) => g n m GREATER
          | (RatPow n, RatPow m) => f (n,m)
          | (RatPow n, NotIntPow m) => g n m LESS
          | (RatPow n, NotRatPow m) => g n m GREATER
          | (NotIntPow n, IntPow m) => g n m GREATER
          | (NotIntPow n, RatPow m) => g n m GREATER
          | (NotIntPow n, NotIntPow m) => f (n,m)
          | (NotIntPow n, NotRatPow m) => g n m GREATER
          | (NotRatPow n, IntPow m) => g n m LESS
          | (NotRatPow n, RatPow m) => g n m LESS
          | (NotRatPow n, NotIntPow m) => g n m LESS
          | (NotRatPow n, NotRatPow m) => f (n,m)
    end;

fun sort_preds ps =
    Useful.sort cmp_preds ps;

(* Does d divide n? *)

fun divides d n =
    IntInf.mod (n, d) = 0;

(* qi_pred negation *)

fun not_p p =
    case p of
        IntPow n => NotIntPow n
      | RatPow n => NotRatPow n
      | NotIntPow n => IntPow n
      | NotRatPow n => RatPow n;

(* Does a given d satisfy a Q constraint? *)

fun d_sat_q d p =
    case p of
        RatPow n => divides d n
      | NotRatPow n => not(divides d n)
      | _ => raise Useful.Error
                   ("d_sat_q should only be used upon [Not]RatPow constraints");

(* Given a qi_table, add a new constraint to it, recognizing
   simple explicit inconsistencies *)

fun insert_pred p tbl =
    case tbl of
        Inconsistent ps => Inconsistent (p :: ps)
      | Consistent (d, ps) =>
        if mem (not_p p) ps then Inconsistent (p :: ps)
        else
            (case p of
                 RatPow _ => if d_sat_q d p
                             then Consistent (d, p :: ps)
                             else Unknown (p :: ps)
               | NotRatPow _ => if d_sat_q d p
                                then Consistent (d, p :: ps)
                                else Unknown (p :: ps)
               | _ => Unknown (p :: ps)
            )
      | Unknown ps =>
        if mem (not_p p) ps then Inconsistent (p :: ps)
        else Unknown (p :: ps);

(* Gamma-saturation rules *)

exception NotApplicable of string;

fun trace_i r s =
    ((* print ("[rqi_gamma] : " ^ s ^ "\n"); *)
     r);

fun rule_1 (NotRatPow n) = trace_i (NotIntPow n) "rule_1"
  | rule_1 _  = raise (NotApplicable "rule_1");

fun rule_2 (IntPow n) = trace_i (RatPow n) "rule_2"
  | rule_2 _ = raise (NotApplicable "rule_2");

fun rule_3 (IntPow _, NotIntPow _) = trace_i (NotRatPow 1) "rule_3"
  | rule_3 (NotIntPow _, IntPow _) = trace_i (NotRatPow 1) "rule_3"
  | rule_3 _ = raise (NotApplicable "rule_3");

fun rule_4 (IntPow _, RatPow m) = trace_i (IntPow m) "rule_4"
  | rule_4 (RatPow m, IntPow _) = trace_i (IntPow m) "rule_4"
  | rule_4 _ = raise (NotApplicable "rule_4");

fun rule_5 (IntPow _, NotIntPow m) = trace_i (NotRatPow m) "rule_5"
  | rule_5 (NotIntPow m, NotIntPow _) = trace_i (NotRatPow m) "rule_5"
  | rule_5 _ = raise (NotApplicable "rule_5");

fun set_equal l1 l2 =
    let val s1 = Useful.setify l1
        val s2 = Useful.setify l2
    in
        Useful.subset s1 s2
        andalso
        Useful.subset s2 s1
    end;

fun saturate ps =
    let val old_ps = ref (Useful.setify ps)
        val old_pairs = Groebner.uc_pairs (!old_ps)
        val new_ps = ref ([] : qi_pred list)
        fun app r = map (fn p => new_ps := (r p) :: (!new_ps)
                                 handle _ => ())
        fun one_pass () =
            (new_ps := [];
             app rule_1 (!old_ps);
             app rule_2 (!old_ps);
             app rule_3 old_pairs;
             app rule_4 old_pairs;
             app rule_5 old_pairs;
             List.filter (fn p => not(mem p (!old_ps)))
                         (Useful.setify(!new_ps)))
        val quit = ref false
    in
        (while not(!quit)
               do
               let val new_ps = one_pass ()
               in
                   if new_ps = [] then quit := true
                   else
                       (old_ps := Useful.union new_ps (!old_ps))
               end;
         sort_preds (!old_ps))
    end;

fun preds_to_tbl ps =
    List.foldr (fn (x,xs) => insert_pred x xs) (Unknown []) ps;

fun saturate_tbl ps =
    preds_to_tbl (saturate ps);

fun max_pow ps =
    case (hd (rev (sort_preds ps))) of
        IntPow n => n
      | RatPow n => n
      | NotIntPow n => n
      | NotRatPow n => n;

fun min_ratpow' ps =
    case ps of
        [] => NONE
      | p::ps =>
        (case p of
             RatPow n => SOME n
           | _ => min_ratpow' ps);

fun min_ratpow ps =
    min_ratpow' (sort_preds ps);

fun max_notratpow' ps =
    case ps of
        [] => NONE
      | p::ps =>
        (case p of
             NotRatPow n => SOME n
           | _ => max_notratpow' ps);

fun max_notratpow ps =
    max_notratpow' (rev (sort_preds ps));

fun k1_of ps =
    let fun k1_of' ps v =
            case ps of
                [] => v
              | (RatPow n) :: ps => k1_of' ps n
              | (_ :: ps) => k1_of' ps v
    in
        k1_of' ps 0
    end;

fun k2_of ps =
    let fun k2_of' ps v =
            case ps of
                [] => v
              | (NotRatPow n) :: ps => k2_of' ps n
              | (_ :: ps) => k2_of' ps v
    in
        k2_of' ps 0
    end;

fun k3_of ps =
    let fun k3_of' ps v =
            case ps of
                [] => v
              | (IntPow n) :: ps => k3_of' ps n
              | (_ :: ps) => k3_of' ps v
    in
        k3_of' ps 0
    end;


fun check_q_divisor ps d =
    case ps of
        [] => true
      | (RatPow n)::ps =>
        (divides d n) andalso check_q_divisor ps d
      | (NotRatPow n)::ps =>
        (not(divides d n)) andalso check_q_divisor ps d
      | _::ps => check_q_divisor ps d;

fun search_for_sat_upto ps d =
    let fun search ps c d =
            if c > d then NONE
            else
                if check_q_divisor ps c then
                    SOME c
                else
                    search ps (c+1) d
    in
        case search ps 1 d of
            SOME d => Consistent (d, ps)
          | NONE => Inconsistent ps
    end;

fun check tbl =
    case tbl of
        Unknown ps =>
        let val k1 = k1_of ps
            val k2 = k2_of ps
        in
            if k1 = 0 then
                let val m = max_notratpow ps in
                    (case m of
                         SOME m => Consistent (m, ps)
                       | _ => raise (Useful.Error "gamma_check: unreachable 1"))
                end
            else if k2 = 0 then
                Consistent (1, ps)
            else
                let val b = min_ratpow ps in
                    (case b of
                         SOME b => search_for_sat_upto ps b
                       | _ => raise (Useful.Error "gamma_check: unreachable 2"))
                end
        end
      | _ => tbl;

fun saturate_and_check ps =
    check (saturate_tbl ps);

(* Evaluate a qi_pred at a real algebraic point *)

local open RealAlg
in

(* We now record any qi_pred other facts about alpha we've already
   determined in this run. This keeps us from, e.g., (re-)proving
   (x^n in Q) after we've already proved (x^n in Z). *)

fun eval_p_over_alpha p alpha known_facts =
    let fun a_n_str n = ("\\alpha^" ^ (Int.toString n))
        val _ = print ("  \\item Evaluating $" ^ (qi_pred_to_string_alpha p)
                       ^ "$ for $\\alpha=" ^ (RealAlg.toStringLatex alpha) ^ "$.\n")
        fun pr a n =
            if (n>1) then print ("   Observe $" ^ (a_n_str n)
                                 ^ " = " ^ (RealAlg.toStringLatex a) ^ "$.\n")
            else ()
    in
    case p of
        RatPow n =>
        if mem (IntPow n) known_facts then
            (print ("  But, we've already proven $(" ^ (a_n_str n)
                    ^ " \\in \\mathbb{Z})$ above. Thus, $(" ^ (a_n_str n)
                    ^ " \\in \\mathbb{Q})$.\n");
             true)
        else
            let val a = pow (alpha, n)
                val _ = pr a n
            in
                mem (num_type_of a n) [IsInt, IsRat]
            end
      | IntPow n =>
        let val a = pow (alpha, n)
            val _ = pr a n
        in
            (num_type_of a n) = IsInt
        end
      | NotRatPow n =>
        let val a = pow (alpha, n)
            val _ = pr a n
        in
            (num_type_of a n) = IsReal
        end
      | NotIntPow n =>
        if mem (NotRatPow n) known_facts then
            (print ("  But, we've already proven $(" ^ (a_n_str n)
                    ^ " \\not\\in \\mathbb{Q})$ above. Thus, $(" ^ (a_n_str n)
                    ^ " \\not\\in \\mathbb{Z})$.\n");
             true)
        else
            let val a = pow (alpha, n)
                val _ = pr a n
            in
                mem (num_type_of a n) [IsRat, IsReal]
            end
    end
end;

fun ps_over_alpha_with_known_facts ps alpha known_facts =
    case ps of
        [] => true
      | p :: ps => eval_p_over_alpha p alpha known_facts
                   andalso
                   ps_over_alpha_with_known_facts ps alpha (p :: known_facts);

(* Check SAT of a list of qi_preds over a real algebraic point,
   i.e., over the single point of a 0-cell *)

fun gamma_over_zc ps alpha =
    let val _ = print " \\begin{enumerate}\n"
        val v = ps_over_alpha_with_known_facts ps alpha []
        val _ = print " \\end{enumerate}\n"
    in v end;

fun int_lb q =
    case (Rat.dest_integer (Rat.rounddown q)) of
        SOME i => i
      | NONE => raise (Useful.Error "int_lb: rational not an int!");

fun int_ub q =
    case (Rat.dest_integer (Rat.roundup q)) of
        SOME i => i
      | NONE => raise (Useful.Error "int_ub: rational not an int!");

(* Given two real algebraic numbers alpha and beta, construct a list
   of all integers strictly between alpha and beta. *)

local open RealAlg in
fun all_ints_between alpha beta =
    let fun range x y =
            List.tabulate(y-x+1, fn z => z+x)
        fun r_lt a z =
            sign (add (a, (neg (real_alg_of_rat (Rat.rat_of_int z)))))
            = Sturm.NEG
        fun r_gt a z =
            RealAlg.sign
                (add (a, (neg (real_alg_of_rat (Rat.rat_of_int z)))))
            = Sturm.POS
    in
        case (alpha, beta) of
            ((_, l, _, _), (_, _, u, _)) =>
            let val start_int = int_lb l
                val end_int = int_ub u
            in
                List.filter (fn x => r_lt alpha x andalso r_gt beta x)
                            (range start_int end_int)
            end
    end
end;

(* Form the nth root of an integer as a real algebraic number *)

local open Algebra RealAlg
in
fun nth_root n z =
    let fun f n m =
            (* p = x^n - m *)
            let val p = [(Rat.one, [(0, n)]), (Rat.neg (Rat.rat_of_int m), [])] in
                RealAlg.mk_real_alg p Rat.zero (Rat.rat_of_int m) NONE
            end
    in
        if z >= 0 then
            f n z
        else raise (Useful.Error "Cannot form real nth-root of negative number")
    end
end

(* Check SAT of a list of qi_preds over a 1-cell.
   This must be given the result of gamma saturation as an input *)

local open RealAlg in
fun gamma_over_oc gamma c =
    case gamma of
        Inconsistent _ => false
      | Unknown _ => raise (Useful.Error "gamma_over_oc: unreachable 1")
      | Consistent (d, ps) =>
        let val d_str = Int.toString d in
        (* If ps (Gamma) contains no positive integrality
                constraints, then the consistency of
                (saturate(Gamma))_Q guarantees ps is SAT over c. *)

            if k3_of ps = 0 then
                true
            else
                case c of
                    Alg_pt _ => raise (Useful.Error "gamma_over_oc: unreachable 2")
                  | LInf _ => (print (" Call this r-cell $c$. As $c$ is unbounded towards ${-\\infty}$," ^
                                      " there exist infinitely many primes $p$ s.t. $-p \\in c$ and $-\\sqrt[" ^
                                      d_str ^ "]{p} \\in c$. Let $p$ be such a prime. Then," ^
                                      " it follows by Eisenstein's criterion that $deg(\\sqrt[" ^ d_str ^
                                      "]{p})=" ^ d_str ^ "$. But then $c$ obviously satisfies $\\Gamma$.");
                           true)
                  | RInf _ => (print (" Call this r-cell $c$. As $c$ is unbounded towards ${+\\infty}$," ^
                                      " there exist infinitely many primes $p$ s.t. $p \\in c$ and $\\sqrt[" ^
                                      d_str ^ "]{p} \\in c$. Let $p$ be such a prime. Then," ^
                                      " it follows by Eisenstein's criterion that $deg(\\sqrt[" ^ d_str ^
                                      "]{p})=" ^ d_str ^ "$. But then $c$ obviously satisfies $\\Gamma$.");
                               true)
                  | OIntvl (alpha, beta) =>
                    let val _ = print ("   Call the boundaries of this r-cell $L$ and $U$.\n"
                                       ^ " As $\\Gamma$ contains a positive integrality constraint and"
                                       ^ " $d=" ^ d_str ^"$, any satisfying witness in this"
                                       ^ " r-cell must be of the form $\\sqrt[" ^ d_str ^ "]"
                                       ^ "{z}$ for z an integer in "
                                       ^ "$\\interval[open]{L^" ^ d_str ^ "}{U^" ^ d_str ^ "}$.\n")
                        val alpha_pow_d = pow(alpha, d)
                        val beta_pow_d = pow(beta, d)
                        (* We need to check all integers in ]alpha^d, beta^d[ *)
                        val zs = all_ints_between alpha_pow_d beta_pow_d
                    in if length zs = 0 then
                           (print (" But, there are no integers in this range.\n");
                            false)
                       else
                           let val num_ints = Int.toString (length zs)
                               val z_first = Int.toString (hd zs)
                               val z_last = Int.toString (hd (rev zs))
                               val _ = print (" The set of integers in question is "
                                              ^ "$Z=\\{ z \\in \\mathbb{Z} \\ | \\ " ^ z_first ^ " \\leq z \\leq "
                                              ^ z_last ^ "\\}$, containing "
                                              ^ num_ints ^ " members.\n")
                               val _ = print ("We shall examine $\\sqrt[" ^ d_str
                                              ^ "]{z}$ for each $z \\in Z$ in turn.\n")
                               (* Note: The use of abs here is sound by symmetry
                                 and the fact that r-cells don't contain zero *)
                               val rs = List.map (fn x => nth_root d (abs x)) zs
                               val w = List.find (gamma_over_zc ps) rs
                           in
                               case w of
                                   SOME alpha => (print ("Witness found: $" ^ (toStringLatex alpha) ^ "$.\n");
                                                  true)
                                 | NONE => false
                           end
                    end
        end
end;

(* Midpoint of two rationals a, b *)

fun rat_mid a b =
    Rat.mult (Rat.add(a, b), Rat.inv (Rat.rat_of_int 2));

(* Main decision method for existential formulas.  We currently work
   on conjunctions of the form Phi /\ Gamma, where Phi is a formula of
   univariate real algebra, and Gamma is a system of rationality and
   integrality constraints. *)

local open RealAlg MTAlgebra in
fun check_r_cell_alg (phi : Formula.formula) (c : r_cell) =
    case phi of
        Formula.True => true
      | Formula.False => false
      | phi =>
        (case c of
             Alg_pt alpha => eval_fm_at_sp phi alpha false
           | LInf alpha =>
             let val (_, l, _, _) = alpha
                 val sp = real_alg_of_rat l
             in
                 eval_fm_at_sp phi sp false
             end
           | RInf alpha =>
             let val (_, _, u, _) = alpha
                 val sp = real_alg_of_rat u
             in
                 eval_fm_at_sp phi sp false
             end
           | OIntvl (alpha, beta) =>
             let val ((_, _, u1, _), (_, l2, _, _)) = (alpha, beta)
                 val sp = if (Rat.lt (u1, l2)) then
                              real_alg_of_rat (rat_mid u1 l2)
                          else raise (Useful.Error "check_r_cell: u1 must be less than l2")
             in
                 eval_fm_at_sp phi sp false
             end)
end;

(* Check Gamma, a system of rationality and integrality constraints,
   over an r_cell *)

local open RealAlg in
fun check_r_cell_qi (gamma : qi_pred list) (c : r_cell) =
    let val gamma' = saturate_and_check gamma in
        case gamma' of
            Inconsistent _ => false
          | Unknown _ => raise (Useful.Error "check_r_cell_qi: unreachable")
          | Consistent (d, ps) =>
            (case c of
                 Alg_pt alpha => gamma_over_zc ps alpha
               | _ => gamma_over_oc gamma' c)
    end
end;

(* Print \varphi (univariate RCF formula) in a LaTeX-friendly way *)

fun atom_str ((reln, [x, y]) : Atom.atom) =
    let val reln =
            case reln of
                ">=" => "\\geq"
              | "<=" => "\\leq"
              | _ => reln
    in
        "(" ^ (Term.toString x) ^ " " ^ reln ^ " " ^ (Term.toString y) ^ ")"
    end
  | atom_str _ = raise Useful.Error "atom_str: atom's reln must be binary";

local open Formula
in
  fun fml_str False = "False"
    | fml_str True  = "True"
    | fml_str (Atom a) = atom_str a
    | fml_str (Not p)  = "\\neg " ^ (fml_str p)
    | fml_str (And(p,q)) = "(" ^ (fml_str p) ^ " \\wedge " ^ (fml_str q) ^ ")"
    | fml_str (Or(p,q))  = "(" ^ (fml_str p) ^ " \\vee " ^ (fml_str q) ^ ")"
    | fml_str (Imp(p,q)) = "(" ^ (fml_str p) ^ " \\Rightarrow " ^ (fml_str q) ^ ")"
    | fml_str (Iff(p,q)) = "(" ^ (fml_str p) ^ " \\iff " ^ (fml_str q) ^ ")"
    | fml_str (Forall(x,p)) = fml_qquant "\\forall" (x,p)
    | fml_str (Exists(x,p)) = fml_qquant "\\exists" (x,p)
  and fml_qquant qname (x,p) = "(" ^ qname ^ " " ^ (Name.toString x) ^ " " ^ (fml_str p) ^ ")"
end;

(* Nice string printing of cardinals for 0..9,
   defaulting to Int.toString for the rest (laziness) *)

fun spell_num n =
    case n of
        0 => "zero"
      | 1 => "one"
      | 2 => "two"
      | 3 => "three"
      | 4 => "four"
      | 5 => "five"
      | 6 => "six"
      | 7 => "seven"
      | 8 => "eight"
      | 9 => "nine"
      | _ => Int.toString n;

(* Main decision procedure for Exists x. Phi(x) /\ Gamma(x). *)

exception UnsatByGammaC;

local open MTAlgebra RealAlg in
fun decide_exists (phi : Formula.formula, gamma : qi_pred list) =
    let val _ = print "\nLet us decide $\\exists x (\\varphi(x) \\wedge \\Gamma(x))$, where\n"
        val _ = print (" \\[ \\varphi = \\isa{" ^ (fml_str phi) ^ "} \\ \\textnormal{ and } \\ \n")
        val _ = print ("   \\Gamma = " ^ (qi_preds_to_string gamma) ^ ".\\]\n")
        val _ = print ("\n\\noindent We first compute $\\clgamma$, the closure of $\\Gamma$ under"
                           ^ " the saturation rules:\n")
        val clgamma = saturate_and_check gamma
        val _ = case clgamma of Inconsistent ps =>
                                (print ("  \\[\\clgamma = " ^ (qi_preds_to_string ps) ^ ".\\]\n");
                                 raise UnsatByGammaC)
                              | Consistent (d, ps) =>
                                (print ("  \\[\\clgamma = " ^ (qi_preds_to_string ps) ^ ".\\]\n");
                                 print ("  Observe $\\mathcal{D}(\\clgamma_{\\mathbb{Q}})$ is satisfied "
                                        ^ "(minimally) by $d="
                                        ^ (Int.toString d) ^ "$.\n")
                                )
                              | Unknown _  => raise (Useful.Error "decide_exists: unreachable 1")
        val vh = mk_vv_ht 10
        val polys = polys_of_fm (vh, phi)
        val _ = print ("\nWe next compute an r-cell decomposition of $\\mathbb{R}$ induced by"
                       ^ " $\\varphi$, yielding:\n")
        val cs = r_cell_decomposition polys
        (* We must filter out r_cells that don't satisfy phi *)
        val cs' = List.filter (check_r_cell_alg phi) cs
        val _ = if length cs' < length cs then
                    (print ("\\noindent By IVT, $\\varphi$ has constant truth value over each such r-cell." ^
                            " Only " ^ (spell_num (length cs'))
                            ^ (if length cs' > 1 then " r-cells" else " r-cell")
                            ^ " in the decomposition "
                            ^ (if length cs' > 1 then " satisfy" else " satisfies")
                            ^ " $\\varphi$:\n\n  ");
                     print (String.concatWith ",\n  " (List.map r_cell_to_string cs'));
                     print ".\n"
                    )
                else ()
    in
        case cs' of
            [] => false (* No r_cells satisfy Phi. Thus, purely from the
                           univariate real algebra part of the formula,
                           we have unsatisfiability *)

          | cs  =>
            let val _ = print "\n\\noindent Let us now see if any of these r-cells satisfy $\\Gamma$.\n"
                val _ = print "\\begin{enumerate}\n"
                val v = List.exists
                            (fn c => (print (" \\item We check if "
                                             ^ (r_cell_to_string c)
                                             ^ " satisfies $\\Gamma$.\n");
                                      let val v = (check_r_cell_qi gamma c)
                                          val _ = if v then (print " So, the r-cell does satisfy $\\Gamma$.\n")
                                                  else (print " So, the r-cell does not satisfy $\\Gamma$.\n")
                                      in v end))
                            cs
                val _ = print "\\end{enumerate}\n"
                val _ = if v then print "Thus, the conjecture is true. \\qed\n\n\n"
                        else print "Thus, as all r-cells have been ruled out, the conjecture is false. \\qed\n\n"
            in
                v
            end
    end
    handle UnsatByGammaC => (print "But, $\\clgamma$ is obviously inconsistent.\n";
                             print "Thus, the conjecture is false. \\qed\n\n";
                             false)
end;

(* Examples:

saturate_tbl [RatPow 2, NotRatPow 3];

saturate_tbl [RatPow 2, NotRatPow 3, RatPow 6];

saturate_tbl [RatPow 4, IntPow 5, NotIntPow 4];

saturate_tbl [RatPow 4, IntPow 5, NotIntPow 4, NotIntPow 25, RatPow 6];

saturate_and_check [RatPow 2, RatPow 5];

saturate_and_check [RatPow 2, RatPow 5, NotIntPow 2];

saturate_and_check [RatPow 2, RatPow 5, NotIntPow 2, NotRatPow 4];

saturate_and_check [RatPow 2, NotRatPow 1, RatPow 5];

saturate_and_check [RatPow 2, NotRatPow 1, RatPow 6];

*)

(* local open Algebra RealAlg in *)

(*  val sac = saturate_and_check; *)
(*  val p = [(Rat.one, [(0, 2)]), (Rat.rat_of_int ~2, [])] : poly; *)
(*  val alpha = mk_real_alg p Rat.zero (Rat.rat_of_int 5) NONE; *)
(*  val e1 = gamma_over_zc ([IntPow 2, NotRatPow 1, IntPow 4]) alpha; *)
(*  val e2 = gamma_over_zc ([IntPow 2, NotRatPow 1, IntPow 4, NotIntPow 6]) alpha; *)
(*  val e3 = gamma_over_zc ([IntPow 2, NotRatPow 1, IntPow 4, NotIntPow 11]) alpha; *)
(*  val e4 = gamma_over_oc (sac [IntPow 2, NotRatPow 1]) (OIntvl (alpha, add(alpha, alpha)));  *)
(*  val e5 = gamma_over_oc (sac [NotIntPow 2, NotRatPow 1]) (OIntvl (alpha, add(alpha, alpha)));  *)
(*  val e6 = gamma_over_oc (sac [IntPow 3, NotIntPow 2, NotRatPow 1]) (OIntvl (alpha, add(alpha, alpha)));  *)

(*  val e7 = decide_exists (Formula.Atom ("=", [Term.Fn("-", [Term.Fn("*", [Term.Fn("x", []), Term.Fn("x", [])]), *)
(*                                                            Term.Rat(Rat.rat_of_int 2)]), *)
(*                                              Term.Rat(Rat.zero)]), *)
(*                         [IntPow 2]); *)

(*  val e8 = decide_exists (Formula.Atom ("=", [Term.Fn("-", [Term.Fn("*", [Term.Fn("x", []), Term.Fn("x", [])]), *)
(*                                                            Term.Rat(Rat.rat_of_int 2)]), *)
(*                                              Term.Rat(Rat.zero)]), *)
(*                         [RatPow 1]); *)

(*  val e9 = decide_exists (Formula.Atom ("=", [Term.Fn("-", [Term.Fn("*", [Term.Fn("x", []), Term.Fn("x", [])]), *)
(*                                                            Term.Rat(Rat.rat_of_int 2)]), *)
(*                                              Term.Rat(Rat.zero)]), *)
(*                         [RatPow 2]); *)

(* end; *)

(*
open Algebra;
open RealAlg;

(* Problem 1: Exists x. (x^2 - 2 = 0 /\ (x in Q)) *)

let val tm_x = Term.Fn("x", [])
    val tm_two = Term.Rat (Rat.rat_of_int 2)
    val tm_zero = Term.Rat Rat.zero
    val tm_p = Term.Fn("-", [Term.Fn("^", [tm_x, tm_two]), tm_two])
in
    decide_exists (Formula.Atom ("=", [tm_p, tm_zero]),
                   [RatPow 1])
end;

(* Problem 2: Exists x. (x^3 in Z, x^5 not in Z, x in Q). *)

local open Algebra RealAlg in
 val p3 = decide_exists (Formula.True,
                         [IntPow 3, NotIntPow 5, RatPow 1]);
end;


(* Problem 3 *)

let val tm_x = Term.Fn("x", [])
    val tm_two = Term.Rat (Rat.rat_of_int 2)
    val tm_three = Term.Rat (Rat.rat_of_int 3)
    val tm_seven = Term.Rat (Rat.rat_of_int 7)
    val tm_fifty = Term.Rat (Rat.rat_of_int 50)
    val tm_zero = Term.Rat Rat.zero
    val tm_p1 = Term.Fn("-", [Term.Fn("^", [tm_x, tm_three]), tm_seven])
    val tm_p2 = Term.Fn("+", [Term.Fn("^", [tm_x, tm_two]), Term.Rat Rat.one])
in
    decide_exists (Formula.And
                       (Formula.Atom (">", [tm_p1,
                                             tm_three]),
                        (Formula.Atom ("<", [tm_p2,
                                             tm_fifty]))),
                   [NotRatPow 2, IntPow 3])
end;


(* Problem 4: Exists x. (x>3 /\ x^2 + 2x - 1 >= 0 /\ (x^5 \not\in Q) /\ (x^6 \in \mathbb{Z}) *)


let val tm_x = Term.Fn("x", [])
    val tm_one = Term.Rat Rat.one
    val tm_two = Term.Rat (Rat.rat_of_int 2)
    val tm_three = Term.Rat (Rat.rat_of_int 3)
    val tm_four = Term.Rat (Rat.rat_of_int 4)
    val tm_zero = Term.Rat Rat.zero
    val tm_p1 = Term.Fn("-", [Term.Fn("^", [tm_x, tm_two]), Term.Fn("*", [tm_two, tm_x])])
    val tm_p2 = Term.Fn("+", [Term.Fn("^", [tm_x, tm_four]),
                              tm_one])
in
    decide_exists (Formula.And (Formula.Atom (">", [tm_x, tm_three]),
                                (Formula.Atom (">=", [tm_p1,
                                                      tm_zero]))),
                   [NotRatPow 3, NotRatPow 5, IntPow 6])
end;



(* Problem 4: Exists x. (x^4 - 10x^2 + 1 = 0 /\ x > 1 /\ x \in Q). *)

let val tm_x = Term.Fn("x", [])
    val tm_two = Term.Rat (Rat.rat_of_int 2)
    val tm_zero = Term.Rat Rat.zero
    val tm_p = Term.Fn("-", [Term.Fn("^", [tm_x, tm_two]), tm_two])
in
    decide_exists (Formula.Atom ("=", [tm_p, tm_zero]),
                   [RatPow 1])
end;


*)


(* Problem 5 *)


(* let val tm_x = Term.Fn("x", []) *)
(*     val tm_two = Term.Rat (Rat.rat_of_int 2) *)
(*     val tm_three = Term.Rat (Rat.rat_of_int 3) *)
(*     val tm_seven = Term.Rat (Rat.rat_of_int 7) *)
(*     val tm_zero = Term.Rat Rat.zero *)
(*     val tm_p1 = Term.Fn("-", [Term.Fn("^", [tm_x, tm_three]), tm_seven]) *)
(*     val tm_p2 = Term.Fn("+", [Term.Fn("^", [tm_x, tm_two]), Term.Rat Rat.one]) *)
(* in *)
(*     decide_exists (Formula.And  *)
(*                     (Formula.Atom (">=", [tm_p1, *)
(*                                           tm_three]), *)
(*                      (Formula.Atom ("<", [tm_p2, *)
(*                                           tm_zero]))), *)
(*                 [NotRatPow 2, IntPow 3]) *)
(* end; *)
