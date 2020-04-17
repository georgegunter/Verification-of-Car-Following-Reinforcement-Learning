
(* ========================================================================= *)
(* POLYNOMIAL OPERATIONS *)
(* ========================================================================= *)

structure Poly :> Poly =
struct

(*Set to false for problems containing existential variables to be solved.
  Then non-ground formulas are open to simplification, even using QEPCAD.
  This greatly harms performance on purely universal problems.*)
val ground_only = ref true;

open Useful Term;

(* ------------------------------------------------------------------------------- *)
(* Basic arithmetic operations on Metis canonical polynomials.                     *)
(* ------------------------------------------------------------------------------- *)

fun is_natural (Rat r) =
      let val (p,q) = Rat.quotient_of_rat r
      in p>=0 andalso q=1 end
  | is_natural _ = false;

fun isInt n (Rat r) =
      let val (p,q) = Rat.quotient_of_rat r
      in p=n andalso q=1 end
  | isInt _ _ = false;

fun mk_sum (s,t) = Fn("+",[s,t]);
fun mk_prod (s,t) = Fn("*",[s,t]);
fun mk_quo (s,t) = Fn("/",[s,t]);

val zero = Term.Rat (Rat.rat_of_int 0);
val one =  Term.Rat (Rat.rat_of_int 1);
val minusone =  Term.Rat (Rat.rat_of_int ~1);

(*Preserves the order of the factors*)
fun list_prod [] = one
  | list_prod ts =
      let val x::xs = rev ts
      in  List.foldl mk_prod x xs  end;

fun eval_term (Fn (f,ts)) = eval_Fn (f, map eval_term ts)
  | eval_term t = t;

(*This ordering serves to identify non-algebraic terms, which will be regarded as variables
  for the canonical form construction. In particular, we wish the most complex term to be dominant.
  This will cause that term to be isolated, and therefore given priority in the proof process.
  Quotients are maximal in this ordering: we wish to isolate them first in the hope that
  the denominator will be either positive or negative but never cross zero. *)

val kboCmp = KnuthBendixOrder.compare KnuthBendixOrder.default;

fun priority_aux x y =
  case kboCmp (x,y) of
      NONE => Term.compare (x,y)  (*Why first KBO? To isolate log and exp, with their big weights*)
    | SOME c => c;

(*In the Horner normal form transformation, we take quotients as greater than special functions.
  Therefore, a quotient is more likely to be the outermost "variable" to be isolated.
  The reverse orientation was intended, and the existing one introduced accidentally,
  but this approach improves the success rate by 3%.*)
fun priority x y =
  case (x,y) of
      (Fn("/",_), Fn("/",_)) => priority_aux x y
    | (Fn("/",_), Fn(_,[_])) => GREATER
    | (Fn(_,[_]), Fn("/",_)) => LESS
    | _ => priority_aux x y;

fun horner_atom x = Fn ("+",[zero, Fn("*",[x, one])]);

fun horner_add pol1 pol2 =
  if isInt 0 pol1 then pol2
  else if isInt 0 pol2 then pol1
  else
  case (pol1,pol2) of
      (Fn("+",[c, Fn("*",[x, p])]),
       Fn("+",[d, Fn("*",[y, q])])) =>
	    (case priority x y of
		GREATER => horner_cadd pol2 pol1
	      | LESS    => horner_cadd pol1 pol2
	      | EQUAL   =>
		  let val cd = horner_add c d
		      val pq = horner_add p q
		  in if Term.equal zero pq then cd
		     else Fn("+",[cd, Fn("*",[x, pq])])
		  end)
      | (_, Fn("+",_)) => horner_cadd pol1 pol2
      | (Fn("+",_), pol2) => horner_cadd pol2 pol1
      | (Rat r1, Rat r2) => Term.Rat (Rat.add(r1,r2))
      | _ => raise Bug ("horner_add: " ^ Term.toString pol1 ^ ", " ^ Term.toString pol2)
and horner_cadd pol1 (Fn("+",[d, e])) =
                Fn("+",[horner_add pol1 d, e]);

fun horner_neg (Fn("+", [c, Fn("*",[d, p])])) =
      Fn("+", [horner_neg c, Fn("*",[d, horner_neg p])])
  | horner_neg (Rat r) = Term.Rat (Rat.neg r)
  | horner_neg t = raise Bug ("horner_neg: t = " ^ Term.toString t);

fun horner_sub p q = horner_add p (horner_neg q);

fun horner_mul pol1 pol2 =
  if isInt 0 pol1 then zero
  else if isInt 0 pol2 then zero
  else
  case (pol1,pol2) of
      (Fn("+",[c, Fn("*",[x, p])]),
       Fn("+",[_, Fn("*",[y, _])])) =>
           if Term.equal zero c andalso Term.equal one p andalso Term.equal x y
           then Fn("+", [c, Fn("*",[x, pol2])])
           else
	      (case priority x y of
		  GREATER => horner_cmul pol2 pol1
		| _ => horner_cmul pol1 pol2)
    | (_,Fn("+",_)) => horner_cmul pol1 pol2
    | (Fn("+",_),_) => horner_cmul pol2 pol1
    | (Rat r1, Rat r2) => Term.Rat (Rat.mult(r1,r2))
    | _ => raise Bug ("horner_mult: " ^ Term.toString pol1 ^ ", " ^ Term.toString pol2)
and horner_cmul pol1 (Fn("+",[d, Fn("*",[y, q])])) =
      horner_add (horner_mul pol1 d)
		 (Fn("+",[zero,
			  Fn("*", [y, horner_mul pol1 q])]))
  | horner_cmul pol1 pol2 = raise Bug ("horner_cmul: pol1 = " ^ Term.toString pol1 ^ "  pol2 = " ^ Term.toString pol2);

fun horner_pow p n =
  if n > 0 then funpow n (horner_mul p) one
  else if n = 0 then one
  else horner_atom (eval_Fn("/",[one, horner_pow p (~n)]));

(* ------------------------------------------------------------------------- *)
(* Convert Metis term into canonical polynomial representative.              *)
(* ------------------------------------------------------------------------- *)

fun metis_poly_term tm =
  case tm of
    Rat _    => tm  (*rational number*)
  | Fn(_,[]) => horner_atom tm  (*Skolemized variable*)
  | Fn("^",[s,t]) =>
      let val t' = eval_term t
      in
	 case Rat.dest_integer (Term.destRat t') handle Error _ => NONE of
	    SOME n => horner_pow (metis_poly_term s) (IntInf.toInt n)
	  | NONE => horner_atom (Fn("^",[s,t']))
      end
  | Fn("/",[s,t]) => horner_div (metis_poly_term s) (metis_poly_term t)
  | Fn("*",[s,t]) => horner_mul (metis_poly_term s) (metis_poly_term t)
  | Fn("+",[s,t]) => horner_add (metis_poly_term s) (metis_poly_term t)
  | Fn("-",[s,t]) => horner_sub (metis_poly_term s) (metis_poly_term t)
  | Fn("-",[t]) => horner_neg (metis_poly_term t)
  | _ => horner_atom tm
and horner_div s (Fn("-",[t])) = horner_div (Fn("-",[s])) t
  | horner_div s (Rat r) =
      if Rat.eq (r, Rat.zero) then zero (*division by zero yields zero!*)
      else horner_mul (metis_poly_term s) (Term.Rat (Rat.inv r)) (* the product s*(1/n) *)
  | horner_div s t =
      if isInt 0 s then zero
      else horner_atom (Fn("/",[s,t]));

(* ------------------------------------------------------------------------- *)
(* Do likewise for Metis atom so the RHS is zero.                            *)
(* ------------------------------------------------------------------------- *)

fun simp_mk_neg (Fn ("+",[s,t])) = eval_Fn ("+",[simp_mk_neg s, simp_mk_neg t])
  | simp_mk_neg (Fn ("*",[s,t])) = eval_Fn ("*",[s, simp_mk_neg t])  (*coeff is in t*)
  | simp_mk_neg t = eval_Fn ("-",[t])

fun simp_mk_prod (t, u) = if isInt 1 u then t else eval_Fn("*", [t, u]);

(*Products are nested to the right, with any rational coefficient innermost.
  In that way, the dominant factor will be the popular operand.*)
fun arith_simplify_product_rat (r, t) =
  if Rat.eq (r, Rat.one) then t
  else
  case t of
      Rat r' => Term.Rat (Rat.mult (r,r'))
    | Fn ("*",[t1,t2]) => simp_mk_prod (t1, arith_simplify_product_rat (r, t2))
    | _ => simp_mk_prod (t, Term.Rat r);

(**)
fun arith_simplify_product (Rat r, u) = arith_simplify_product_rat (r, u)
  | arith_simplify_product (Fn("*",[t1,t2]), u) = simp_mk_prod (t1, arith_simplify_product (t2, u))
  | arith_simplify_product (t,u) = simp_mk_prod (t,u);

fun is_special_function f = not (mem f ["+","-","*","/","abs"]);

fun is_pi (Fn("pi",[])) = true
 |  is_pi _ = false;

fun is_int_mult_of_pi (Fn("*",[Rat r,t])) =
             Rat.is_integer r andalso is_pi t
 |  is_int_mult_of_pi (Fn("*",[t,Rat r])) =
             Rat.is_integer r andalso is_pi t
 |  is_int_mult_of_pi _ = false;

fun is_odd_int_mult_of_pi (Fn("*",[Rat r,t])) =
             Rat.is_odd_integer r andalso is_pi t
 |  is_odd_int_mult_of_pi (Fn("*",[t,Rat r])) =
             Rat.is_odd_integer r andalso is_pi t
 |  is_odd_int_mult_of_pi _ = false;

fun is_even_int_mult_of_pi (Fn("*",[Rat r,t])) =
             Rat.is_even_integer r andalso is_pi t
 |  is_even_int_mult_of_pi (Fn("*",[t,Rat r])) =
             Rat.is_even_integer r andalso is_pi t
 |  is_even_int_mult_of_pi _ = false;

(*Simplify 0+t = t, s+0 = s, s*0 = 0, s*1 = s, etc.  Also, constant folding for terms.*)
fun arith_simplify_term (Fn ("+",[s,t])) =
      let val (s', t') = (arith_simplify_term s, arith_simplify_term t)
      in
	if isInt 0 s' then t'
	else
	if isInt 0 t' then s'
	else eval_Fn ("+",[s',t'])
      end
  | arith_simplify_term (Fn ("-",[s,t])) =
      let val (s', t') = (arith_simplify_term s, arith_simplify_term t)
      in
	if isInt 0 s' then eval_Fn ("-",[t'])
	else
	if isInt 0 t' then s'
	else eval_Fn ("-",[s',t'])
      end
  | arith_simplify_term (Fn ("-",[t])) = (*unary minus*)
     (case arith_simplify_term t of
          (Fn ("-",[t'])) => t'
        | t' => eval_Fn ("-",[t']))
  | arith_simplify_term (Fn ("*",[s,t])) =
      let val (s', t') = (arith_simplify_term s, arith_simplify_term t)
      in
	if isInt 0 s' orelse isInt 0 t' then zero
	else arith_simplify_product (s',t')
      end
  | arith_simplify_term (Fn ("/",[s,t])) =
      let val (s', t') = (arith_simplify_term s, arith_simplify_term t)
      in
	if isInt 1 t' then s'
	else eval_Fn ("/",[s',t'])
      end
  | arith_simplify_term (Fn ("^",[s,t])) =
      let val (s', t') = (arith_simplify_term s, arith_simplify_term t)
      in
	if isInt 1 t' then s'
	else eval_Fn ("^",[s',t'])
      end
  | arith_simplify_term (Fn ("sin",[t])) =
      let val t' = arith_simplify_term (metis_poly_term t) in
      if isInt 0 t' then zero
      else if is_pi t' orelse is_int_mult_of_pi t' then zero
      else Fn ("sin",[t'])
      end
  | arith_simplify_term (Fn ("cos",[t])) =
      let val t' = arith_simplify_term (metis_poly_term t) in
      if isInt 0 t' orelse is_even_int_mult_of_pi t' then one
      else if is_pi t' orelse is_odd_int_mult_of_pi t' then minusone
      else Fn ("cos",[t'])
      end
  | arith_simplify_term (Fn ("ln",[t])) =
      let val t' = arith_simplify_term (metis_poly_term t) in
      if isInt 1 t' then zero
      else Fn ("ln",[t'])
      end
  | arith_simplify_term (Fn ("exp",[t])) =
      let val t' = arith_simplify_term (metis_poly_term t) in
      if isInt 0 t' then one
      else Fn ("exp",[t'])
      end

  | arith_simplify_term (Fn(f,args)) =  (*simplify function arguments*)
      Fn(f, map (arith_simplify_term o metis_poly_term) args)
  | arith_simplify_term t = t;  (*Var or Rat*)


(*We leave non-trivial rational denominators alone to avoid generating enormous numbers.*)

fun nontrivRat (Rat r) =
      let val (p,q) = Rat.quotient_of_rat r
      in not (abs p = 1 andalso q=1) end
  | nontrivRat _ = false;

fun nontriv (nu,de,divs) =
  if nontrivRat de then (Fn ("/",[nu,de]), one, divs)
  else (nu,de,divs);

fun nontriv_inv (nu,de,divs) =
  if nontrivRat de then (one, Fn ("/",[de,nu]), divs)
  else (nu,de,divs);

(*Try to force any term into a rational form, i.e. with / above. Result is a
  numerator, a denominator and a list of terms that must not be zero.
  The latter are not all denominator terms but just those involved in cross-multiplication.
  We avoid calling eval_Fn everywhere because it causes a few proofs to fail. Possibly very large
  integers are involved.*)
fun rational_fn (Fn ("-",[t1,t2])) =
      if isInt 0 t2 then rational_fn t1
      else rational_fn (Fn ("+", [t1, eval_Fn ("-",[t2])]))
  | rational_fn (Fn ("/",[t1,t2])) =
      let val (nu1,de1,divs1) = nontriv (rational_fn t1)
          and (nu2,de2,divs2) = nontriv_inv (rational_fn t2)
      in  (Fn ("*",[nu1,de2]), eval_Fn ("*",[de1,nu2]), divs1 @ divs2)  end
  | rational_fn (Fn (a,[t1,t2])) =
      let val (nu1,de1,divs1) = nontriv (rational_fn t1)
          and (nu2,de2,divs2) = nontriv (rational_fn t2)
      in  case a of
      	     "+" => if isInt 0 t1 then (nu2,de2,divs2)
	            else
	            if isInt 0 t2 then (nu1,de1,divs1)
		    else
		    (Fn ("+", [Fn ("*",[nu1,de2]), Fn ("*",[nu2,de1])]),
      	             eval_Fn ("*",[de1,de2]), [de1,de2] @ (divs1 @ divs2))
      	   | "*" => (Fn ("*",[nu1,nu2]), eval_Fn ("*",[de1,de2]), divs1 @ divs2)
      	   | _ => (Fn (a,[t1,t2]), one, [])
      end
  | rational_fn (Fn ("-",[t])) =
      let val (nu,de,divs) = rational_fn t
      in  (Fn ("-",[nu]), de, divs)  end
  | rational_fn t = (t, one, []);

fun map_accum f [] = ([], [])
  | map_accum f (t::ts) =
      let val (ys,zs1) = map_accum f ts
          val (y,zs2) = f t
      in  (y::ys, zs1 @ zs2)  end;

fun simp_mk_quo (Fn ("+",[s,t]), r) = eval_Fn ("+",[simp_mk_quo (s,r), simp_mk_quo (t,r)])
  | simp_mk_quo (Fn ("*",[s,t]), r) = eval_Fn ("*",[s, simp_mk_quo (t,r)])  (*coeff is in t*)
  | simp_mk_quo (Fn ("-",[t]), r) = eval_Fn ("-",[simp_mk_quo (t,r)])
  | simp_mk_quo (Rat r', r) = Term.Rat (Rat.mult (r', Rat.inv r))
  | simp_mk_quo (t,r) = simp_mk_prod (t, Term.Rat (Rat.inv r));

fun addfacts ts (Fn ("*",[s,t])) = addfacts (addfacts ts t) s
  | addfacts ts t = if isInt 1 t then ts else t::ts;

fun delFirstTerm (x,[]) =  raise Bug "delFirstTerm"
  | delFirstTerm (x,y::ys) = if Term.equal x y then ys else y :: delFirstTerm (x,ys);

fun delfact ts cans = list_prod (TermSet.foldl delFirstTerm ts cans);

(*Given a rational function, cancel common factors. They are added to the third argument,
  which accumulates terms that we are assuming to be nonzero.*)
fun cancel_common (nu,de,divs) =
  let val nus = addfacts [] nu
      and des = addfacts [] de
      val cans = TermSet.intersect (TermSet.fromList nus) (TermSet.fromList des)
  in  if TermSet.null cans then (nu,de,divs)
      else (delfact nus cans, delfact des cans, TermSet.toList cans @ divs)
  end;

(*Simplify a rational function when the denominator is a rational number.*)
fun simp_rational t =
  let val (nu, de, divs) = cancel_common (rational_fn t)
      val u = (case de of
                   Rat r => simp_mk_quo (nu,r)
                 | _ => Fn ("/",[nu,de]))
  in  (arith_simplify_term u, divs)  end;

fun truthOf true =  ("True",[])
  | truthOf false = ("False",[]);

fun numeric_eval_apply_lit "=" [x,y] = truthOf (Rat.eq(x,y))
  | numeric_eval_apply_lit "<" [x,y] = truthOf (Rat.lt(x,y))
  | numeric_eval_apply_lit "<=" [x,y] = truthOf (Rat.le(x,y))
  | numeric_eval_apply_lit _ _ = raise Error "numeric_eval_apply_lit";

(*Make an atomic expression, which can only be = or <=.  Trivial simplifications.*)
fun make_Atom (fname, [Fn("-",[s]), Fn("-",[t])]) = make_Atom (fname, [t,s])
  | make_Atom (fname, args) =
      numeric_eval_apply_lit fname (map destRat args)
      handle Error _ => (fname, args);

fun make_eqzero_atom t = make_Atom ("=", [t, zero]);

val unsafe_divisors = ref false;

(*Invoke a predicate, flattening each arithmetic expression to a single rational function
  Also returns side-conditions necessary to show the absence of division by zero.*)
fun simplify_Atom (fname, args) =
  let val _ = chatting 4 andalso
              chat ("Enter simplify_Atom: " ^ Atom.toString (fname, args))
      val (rats,divs) = map_accum simp_rational args
  in  (make_Atom (fname, rats),
       if !unsafe_divisors then []
       else map (make_eqzero_atom o arith_simplify_term) divs)
  end;

(* GOP: Modified to be a ref and allow extension. *)

val algebraic_ops = ["*","+","-"];
val special_functions = ["abs","floor","arccos","arcsin","arctan","cosh","sinh","tanh",
                            "cos","sin","tan","cbrt","exp","ln","log","pow","sqrt"];
val allow_special_functions = ref false;
val allow_nested_special_functions = ref true;

(*if gnd = true, term must be ground as well as algebraic*)
fun is_algebraic gnd =
  let fun strictly_algeb (Term.Var _) = not gnd
	| strictly_algeb (Rat _) = true
	| strictly_algeb (Fn (_,[])) = true   (*Skolem var*)
	| strictly_algeb (Fn ("^",[t,u])) = strictly_algeb t andalso is_natural u
	| strictly_algeb (Fn (f,args)) = mem f algebraic_ops andalso List.all strictly_algeb args
      fun algeb (Term.Var _) = not gnd
	| algeb (Rat _) = true
	| algeb (Fn (_,[])) = true   (*Skolem var*)
	| algeb (Fn ("^",[t,u])) = algeb t andalso is_natural u
	| algeb (Fn (f,args)) = (mem f algebraic_ops andalso List.all algeb args) orelse
                                ((!allow_special_functions) andalso mem f special_functions andalso
                                 (((!allow_nested_special_functions) andalso List.all algeb args) orelse List.all strictly_algeb args))

  in algeb end;

fun is_strictly_algebraic gnd =
  let fun strictly_algeb (Term.Var _) = not gnd
	| strictly_algeb (Rat _) = true
	| strictly_algeb (Fn (_,[])) = true   (*Skolem var*)
	| strictly_algeb (Fn ("^",[t,u])) = strictly_algeb t andalso is_natural u
	| strictly_algeb (Fn (f,args)) = mem f algebraic_ops andalso List.all strictly_algeb args
  in strictly_algeb end;

fun is_algebraic_literal gnd (_, (a,ts)) =
      mem a ["=","<=","<"] andalso List.all (is_algebraic gnd) ts;

fun is_strictly_algebraic_literal gnd (_, (a,ts)) =
      mem a ["=","<=","<"] andalso List.all (is_strictly_algebraic gnd) ts;


(*Trying to isolate the biggest term, t. Divide both sides by any constant coefficient it carries.*)
fun divide_coeff (a, t, u) =
 (chatting 4 andalso
  chat ("Enter divide_coeff: " ^ a ^ "  t = " ^ Term.toString t ^
	"  u = " ^ Term.toString u);
  case arith_simplify_term t of
      Fn("*", [t', Rat r]) =>
	  if Rat.gt0 r
	  then simplify_Atom(a, [t', simp_mk_quo (simp_mk_neg u, r)])
	  else simplify_Atom(a, [simp_mk_quo (u, Rat.neg r), t'])
    | t => simplify_Atom(a, [t, simp_mk_neg u])
 );

(*Simplification of predicates: the main case covers the arithmetic relations (=, <=).*)
fun mk_relation (a, Fn ("+",[t1,t2])) = (*t2 is "biggest" term in Horner nf*)
      divide_coeff (a, t2, t1)
  | mk_relation (a,t) = simplify_Atom(a, [t, zero]);

(** It seems obvious that "abs" should be included in the simplifications below,
    but tests on 100 problems demonstrate that if anything, it is harmful. **)

(*Simplify literals of the form f(t)=0. Only benefits a few problems.*)
fun simp_eq_zero (Fn("abs",[t]), lits) =
      (make_Atom("=",[t, zero]), lits)
  | simp_eq_zero (Fn("arcsin",[t]), lits) =
      (make_Atom("=",[t, zero]), lits)
  | simp_eq_zero (Fn("arctan",[t]), lits) =
      (make_Atom("=",[t, zero]), lits)
  | simp_eq_zero (Fn("exp",[_]), lits) = (truthOf false, lits)
  | simp_eq_zero (Fn("ln",[t]), lits) =
      (make_Atom("=",[t, one]),
       (make_Atom("<=",[t, zero])) :: lits)
  | simp_eq_zero (Fn("sqrt",[t]), lits) =
      (make_Atom("<=",[t, zero]), lits)
  | simp_eq_zero (Fn("cbrt",[t]), lits) =
      (make_Atom("=",[t, zero]), lits)
  | simp_eq_zero (Fn("*",[t, Rat r]), lits) =
      if Rat.eq (r, Rat.zero) then raise Bug "simp_eq_zero"
      else (make_Atom("=",[t, zero]), lits)
  | simp_eq_zero (t, lits) =
      (make_Atom("=",[t, zero]), lits);

(*Simplify literals of the form f(t)<=0.*)
fun simp_le_zero (Fn("arcsin",[t]), lits) =
      (make_Atom("<=",[t, zero]), lits)
  | simp_le_zero (Fn("arctan",[t]), lits) =
      (make_Atom("<=",[t, zero]), lits)
  | simp_le_zero (Fn("exp",[_]), lits) = (truthOf false, lits)
  | simp_le_zero (Fn("ln",[t]), lits) =
      (make_Atom("<=",[t, one]),
       (make_Atom("<=",[t, zero])) :: lits)
  | simp_le_zero (Fn("cosh",[t]), lits) = (truthOf false, lits)
  | simp_le_zero (Fn("sinh",[t]), lits) =
      (make_Atom("<=",[t, zero]), lits)
  | simp_le_zero (Fn("tanh",[t]), lits) =
      (make_Atom("<=",[t, zero]), lits)
  | simp_le_zero (Fn("sqrt",[t]), lits) =
      (make_Atom("<=",[t, zero]), lits)
  | simp_le_zero (Fn("cbrt",[t]), lits) =
      (make_Atom("<=",[t, zero]), lits)
  | simp_le_zero (Fn("*",[t, Rat r]), lits) =
      (case Rat.compare (r, Rat.zero) of
      	   GREATER => (make_Atom("<=",[t, zero]), lits)
      	 | LESS => (make_Atom("<=",[zero, t]), lits)
      	 | EQUAL => raise Bug "simp_le_zero")
  | simp_le_zero (t, lits) =
      (make_Atom("<=",[t, zero]), lits);

(*Simplify literals of the form 0<=f(t).*)
fun simp_ge_zero (Fn("arcsin",[t]), lits) =
      (make_Atom("<=",[zero, t]), lits)
  | simp_ge_zero (Fn("arctan",[t]), lits) =
      (make_Atom("<=",[zero, t]), lits)
  | simp_ge_zero (Fn("exp",[_]), lits) = (truthOf true, lits)
  | simp_ge_zero (Fn("ln",[t]), lits) =
      (make_Atom("<=",[one, t]),
       (make_Atom("<=",[t, zero]) :: lits))
  | simp_ge_zero (Fn("cosh",[t]), lits) = (truthOf true, lits)
  | simp_ge_zero (Fn("sinh",[t]), lits) =
      (make_Atom("<=",[zero, t]), lits)
  | simp_ge_zero (Fn("tanh",[t]), lits) =
      (make_Atom("<=",[zero, t]), lits)
  | simp_ge_zero (Fn("sqrt",[_]), lits) = (truthOf true, lits)
  | simp_ge_zero (Fn("cbrt",[t]), lits) =
      (make_Atom("<=",[zero, t]), lits)
  | simp_ge_zero (Fn("*",[t, Rat r]), lits) =
      (case Rat.compare (r, Rat.zero) of
      	   GREATER => (make_Atom("<=",[zero, t]), lits)
      	 | LESS => (make_Atom("<=",[t, zero]), lits)
      	 | EQUAL => raise Bug "simp_ge_zero")
  | simp_ge_zero (t, lits) = (make_Atom("<=",[zero, t]), lits);

fun simp_rel_zero (lit as ("<=",[s,t]), lits) =
      if isInt 0 s then simp_ge_zero (t, lits)
      else if isInt 0 t then simp_le_zero (s, lits)
      else (lit, lits)
  | simp_rel_zero (lit as ("=",[s,t]), lits) =
      if isInt 0 s then simp_eq_zero (t, lits)
      else if isInt 0 t then simp_eq_zero (s, lits)
      else (lit, lits)
  | simp_rel_zero (lit, lits) = (lit, lits);

infix ##;

fun metis_poly_lit_aux (a,[s,t]) =
      simp_rel_zero (mk_relation (a, metis_poly_term (Fn("-",[s,t]))))
  | metis_poly_lit_aux (a,ts) =
      simplify_Atom (a, map metis_poly_term ts)  (*SOME OTHER PREDICATE?*);

fun affix_sign pol (atm, lits) = ((pol,atm), lits);

(*Ground literals are fully simplified, other literals only for existential problems.
  Otherwise just basic simplification is performed.
  This policy seems natural and on the whole
  it appears to benefit the success rate and solution times.*)
fun metis_poly_lit (pol, ("$real",[_]))    = ((pol, ("True",[])), [])
  | metis_poly_lit (pol, ("$rat",[Rat r])) = ((pol, ("True",[])), [])
  | metis_poly_lit (pol, ("$int",[Rat r])) = ((pol, truthOf (Rat.is_integer r)), [])
  | metis_poly_lit (pol, ("lgen",[Rat r, s, t])) =
      if Rat.eq (r, Rat.zero) then metis_poly_lit (pol, ("<=",[s,t]))
      else
      if Rat.eq (r, Rat.one) then metis_poly_lit (not pol, ("<=",[t,s]))
      else (* raise Bug ("metis_poly_lit: bad rational in lgen : " ^ Rat.toString r) *)
      (
      chat("Warning - bad rational in lgen : lgen(" ^ Rat.toString r ^ ",....)");
      ((pol, ("lgen",[Rat r, s, t])),[])
      )
  | metis_poly_lit (pol, (a,ts)) =
      if not (!ground_only) orelse List.all isGround ts
      then affix_sign pol (metis_poly_lit_aux (a,ts))
      else affix_sign pol (simp_rel_zero ((make_Atom (a, map (arith_simplify_term o metis_poly_term) ts)), []));  (* Non-ground case: limited simplification *)

fun nonFalse ("False",[]) = false
  | nonFalse _            = true;

fun metis_poly_lit_repeat lit =
  let val _ = chatting 3 andalso chat ("Simplifying: " ^ Literal.toString lit)
      val (lit',zatoms) = metis_poly_lit lit
      val zatoms = List.filter nonFalse zatoms
      val _ = chatting 3 andalso not (null zatoms) andalso
              chat ("Side atoms: " ^ Print.toString (Print.ppList Atom.pp) zatoms)
  in  if lit = lit' then (lit',zatoms)
      else let val _ = chatting 3 andalso chat "And again..."
               val (lit'', zatoms') = metis_poly_lit_repeat lit'
      in (lit'', zatoms' @ zatoms) end
  end;

(*Returns true if the given literal is a boolean value identical to that supplied.*)
fun lit_is_bool b (false, atm) = lit_is_bool (not b) (true, atm)
  | lit_is_bool false (true, (a,ts)) = (a = "False" andalso null ts)
  | lit_is_bool true (true, (a,ts)) = (a = "True" andalso null ts);

(*The explicit base case is necessary to prevent looping because of the recursive call,
  which ensures that side conditions are also simplified.*)
fun metis_poly_lits [] = []
  | metis_poly_lits cl_lits =
     let val (clits,zatoms) = map_accum metis_poly_lit_repeat cl_lits
	 val lits = clits @ metis_poly_lits (map (pair true) zatoms)
     in  if List.exists (lit_is_bool true) lits
	 then raise Error "Thm.arith" (*Tautology, therefore reject*)
	 else List.filter (not o lit_is_bool false) lits
     end;

end;
