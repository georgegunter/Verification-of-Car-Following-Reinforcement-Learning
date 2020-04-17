(* ========================================================================= *)
(* THE ACTIVE SET OF CLAUSES                                                 *)
(* Copyright (c) 2001 Joe Hurd, distributed under the MIT license            *)

(* ========================================================================= *)
(* Modified to add splitting with backtracking and to include a split stack  *)
(* in the active data structure.                                JPB 31/1/11  *)
(* ========================================================================= *)
(* this version 29.11.11 *)

structure Active :> Active =
struct

open Useful;

(* ------------------------------------------------------------------------- *)
(* Splitting of products within literals.                                    *)
(* ------------------------------------------------------------------------- *)

fun is_special_function_term (Term.Fn(f,_::_)) = Poly.is_special_function f
  | is_special_function_term _                 = false;

(*Should we include the further condition Term.isGround u or Term.isGround t?
  It makes NO DIFFERENCE WHATEVER (tested again 2011-02-28).*)
fun is_elem_prod (Term.Fn("*", [_, Term.Rat _])) = false
  | is_elem_prod (Term.Fn("*", [t,_]))           = is_special_function_term t
  | is_elem_prod _ = false;

fun has_split (pol, ("<=",[t,u])) = is_elem_prod t orelse is_elem_prod u
  | has_split _                   = false;

val kboCmp = KnuthBendixOrder.compare KnuthBendixOrder.default;

(* reverse kboCmp to allow the easy reversing of ordering in case splitting *)
fun revOrder x =
   case x of NONE => NONE
    | SOME EQUAL => SOME EQUAL
    | SOME LESS => SOME GREATER
    | SOME GREATER => SOME LESS;

(*We prefer to split on a maximal term.*)
fun find_max [] = NONE
  | find_max [lit] = SOME lit
  | find_max (lit1::lit2::lits) =
      case (lit1,lit2) of
        ((_,atm1), (_,atm2)) =>
	    if kboCmp (Term.Fn atm1, Term.Fn atm2) = SOME GREATER
	    then find_max (lit1::lits)
	    else find_max (lit2::lits);

fun orient_split (atm as ("<=",[t,u])) =
  if is_elem_prod t then atm
  else if is_elem_prod u
  then (*move affected term to lhs*)
       ("<=", map Poly.simp_mk_neg [u, t])
  else raise Bug "make_split: bad literal"
  (* the following added just to remove Pattern is not exhaustive warning *)
 | orient_split atm = raise Bug "orient_split : bad atom";


fun leLit (t,u) = (true, ("<=",[t,u]));

fun eq0Lit t = (true, ("=",[t,Poly.zero]));

fun new_split cl lits =
  let val {parameters,thm,...} = Clause.dest cl
  in
      SOME (Clause.mk {parameters = parameters,
		       id = Clause.newId(),
		       thm = Thm.arith (Thm.split (LiteralSet.fromList lits) [thm])})
  end handle Error _ => NONE;

fun delFirstLit (x,[]) =  raise Error "delFirstLit"
  | delFirstLit (x,y::ys) = if Literal.equal x y then ys else y :: delFirstLit (x,ys);

fun make_split (cl, (pol,atm), lits) =
  let val _ = chatting 2 andalso
              chat ("PRODUCT SPLITTING " ^ Print.toString Clause.pp cl ^
                    "\n...at literal " ^ Print.toString Literal.pp (pol,atm))
      val lits = delFirstLit ((pol,atm),lits)
      val ("<=",[(Term.Fn("*", [t,u])), v]) = orient_split atm
      val _ = chatting 3 andalso
              chat ("  t = " ^ Print.toString Term.pp t ^ ";  u = " ^ Print.toString Term.pp u ^
                    "\n  v = " ^ Print.toString Term.pp v)
      open Poly
  in
      if is_special_function_term t then
	  let val branches = [((pol, ("<=",[t, mk_quo(v,u)])) :: leLit(u,zero) :: lits),
			      ((pol, ("<=",[mk_quo(v,u), t])) :: leLit(zero,u) :: lits),
			      ((pol, ("<=",[zero,v])) :: Literal.negate (leLit(u,zero)) :: Literal.negate (leLit(zero,u)) :: lits)]
	      (* val branches' = List.filter (fn c => not (RCF.isArithTaut (LiteralSet.fromList c))) branches
		 val branches'' = if (List.length branches' < 3) then branches' else branches *)
	      val branches'' = branches
(*	      val _ = if List.length branches'' < 3 then
			  print ("\n *** " ^ (Int.toString (3 - (List.length branches')))
				 ^ " quotient splitting branch(es) eliminated.\n") else () *)
	  in List.mapPartial (new_split cl) branches'' end
      else raise Bug "make_split: not elementary function"
  end;

fun quotient_split_clause cl acc =
  let val lits = (LiteralSet.toList o Clause.literals) cl
      val largelits = (LiteralSet.toList o Clause.largestLiterals) cl
  in
    case find_max (List.filter has_split largelits) of
        NONE => acc
      | SOME (pol,atm) => make_split (cl, (pol,atm), lits) @ acc
  end;

(* ------------------------------------------------------------------------- *)
(* Splitting of positive equalities: t = u  ===>  u <= t & t <= u            *)
(* ------------------------------------------------------------------------- *)

(* Only two problems benefit from this heuristic: cot-error-analysis-Intel-1, sin-cos-problem-7*)

(*Inequalities must contain at least one Skolem constant and not be algebraic.*)
fun is_equality (true, ("=",[t,u])) = not (NameSet.null (Term.freeSkosList [t,u]) orelse List.all (Poly.is_algebraic false) [t,u])
  | is_equality _                   = false;

fun make_eq_split (cl, lit as (true, ("=",[t,u])), lits) =
  let val _ = chatting 2 andalso
              chat ("EQUALITY SPLITTING " ^ Print.toString Clause.pp cl)
      val lits = delFirstLit (lit,lits)
  in
      chatting 3 andalso
      chat ("t = " ^ Print.toString Term.pp t ^ ";  u = " ^ Print.toString Term.pp u);
      List.mapPartial (new_split cl) [(leLit(u,t) :: lits), (leLit(t,u) :: lits)]
  end
 (* added to get rid of Pattern is not exhaustive warning *)
 | make_eq_split (cl,lit,lits) = raise Bug "make_eq_split bad lit";

fun equals_split_clause cl acc =
  let val lits = (LiteralSet.toList o Clause.literals) cl
      val largelits = (LiteralSet.toList o Clause.largestLiterals) cl
  in
    case find_max (List.filter is_equality largelits) of
        NONE => acc
      | SOME (pol,atm) => make_eq_split (cl, (pol,atm), lits) @ acc
  end;

(* ------------------------------------------------------------------------- *)
(* Squares.                                                                  *)
(* ------------------------------------------------------------------------- *)

(*We simplify non-algebraic comparisons involving zero, for example, t^2*u >= 0 or t*u=0.
  The literal t^2*u <= 0 is replaced by u <= 0 | t=0.
  But only two problems benefit from this heuristic: cosh-369, sin-index-2*)

fun dest_prod0 (Term.Fn("*",[s,t])) = SOME (s,t)
  | dest_prod0 _                    = NONE;

fun dest_prod t = if Poly.is_algebraic false t then NONE else dest_prod0 t;

fun factors (Term.Fn ("-",[s]))   = Poly.minusone :: factors s
  | factors (Term.Fn ("*",[s,t])) = factors s @ factors t
  | factors t = [t];

fun findsq us [] = NONE
  | findsq us (t::ts) =
      if List.exists (Term.equal t) ts andalso not (Poly.is_algebraic false t)
      then SOME (t, Poly.list_prod (rev us @ Poly.delFirstTerm (t,ts)))
      else findsq (t::us) ts;

(*Given t, returns (x,u) where t = x^2 u, or NONE. *)
fun find_square t = findsq [] (factors t);

val has_square = Option.isSome o find_square;
val has_prod = Option.isSome o dest_prod;

fun has_square_lit (pol,("<=",[t,u])) =
      ((Term.equal t Poly.zero andalso has_square u)
       orelse
       (Term.equal u Poly.zero andalso has_square t))
  | has_square_lit (pol,("=",[t,u])) =
      ((Term.equal t Poly.zero andalso has_prod u)
       orelse
       (Term.equal u Poly.zero andalso has_prod t))
  | has_square_lit _ = false;

fun square_split_clauses ((true, ("<=",[t,u])), lits) =
      if Term.equal t Poly.zero then
        case find_square u of
            	NONE => []
              | SOME (x,y) => [ eq0Lit x :: leLit (Poly.zero, y) :: lits ]
      else if Term.equal u Poly.zero then
        case find_square t of
            	NONE => []
              | SOME (x,y) => [ eq0Lit x :: leLit (y, Poly.zero) :: lits ]
      else []
  | square_split_clauses ((true, ("=",[t,u])), lits) =
      if Term.equal t Poly.zero then
        if Term.equal u Poly.zero then []
        else square_split_clauses ((true, ("=",[u,t])), lits)
      else if Term.equal u Poly.zero then
        case dest_prod t of
            	NONE => []
              | SOME (x,y) => [ eq0Lit x :: eq0Lit y :: lits ]
      else []
  | square_split_clauses ((false, ("<=",[t,u])), lits) =
      if Term.equal t Poly.zero then
        case find_square u of
            	NONE => []
              | SOME (x,y) => [ Literal.negate (eq0Lit x) :: lits,
                                Literal.negate (leLit (Poly.zero, y)) :: lits ]
      else if Term.equal u Poly.zero then
        case find_square t of
            	NONE => []
              | SOME (x,y) => [ Literal.negate (eq0Lit x) :: lits,
                                Literal.negate (leLit (y, Poly.zero)) :: lits ]
      else []
  | square_split_clauses ((false, ("=",[t,u])), lits) =
      if Term.equal t Poly.zero then
        if Term.equal u Poly.zero then [lits]   (*literal is 0<>0 *)
        else square_split_clauses ((false, ("=",[u,t])), lits)
      else if Term.equal u Poly.zero then
        if Poly.is_algebraic false t then []
        else
        case dest_prod t of
            	NONE => []
              | SOME (x,y) => [ Literal.negate (eq0Lit x) :: lits,
                                Literal.negate (eq0Lit y) :: lits]
      else []
  | square_split_clauses _ = [];

fun split_square_lit (cl, (pol,atm), lits) =
  let val _ = chatting 2 andalso
              chat ("SQUARE RULE " ^ Print.toString Clause.pp cl ^
                    "\n...at literal " ^ Print.toString Literal.pp (pol,atm))
      val lits = delFirstLit ((pol,atm),lits)
  in
      List.mapPartial (new_split cl) (square_split_clauses ((pol,atm), lits))
  end;

fun square_split_clause cl acc =
  let val lits = (LiteralSet.toList o Clause.literals) cl
      val largelits = (LiteralSet.toList o Clause.largestLiterals) cl
  in
    case find_max (List.filter has_square_lit largelits) of
        NONE => acc
      | SOME (pol,atm) => split_square_lit (cl, (pol,atm), lits) @ acc
  end;

(* ------------------------------------------------------------------------- *)
(* Case Splitting of ground clauses.                                         *)
(* ------------------------------------------------------------------------- *)

fun has_special_function (Term.Fn(f,ts)) =
	(not (null ts) andalso Poly.is_special_function f)
	orelse List.exists has_special_function ts
  | has_special_function _               = false;

(*Only inequalities involving special functions are interesting.*)
fun is_special_lit (pol, (a,ts)) =
  (a = "<=" andalso List.exists has_special_function ts);

fun new_pred () = (Name.newName (), []);

fun new_cases cl lits =
  let val {parameters,thm,...} = Clause.dest cl
  in
      Clause.mk {parameters = parameters,
	         id = Clause.newId(),
	         thm = Thm.cases (LiteralSet.fromList lits) [thm]}
  end;

exception HASH;

(*Create a hash table for literals, of the given size*)
fun mk_lit_table n =
      Polyhash.mkTable (Word.toIntX o Literal.hash, uncurry Literal.equal)
                       (n, HASH);

val cases_ht = mk_lit_table 500;

fun spl (_, [], _) = raise Bug "case split: empty"
  | spl (cl, [slit], olits) = [new_cases cl (slit::olits)]
  | spl (cl, slit1::slit2::slits, olits) =
      case Polyhash.peek cases_ht slit1 of
        SOME p => (chatting 2 andalso
                   chat ("Cached case " ^ Atom.toString p ^ " for\n" ^
                         Literal.toString slit1);
                   spl (cl, slit2::slits, (false,p) :: olits))
      | NONE =>
          let val p = new_pred ()
	  in
	     Polyhash.insert cases_ht (slit1, p);
	     new_cases cl [slit1,(true,p)] :: spl (cl, slit2::slits, (false,p) :: olits)
	  end;

fun make_cases (cl, slits, olits) =
  let val _ = chatting 2 andalso
              chat ("CASE SPLITTING " ^ Print.toString Clause.pp cl)
  in  spl (cl, slits, olits)  end;

val max_splits_r = ref 0;   (*LCP: upper limit for case splitting*)

fun lit_order ((pos1,atm1),(pos2,atm2)) =
  let val tm_pair = (Term.Fn atm1,Term.Fn atm2)
  in  valOf (kboCmp tm_pair) handle Option => Term.compare tm_pair
  end;

fun cases_split_clause cl =
  if !max_splits_r = 0 then NONE
  else
  let val lits = (LiteralSet.toList o Clause.literals) cl
      val (slits,olits) = List.partition is_special_lit lits
  in
    if length (List.filter is_special_lit slits) < 2 orelse
       not (List.all Literal.isGround lits) then NONE
    else (max_splits_r := !max_splits_r - 1;
          SOME (make_cases (cl, sort lit_order slits, olits)))
  end;

(* ------------------------------------------------------------------------- *)
(* Version of splitting code for use with backtracking i.e. no new variables *)
(* and splits are into two parts, left split is the minimum literal and the  *)
(* rest goes into the right split (though it may then be split further in a  *)
(* later split)                                                              *)
(* ------------------------------------------------------------------------- *)


(* identical to has_special_function but copied here to keep all code together *)
fun hasSpecialFunction (Term.Fn(f,ts)) =
	(not (null ts) andalso Poly.is_special_function f)
	orelse List.exists hasSpecialFunction ts
  | hasSpecialFunction _               = false;

(*Only inequalities involving special functions are interesting.*)
(* identical to is_special_lit *)
fun isSpecialLit (pol, (a,ts)) =
  (a = "<=" andalso List.exists hasSpecialFunction ts);

(* litsLeft will, in general, be just one literal but to make future changes *)
(* easier, is passed as a list in the same manner as litsRight               *)
fun newCases cl litsLeft litsRight =
  let val {parameters,thm,...} = Clause.dest cl
      val clLeft = Clause.mk {parameters = parameters,
	           id = Clause.newId(),
	           thm = Thm.leftCaseSplit (LiteralSet.fromList litsLeft) [thm]}
      val clRight = Clause.mk {parameters = parameters,
	           id = Clause.newId(),
	           thm = Thm.caseSplit (LiteralSet.fromList litsRight) [thm]}
  in
      (clLeft,clRight)
  end;

fun splClause (_, [], _) = raise Bug "case split: empty"
  | splClause (cl,(slit::slits), olits) = (newCases cl [slit] (slits @ olits));

fun makeCases (cl, slits, olits) =
  let val _ = chatting 2 andalso
              chat ("CASE SPLITTING (Backtracking version) " ^ Print.toString Clause.pp cl ^ "\n")
  in  splClause (cl, slits, olits)  end;

(* reverse ordering to lit_order *)
fun litOrder ((pos1,atm1),(pos2,atm2)) =
  let val tm_pair = (Term.Fn atm1,Term.Fn atm2)
  in  valOf (kboCmp tm_pair) handle Option => Term.compare tm_pair
  end;

fun caseSplitClause cl =
  let val lits = (LiteralSet.toList o Clause.literals) cl
      val (slits,olits) = List.partition isSpecialLit lits
  in
    if length (List.filter isSpecialLit slits) < 2 orelse
       not (List.all Literal.isGround lits) then NONE
    else
          SOME (makeCases (cl, sort litOrder slits, olits))
  end;

(* ------------------------------------------------------------------------- *)
(* Helper functions.                                                         *)
(* ------------------------------------------------------------------------- *)

(*MetisDebug
local
  fun mkRewrite ordering =
      let
        fun add (cl,rw) =
            let
              val {id, thm = th, ...} = Clause.dest cl
            in
              case total Thm.destUnitEq th of
                SOME l_r => Rewrite.add rw (id,(l_r,th))
              | NONE => rw
            end
      in
        foldl add (Rewrite.new (KnuthBendixOrder.compare ordering))
      end;

  fun allFactors red =
      let
        fun allClause cl =
            List.all red (cl :: Clause.factor cl) orelse
            let
              val () = Print.trace Clause.pp
                         "Active.isSaturated.allFactors: cl" cl
            in
              false
            end
      in
        List.all allClause
      end;

  fun allResolutions red =
      let
        fun allClause2 cl_lit cl =
            let
              fun allLiteral2 lit =
                  case total (Clause.resolve cl_lit) (cl,lit) of
                    NONE => true
                  | SOME cl => allFactors red [cl]
            in
              LiteralSet.all allLiteral2 (Clause.literals cl)
            end orelse
            let
              val () = Print.trace Clause.pp
                         "Active.isSaturated.allResolutions: cl2" cl
            in
              false
            end

        fun allClause1 allCls cl =
            let
              val cl = Clause.freshVars cl

              fun allLiteral1 lit = List.all (allClause2 (cl,lit)) allCls
            in
              LiteralSet.all allLiteral1 (Clause.literals cl)
            end orelse
            let
              val () = Print.trace Clause.pp
                         "Active.isSaturated.allResolutions: cl1" cl
            in
              false
            end

      in
        fn [] => true
         | allCls as cl :: cls =>
           allClause1 allCls cl andalso allResolutions red cls
      end;

  fun allParamodulations red cls =
      let
        fun allClause2 cl_lit_ort_tm cl =
            let
              fun allLiteral2 lit =
                  let
                    val para = Clause.paramodulate cl_lit_ort_tm

                    fun allSubterms (path,tm) =
                        case total para (cl,lit,path,tm) of
                          NONE => true
                        | SOME cl => allFactors red [cl]
                  in
                    List.all allSubterms (Literal.nonVarTypedSubterms lit)
                  end orelse
                  let
                    val () = Print.trace Literal.pp
                               "Active.isSaturated.allParamodulations: lit2" lit
                  in
                    false
                  end
            in
              LiteralSet.all allLiteral2 (Clause.literals cl)
            end orelse
            let
              val () = Print.trace Clause.pp
                         "Active.isSaturated.allParamodulations: cl2" cl
              val (_,_,ort,_) = cl_lit_ort_tm
              val () = Print.trace Rewrite.ppOrient
                         "Active.isSaturated.allParamodulations: ort1" ort
            in
              false
            end

        fun allClause1 cl =
            let
              val cl = Clause.freshVars cl

              fun allLiteral1 lit =
                  let
                    fun allCl2 x = List.all (allClause2 x) cls
                  in
                    case total Literal.destEq lit of
                      NONE => true
                    | SOME (l,r) =>
                      allCl2 (cl,lit,Rewrite.LeftToRight,l) andalso
                      allCl2 (cl,lit,Rewrite.RightToLeft,r)
                  end orelse
                  let
                    val () = Print.trace Literal.pp
                               "Active.isSaturated.allParamodulations: lit1" lit
                  in
                    false
                  end
            in
              LiteralSet.all allLiteral1 (Clause.literals cl)
            end orelse
            let
              val () = Print.trace Clause.pp
                         "Active.isSaturated.allParamodulations: cl1" cl
            in
              false
            end
      in
        List.all allClause1 cls
      end;

  fun redundant {subsume,reduce,rewrite} =
      let
        fun simp cl =
            case Clause.simplify cl of
              NONE => true
            | SOME cl =>
              Subsume.isStrictlySubsumed subsume (Clause.literals cl) orelse
              let
                val cl' = cl
                val cl' = Clause.reduce reduce cl'
                val cl' = Clause.rewrite rewrite cl'
              in
                not (Clause.equalThms cl cl') andalso
                (simp cl' orelse
                 let
                   val () = Print.trace Clause.pp
                              "Active.isSaturated.redundant: cl'" cl'
                 in
                   false
                 end)
              end
      in
        fn cl =>
           simp cl orelse
           let
             val () = Print.trace Clause.pp
                        "Active.isSaturated.redundant: cl" cl
           in
             false
           end
      end;
in
  fun isSaturated ordering subs cls =
      let
        val rd = Units.empty
        val rw = mkRewrite ordering cls
        val red = redundant {subsume = subs, reduce = rd, rewrite = rw}
      in
        (allFactors red cls andalso
         allResolutions red cls andalso
         allParamodulations red cls) orelse
        let
          val () = Print.trace Rewrite.pp "Active.isSaturated: rw" rw
          val () = Print.trace (Print.ppList Clause.pp)
                     "Active.isSaturated: clauses" cls
        in
          false
        end
      end;
end;

fun checkSaturated ordering subs cls =
    if isSaturated ordering subs cls then ()
    else raise Bug "Active.checkSaturated";
*)

(* ------------------------------------------------------------------------- *)
(* A type of active clause sets.                                             *)
(* ------------------------------------------------------------------------- *)

type simplify = {subsume : bool, reduce : bool, rewrite : bool};

type parameters =
     {clause : Clause.parameters,
      prefactor : simplify,
      postfactor : simplify};

datatype active =
    Active of
      {parameters : parameters,
       clauses : Clause.clause IntMap.map,
       units : Units.units,
       rewrite : Rewrite.rewrite,
       subsume : Clause.clause Subsume.subsume,
       literals : (Clause.clause * Literal.literal) LiteralNet.literalNet,
       equations :
         (Clause.clause * Literal.literal * Rewrite.orient * Term.term)
         TermNet.termNet,
       subterms :
         (Clause.clause * Literal.literal * Term.path * Term.term)
         TermNet.termNet,
       allSubterms : (Clause.clause * Term.term) TermNet.termNet};

fun getSubsume (Active {subsume = s, ...}) = s;

fun getAllClauses (Active {clauses = c, ...}) = IntMap.values c

fun updateSubsume (Active {parameters,clauses,units,rewrite,subsume,literals,equations,subterms,allSubterms}) s =
    Active{parameters = parameters, clauses = clauses, units = units, rewrite = rewrite,
           subsume = s,
           literals = literals, equations = equations, subterms = subterms, allSubterms = allSubterms};

fun extractDeleted active =
  let
     val s = getSubsume active
     val (s,deletedClauses) = Subsume.extractDeleted (s,[])
     val active = updateSubsume active s
  in
     (active,deletedClauses)
  end;



fun setRewrite active rewrite =
    let
      val Active
            {parameters,clauses,units,subsume,literals,equations,
             subterms,allSubterms,...} = active
    in
      Active
        {parameters = parameters, clauses = clauses, units = units,
         rewrite = rewrite, subsume = subsume, literals = literals,
         equations = equations, subterms = subterms, allSubterms = allSubterms}
    end;

(* ------------------------------------------------------------------------- *)
(* Basic operations.                                                         *)
(* ------------------------------------------------------------------------- *)

val maxSimplify : simplify = {subsume = true, reduce = true, rewrite = true};

val default : parameters =
    {clause = Clause.default,
     prefactor = maxSimplify,
     postfactor = maxSimplify};

fun empty parameters =
    let
      val {clause,...} = parameters
      val {ordering,...} = clause
    in
      Active
        {parameters = parameters,
         clauses = IntMap.new (),
         units = Units.empty,
         rewrite = Rewrite.new (KnuthBendixOrder.compare ordering),
         subsume = Subsume.new (),
         literals = LiteralNet.new {fifo = false},
         equations = TermNet.new {fifo = false},
         subterms = TermNet.new {fifo = false},
         allSubterms = TermNet.new {fifo = false}}
    end;

fun emptyExisting (Active {parameters, ...}) =
    let
      val {clause,...} = parameters
      val {ordering,...} = clause
    in
      Active
        {parameters = parameters,
         clauses = IntMap.new (),
         units = Units.empty,
         rewrite = Rewrite.new (KnuthBendixOrder.compare ordering),
         subsume = Subsume.new (),
         literals = LiteralNet.new {fifo = false},
         equations = TermNet.new {fifo = false},
         subterms = TermNet.new {fifo = false},
         allSubterms = TermNet.new {fifo = false}}
    end;

fun size (Active {clauses,...}) = IntMap.size clauses;

fun clauses (Active {clauses = cls, ...}) =
    let
      fun add (_,cl,acc) = cl :: acc
    in
      IntMap.foldr add [] cls
    end;

fun saturation active =
    let
      fun remove (cl,(cls,subs)) =
          let
            val lits = Clause.literals cl
            val th = Clause.thm cl
            val (sflag,subs) = Subsume.isStrictlySubsumed subs th cl
          in
            if sflag then (cls,subs)
            else (cl :: cls, Subsume.insert subs (lits,(cl))) (* NB earlier versions had (lits,()) but this now leads to type errors ??? JPB 23.2.11 *)
          end
      val cls = clauses active
      val (cls,_) = foldl remove ([], Subsume.new ()) cls
      val (cls,subs) = foldl remove ([], Subsume.new ()) cls
(*MetisDebug
      val Active {parameters,...} = active
      val {clause,...} = parameters
      val {ordering,...} = clause
      val () = checkSaturated ordering subs cls
*)
    in
      cls
    end;

(* ------------------------------------------------------------------------------ *)
(* function, based on saturation above, to return a list of clauses in active     *)
(* that are redundant in the sense of being subsumed - this is for debug purposes *)
(* ------------------------------------------------------------------------------ *)
fun redundant active =
    let
      fun remove (cl,(cls,subs)) =
          let
            val lits = Clause.literals cl
            val th = Clause.thm cl
            val (sflag,subs) = Subsume.isStrictlySubsumed subs th cl
          in
            if sflag then (cl::cls,subs)
            else (cls, Subsume.insert subs (lits,(cl)))
          end
      val cls = clauses active
      val (cls,_) = foldl remove ([], Subsume.new ()) cls
      val (cls,subs) = foldl remove (cls, Subsume.new ()) cls
    in
      cls
    end;





(* ------------------------------------------------------------------------- *)
(* Pretty printing.                                                          *)
(* ------------------------------------------------------------------------- *)

val pp =
    let
      fun toStr active = "Active{" ^ Int.toString (size active) ^ "}"
    in
      Print.ppMap toStr Print.ppString
    end;

(*MetisDebug
local
  fun ppField f ppA a =
      Print.blockProgram Print.Inconsistent 2
        [Print.addString (f ^ " ="),
         Print.addBreak 1,
         ppA a];

  val ppClauses =
      ppField "clauses"
        (Print.ppMap IntMap.toList
           (Print.ppList (Print.ppPair Print.ppInt Clause.pp)));

  val ppRewrite = ppField "rewrite" Rewrite.pp;

  val ppSubterms =
      ppField "subterms"
        (TermNet.pp
           (Print.ppMap (fn (c,l,p,t) => ((Clause.id c, l, p), t))
              (Print.ppPair
                 (Print.ppTriple Print.ppInt Literal.pp Term.ppPath)
                 Term.pp)));
in
  fun pp (Active {clauses,rewrite,subterms,...}) =
      Print.blockProgram Print.Inconsistent 2
        [Print.addString "Active",
         Print.addBreak 1,
         Print.blockProgram Print.Inconsistent 1
           [Print.addString "{",
            ppClauses clauses,
            Print.addString ",",
            Print.addBreak 1,
            ppRewrite rewrite,
(*MetisTrace5
            Print.addString ",",
            Print.addBreak 1,
            ppSubterms subterms,
*)
            Print.skip],
         Print.addString "}"];
end;
*)

val toString = Print.toString pp;

(* ------------------------------------------------------------------------- *)
(* Simplify clauses.                                                         *)
(* ------------------------------------------------------------------------- *)

fun simplify simp units rewr subs =
    let
      val {subsume = s, reduce = r, rewrite = w} = simp

      fun rewrite cl =
          let
            val cl' = Clause.rewrite rewr cl
          in
            if Clause.equalThms cl cl' then SOME cl else Clause.simplify cl'
          end
    in
      fn cl =>
         case Clause.simplify cl of
           NONE => (NONE, subs)
         | SOME cl =>
           case (if w then rewrite cl else SOME cl) of
             NONE => (NONE, subs)
           | SOME cl =>
             let
               val cl = if r then Clause.reduce units cl else cl
               val (sflag,subs) = if s then Clause.subsumes subs cl
                                  else (false,subs)
             in
               if sflag
               then (chatting 2 andalso chat ("SUBSUMED:\n" ^ Print.toString Clause.pp cl); (NONE,subs))
               else (SOME cl,subs)
             end
    end;

(*MetisDebug
val simplify = fn simp => fn units => fn rewr => fn subs => fn cl =>
    let
      fun traceCl s = Print.trace Clause.pp ("Active.simplify: " ^ s)
(*MetisTrace4
      val ppClOpt = Print.ppOption Clause.pp
      val () = traceCl "cl" cl
*)
      val cl' = simplify simp units rewr subs cl
(*MetisTrace4
      val () = Print.trace ppClOpt "Active.simplify: cl'" cl'
*)
      val () =
          case cl' of
            NONE => ()
          | SOME cl' =>
            case
              (case simplify simp units rewr subs cl' of
                 NONE => SOME ("away", K ())
               | SOME cl'' =>
                 if Clause.equalThms cl' cl'' then NONE
                 else SOME ("further", fn () => traceCl "cl''" cl'')) of
              NONE => ()
            | SOME (e,f) =>
              let
                val () = traceCl "cl" cl
                val () = traceCl "cl'" cl'
                val () = f ()
              in
                raise
                  Bug
                    ("Active.simplify: clause should have been simplified "^e)
              end
    in
      cl'
    end;
*)

fun simplifyActive simp active =
    let
      val Active {units,rewrite,subsume,...} = active
    in
      simplify simp units rewrite subsume
    end;

(* ------------------------------------------------------------------------- *)
(* Add a clause into the active set.                                         *)
(* ------------------------------------------------------------------------- *)

fun addUnit units cl =
    let
      val th = Clause.thm cl
    in
  (*    if(Thm.getLevel th) > 0 then units else *) (* Only add top level clauses *)
      case total Thm.destUnit th of
        SOME lit => Units.add units (lit,th)
      | NONE => units
    end;

fun addRewrite rewrite cl =
    let
      val th = Clause.thm cl
    in
      if(Thm.getLevel th) > 0 then rewrite else (* Only add top level clauses *)
      case total Thm.destUnitEq th of
        SOME l_r => Rewrite.add rewrite (Clause.id cl, (l_r,th))
      | NONE => rewrite
    end;

fun addSubsume subsume cl = Subsume.insert subsume (Clause.literals cl, cl);

fun addLiterals literals cl =
    let
      fun add (lit as (_,atm), literals) =
          if Atom.isEq atm then literals
          else LiteralNet.insert literals (lit,(cl,lit))
    in
      LiteralSet.foldl add literals (Clause.largestLiterals cl)
    end;

fun addEquations equations cl =
    let
      fun add ((lit,ort,tm),equations) =
          TermNet.insert equations (tm,(cl,lit,ort,tm))
    in
      foldl add equations (Clause.largestEquations cl)
    end;

fun addSubterms subterms cl =
    let
      fun add ((lit,path,tm),subterms) =
          TermNet.insert subterms (tm,(cl,lit,path,tm))
    in
      foldl add subterms (Clause.largestSubterms cl)
    end;

fun addAllSubterms allSubterms cl =
    let
      fun add ((_,_,tm),allSubterms) =
          TermNet.insert allSubterms (tm,(cl,tm))
    in
      foldl add allSubterms (Clause.allSubterms cl)
    end;

fun addClause active cl =
    let
      val Active
            {parameters,clauses,units,rewrite,subsume,literals,
             equations,subterms,allSubterms} = active
      val clauses = IntMap.insert clauses (Clause.id cl, cl)
      and subsume = addSubsume subsume cl
      and literals = addLiterals literals cl
      and equations = addEquations equations cl
      and subterms = addSubterms subterms cl
      and allSubterms = addAllSubterms allSubterms cl
    in
      Active
        {parameters = parameters, clauses = clauses, units = units,
         rewrite = rewrite, subsume = subsume, literals = literals,
         equations = equations, subterms = subterms,
         allSubterms = allSubterms}
    end;

(* A version for debugging (exp-problem-9-weak3) that *)
(* doesn't add to subsume.                            *)
fun addClauseButNotToSubsume active cl =
    let
      val Active
            {parameters,clauses,units,rewrite,subsume,literals,
             equations,subterms,allSubterms} = active
      val clauses = IntMap.insert clauses (Clause.id cl, cl)
      and literals = addLiterals literals cl
      and equations = addEquations equations cl
      and subterms = addSubterms subterms cl
      and allSubterms = addAllSubterms allSubterms cl
    in
      Active
        {parameters = parameters, clauses = clauses, units = units,
         rewrite = rewrite, subsume = subsume, literals = literals,
         equations = equations, subterms = subterms,
         allSubterms = allSubterms}
    end;
(* END OF DEBUG VERSION *)


fun addFactorClause active cl =
    let
      val Active
            {parameters,clauses,units,rewrite,subsume,literals,
             equations,subterms,allSubterms} = active
      val units = addUnit units cl
      and rewrite = addRewrite rewrite cl
    in
      Active
        {parameters = parameters, clauses = clauses, units = units,
         rewrite = rewrite, subsume = subsume, literals = literals,
         equations = equations, subterms = subterms, allSubterms = allSubterms}
    end;

(* Add Negated Left Split to the active set (a bit naughty as saturation *)
(* won't be guaranteed.                                                  *)
(* At present just add it to everything, but can experiment by adding it *)
(* to only unit for instance.                                            *)
(*fun addNegatedLeftSplitClause active cl = addFactorClause active cl;*)
(*fun addNegatedLeftSplitClause active cl = active *) (* Don't add it at all as an experiment - it is added as an algebraic clause *)
 (*   let
      val Active
            {parameters,clauses,units,rewrite,subsume,literals,
             equations,subterms,allSubterms} = active
      val clauses = IntMap.insert clauses (Clause.id cl, cl)
      and subsume = addSubsume subsume cl
      and literals = addLiterals literals cl
      and equations = addEquations equations cl
      and subterms = addSubterms subterms cl
      and allSubterms = addAllSubterms allSubterms cl
    in
      Active
        {parameters = parameters, clauses = clauses, units = units,
         rewrite = rewrite, subsume = subsume, literals = literals,
         equations = equations, subterms = subterms,
         allSubterms = allSubterms}
    end;
*)

fun addNegatedLeftSplitClause active cl =
let
    val active = addFactorClause active cl
    val Active
       {parameters,clauses,units,rewrite,subsume,literals,
        equations,subterms,allSubterms} = active
    val subsume = addSubsume subsume cl
in
      Active
        {parameters = parameters, clauses = clauses, units = units,
         rewrite = rewrite, subsume = subsume, literals = literals,
         equations = equations, subterms = subterms,
         allSubterms = allSubterms}
end;


fun addNegatedLeftSplit active [] = active
 |  addNegatedLeftSplit active (cl::rest) =
    let
       val active = addNegatedLeftSplitClause active cl
    in
       addNegatedLeftSplit active rest
    end;


(* ------------------------------------------------------------------------- *)
(* Derive (unfactored) consequences of a clause.                             *)
(* ------------------------------------------------------------------------- *)

fun deduceResolution literals cl (lit as (_,atm), acc) =
    let
      fun resolve (cl_lit,acc) =
          case total (Clause.resolve cl_lit) (cl,lit) of
            SOME cl' => cl' :: acc
          | NONE => acc
(*MetisTrace4
      val () = Print.trace Literal.pp "Active.deduceResolution: lit" lit
*)
    in
      if Atom.isEq atm then acc
      else foldl resolve acc (LiteralNet.unify literals (Literal.negate lit))
    end;

fun deduceParamodulationWith subterms cl ((lit,ort,tm),acc) =
    let
      fun para (cl_lit_path_tm,acc) =
          case total (Clause.paramodulate (cl,lit,ort,tm)) cl_lit_path_tm of
            SOME cl' => cl' :: acc
          | NONE => acc
    in
      if (!Clause.useParamodulation) then
         foldl para acc (TermNet.unify subterms tm)
      else
         foldl para acc (TermNet.matched subterms tm)
    end;

fun deduceParamodulationInto equations cl ((lit,path,tm),acc) =
    let
      fun para (cl_lit_ort_tm,acc) =
          case total (Clause.paramodulate cl_lit_ort_tm) (cl,lit,path,tm) of
            SOME cl' => cl' :: acc
          | NONE => acc
    in
      if(!Clause.useParamodulation) then
        foldl para acc (TermNet.unify equations tm)
      else
        foldl para acc (TermNet.match equations tm)
    end;

fun deduce active cl =
    let
      val Active {parameters,literals,equations,subterms,...} = active

      val lits = Clause.largestLiterals cl
      val _ = chatting 3 andalso
              (Thm.isUnit (Clause.thm cl) orelse
	       chat ("Largest literals (" ^ Int.toString (LiteralSet.size lits) ^ "):\n" ^
		     join ", " (map Literal.toString (LiteralSet.toList lits))))
      val eqns = Clause.largestEquations cl
      val subtms =
          if TermNet.null equations then [] else Clause.largestSubterms cl
(*MetisTrace5
      val () = Print.trace LiteralSet.pp "Active.deduce: lits" lits
      val () = Print.trace
                 (Print.ppList
                    (Print.ppMap (fn (lit,ort,_) => (lit,ort))
                      (Print.ppPair Literal.pp Rewrite.ppOrient)))
                 "Active.deduce: eqns" eqns
      val () = Print.trace
                 (Print.ppList
                    (Print.ppTriple Literal.pp Term.ppPath Term.pp))
                 "Active.deduce: subtms" subtms
*)
      val acc = []
      val acc = LiteralSet.foldl (deduceResolution literals cl) acc lits
      val acc = foldl (deduceParamodulationWith subterms cl) acc eqns
      val acc = foldl (deduceParamodulationInto equations cl) acc subtms
      val acc = quotient_split_clause cl acc
      val acc = equals_split_clause cl acc
      val acc = square_split_clause cl acc
      val acc = rev acc
(*MetisTrace5
      val () = Print.trace (Print.ppList Clause.pp) "Active.deduce: acc" acc
*)
    in
      acc
    end;

(* 2.5.11 Separate out the non-case splitting deductions *)
fun check_for_splits cl acc  =
      let
          val acc = quotient_split_clause cl acc
      in
        rev acc
      end;

(* ------------------------------------------------------------------------- *)
(* Extract clauses from the active set that can be simplified.               *)
(* ------------------------------------------------------------------------- *)

local
  fun clause_rewritables active =
      let
        val Active {clauses,rewrite,...} = active

        fun rewr (id,cl,ids) =
            let
              val cl' = Clause.rewrite rewrite cl
            in
              if Clause.equalThms cl cl' then ids else IntSet.add ids id
            end
      in
        IntMap.foldr rewr IntSet.empty clauses
      end;

  fun orderedRedexResidues (((l,r),_),ort) =
      case ort of
        NONE => []
      | SOME Rewrite.LeftToRight => [(l,r,true)]
      | SOME Rewrite.RightToLeft => [(r,l,true)];

  fun unorderedRedexResidues (((l,r),_),ort) =
      case ort of
        NONE => [(l,r,false),(r,l,false)]
      | SOME _ => [];

  fun rewrite_rewritables active rewr_ids =
      let
        val Active {parameters,rewrite,clauses,allSubterms,...} = active
        val {clause = {ordering,...}, ...} = parameters
        val order = KnuthBendixOrder.compare ordering

        fun addRewr (id,acc) =
            if IntMap.inDomain id clauses then IntSet.add acc id else acc

        fun addReduce ((l,r,ord),acc) =
            let
              fun isValidRewr tm =
                  case total (Subst.match Subst.empty l) tm of
                    NONE => false
                  | SOME sub =>
                    ord orelse
                    let
                      val tm' = Subst.subst (Subst.normalize sub) r
                    in
                      order (tm,tm') = SOME GREATER
                    end

              fun addRed ((cl,tm),acc) =
                  let
(*MetisTrace5
                    val () = Print.trace Clause.pp "Active.addRed: cl" cl
                    val () = Print.trace Term.pp "Active.addRed: tm" tm
*)
                    val id = Clause.id cl
                  in
                    if IntSet.member id acc then acc
                    else if not (isValidRewr tm) then acc
                    else IntSet.add acc id
                  end

(*MetisTrace5
              val () = Print.trace Term.pp "Active.addReduce: l" l
              val () = Print.trace Term.pp "Active.addReduce: r" r
              val () = Print.trace Print.ppBool "Active.addReduce: ord" ord
*)
            in
              List.foldl addRed acc (TermNet.matched allSubterms l)
            end

        fun addEquation redexResidues (id,acc) =
            case Rewrite.peek rewrite id of
              NONE => acc
            | SOME eqn_ort => List.foldl addReduce acc (redexResidues eqn_ort)

        val addOrdered = addEquation orderedRedexResidues

        val addUnordered = addEquation unorderedRedexResidues

        val ids = IntSet.empty
        val ids = List.foldl addRewr ids rewr_ids
        val ids = List.foldl addOrdered ids rewr_ids
        val ids = List.foldl addUnordered ids rewr_ids
      in
        ids
      end;

  fun choose_clause_rewritables active ids = size active <= length ids

  fun rewritables active ids =
      if choose_clause_rewritables active ids then clause_rewritables active
      else rewrite_rewritables active ids;

(*MetisDebug
  val rewritables = fn active => fn ids =>
      let
        val clause_ids = clause_rewritables active
        val rewrite_ids = rewrite_rewritables active ids

        val () =
            if IntSet.equal rewrite_ids clause_ids then ()
            else
              let
                val ppIdl = Print.ppList Print.ppInt
                val ppIds = Print.ppMap IntSet.toList ppIdl
                val () = Print.trace pp "Active.rewritables: active" active
                val () = Print.trace ppIdl "Active.rewritables: ids" ids
                val () = Print.trace ppIds
                           "Active.rewritables: clause_ids" clause_ids
                val () = Print.trace ppIds
                           "Active.rewritables: rewrite_ids" rewrite_ids
              in
                raise Bug "Active.rewritables: ~(rewrite_ids SUBSET clause_ids)"
              end
      in
        if choose_clause_rewritables active ids then clause_ids else rewrite_ids
      end;
*)

  fun delete active ids =
      if IntSet.null ids then active
      else
        let
          fun idPred id = not (IntSet.member id ids)

          fun clausePred cl = idPred (Clause.id cl)

          val Active
                {parameters,
                 clauses,
                 units,
                 rewrite,
                 subsume,
                 literals,
                 equations,
                 subterms,
                 allSubterms} = active

          val clauses = IntMap.filter (idPred o fst) clauses
          and subsume = Subsume.filter clausePred subsume
          and literals = LiteralNet.filter (clausePred o #1) literals
          and equations = TermNet.filter (clausePred o #1) equations
          and subterms = TermNet.filter (clausePred o #1) subterms
          and allSubterms = TermNet.filter (clausePred o fst) allSubterms
        in
          Active
            {parameters = parameters,
             clauses = clauses,
             units = units,
             rewrite = rewrite,
             subsume = subsume,
             literals = literals,
             equations = equations,
             subterms = subterms,
             allSubterms = allSubterms}
        end;
in
  fun extract_rewritables (active as Active {clauses,rewrite,...}) =
      if Rewrite.isReduced rewrite then (active,[])
      else
        let
(*MetisTrace3
          val () = trace "Active.extract_rewritables: inter-reducing\n"
*)
          val (rewrite,ids) = Rewrite.reduce' rewrite
          val active = setRewrite active rewrite
          val ids = rewritables active ids
          val cls = IntSet.transform (IntMap.get clauses) ids
(*MetisTrace3
          val ppCls = Print.ppList Clause.pp
          val () = Print.trace ppCls "Active.extract_rewritables: cls" cls
*)
        in
          (delete active ids, cls)
        end
(*MetisDebug
        handle Error err =>
          raise Bug ("Active.extract_rewritables: shouldn't fail\n" ^ err);
*)
end;

(* ------------------------------------------------------------------------- *)
(* Factor clauses.                                                           *)
(* ------------------------------------------------------------------------- *)

local
  fun prefactor_simplify active subsume =
      let
        val Active {parameters,units,rewrite,...} = active
        val {prefactor,...} = parameters
      in
        simplify prefactor units rewrite subsume
      end;

  fun postfactor_simplify active subsume =
      let
        val Active {parameters,units,rewrite,...} = active
        val {postfactor,...} = parameters
      in
        simplify postfactor units rewrite subsume
      end;

  val sort_utilitywise =
      let
        fun utility cl =
            case LiteralSet.size (Clause.literals cl) of
              0 => ~1
            | 1 => if Thm.isUnitEq (Clause.thm cl) then 0 else 1
            | n => n
      in
        sortMap utility Int.compare
      end;

  fun factor_add (cl, active_subsume_acc as (active,subsume,acc)) =
    let
      val (scl,subsume) = postfactor_simplify active subsume cl
    in
      case  scl of
        NONE => (active,subsume,acc)
      | SOME cl =>
        let
          val active = addFactorClause active cl
          and subsume = addSubsume subsume cl
          and acc = cl :: acc
        in
          (active,subsume,acc)
        end
     end;

  fun factor1 (cl, active_subsume_acc as (active,subsume,acc)) =
    let
      val (scl,subsume) = prefactor_simplify active subsume cl
    in
      case scl of
        NONE => (active,subsume,acc)
      | SOME cl =>
        let
          val cls = sort_utilitywise (cl :: Clause.factor cl)
        in
          foldl factor_add active_subsume_acc cls
        end
     end;

  fun factor' active acc [] = (active, rev acc)
    | factor' active acc cls =
      let
        val cls = sort_utilitywise cls
        val subsume = getSubsume active
        val (active,subsume,acc) = foldl factor1 (active,subsume,acc) cls
        (* !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!! *)
        (* 24.2.11 Need to be very carefull here - only transfer the deleted clauses NOT the rest of the *)
        (* subsume structure.                                                                            *)
        (* !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!! *)
        val (_,dc) = Subsume.extractDeleted (subsume,[])
        (* filter out those clauses subsumed by top level clauses or subsumed by clauses *)
        (* on the same level.                                                            *)
        fun filter [] fdc = rev fdc
         |  filter ((scl,cl)::rest) fdc =
               let
                  val level_scl = Clause.getLevel scl
                  val level_cl = Clause.getLevel cl
                  val discard = level_scl = 0 orelse level_scl = level_cl
                in
                  if discard then filter rest fdc else filter rest ((scl,cl)::fdc)
                end
        val dc = filter dc []
        val subsume = getSubsume active
        val subsume = Subsume.addDeleted (subsume,dc)
        val active = updateSubsume active subsume
        (* !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!! *)
        val (active,cls) = extract_rewritables active
      in
        factor' active acc cls
      end;
in
  fun factor active cls = factor' active [] cls;
end;

(*MetisTrace4
val factor = fn active => fn cls =>
    let
      val ppCls = Print.ppList Clause.pp
      val () = Print.trace ppCls "Active.factor: cls" cls
      val (active,cls') = factor active cls
      val () = Print.trace ppCls "Active.factor: cls'" cls'
    in
      (active,cls')
    end;
*)

(* ------------------------------------------------------------------------- *)
(* Create a new active clause set and initialize clauses.                    *)
(* ------------------------------------------------------------------------- *)

fun new parameters {axioms,conjecture} =
    let
      val {clause,...} = parameters

      fun mk_clause th =
          Clause.mk {parameters = clause, id = Clause.newId (), thm = th}

      val active = empty parameters
      val (active,axioms) = factor active (map mk_clause axioms)
      val (active,conjecture) = factor active (map mk_clause conjecture)
    in
      (active,
       {axioms = axioms,
        conjecture = List.mapPartial (total Clause.arith) conjecture})
    end;





(* DEBUG *)
fun printSubsumedClauses active=
   let
       fun printSub (scl,cl) =
          "Subsuming clause : \n" ^ Print.toString Clause.pp scl ^ "\nSubsumed Clause : \n" ^ Print.toString Clause.pp cl ^ "\n"
       fun printAllSub [] = "\n++++++++++++++++++++++++++\n"
        |  printAllSub (sp::sps) =
              printSub sp ^ printAllSub sps
       val (_,dc) = extractDeleted active
       val s = "\nSubsuming and Subsumed clauses : \n+++++++++++++++++++++++++++\n" ^ printAllSub dc
    in
       print s
    end
(* END DEBUG *)

(* ------------------------------------------------------------------------- *)
(* Add a clause into the active set and deduce all consequences.             *)
(* ------------------------------------------------------------------------- *)

fun add active cl =
  let
    val (scl,subs) = simplifyActive maxSimplify active cl
    (* add the pair of scl and cl to the deleted clauses in subs - the labels should *)
    (* be correct because both units and rewrite call Thm.resolve.                   *)
    (* NB this code is redundant in add because add is only called when backtrack    *)
    (* case splitting is NOT used - the separated out parts of add in the functions  *)
    (* below are used instead, but I've left the code here incase add is reinstated. *)
    val subs = case scl of
                     NONE => subs
                 |   SOME cl' => if (Clause.equalThms cl cl') then subs
                                 else
                                     Subsume.addDeleted (subs,[(cl',cl)])
    val active = updateSubsume active subs
  in
    case scl of
      NONE => (active,[])
    | SOME cl' =>
      (* Apply LP splitting if it is set *)
      case cases_split_clause cl' of
          SOME cls => (active, cls)
        | NONE =>
      if Clause.isContradiction cl' then (active,[cl'])
      else if not (Clause.equalThms cl cl') then factor active [cl']
      else
        let
  (*MetisTrace2
           val () = Print.trace Clause.pp "Active.add: cl" cl
  *)
           val active = addClause active cl
           val cl = Clause.freshVars cl
           val cls = deduce active cl
           val _ = chatting 3 andalso
	           chat ("deduce active clauses: " ^ Int.toString (length cls))
           val (active,cls) = factor active cls
  (*MetisTrace2
	    val ppCls = Print.ppList Clause.pp
	    val () = Print.trace ppCls "Active.add: cls" cls
  *)
       in
          (active, List.mapPartial (total Clause.arith) cls)
       end
    end;

(* -------------------------------------------------------------------------*)
(* Code to separate simplification/factoring from adding/deducing/factoring *)
(* to allow clause splitting to take place only if simplification hasn't    *)
(* happened. Messy but not as messy as other solutions such as adding the   *)
(* split stack etc to the Active structure.                     JPB 25.3.11 *)
(* -------------------------------------------------------------------------*)
(* 26.4.11 further split to allow simplification to be separate from the    *)
(* factoring stage.  This makes more sense, and in particular allows the    *)
(* splitting of a simplified clause.                                        *)
fun simplify active cl =
let
    val (scl,subs) = simplifyActive maxSimplify active cl

    (* apply arith simplification to catch any oddities such as 0 = -10 *)
    (* This change causes all our normal problems to be given up on!!!!
    val scl = case scl of NONE => NONE
                |  SOME cl' => SOME (Clause.arith cl')
    *)

    (* add the pair of scl and cl to the deleted clauses in subs - the labels should *)
    (* be correct because both units and rewrite call Thm.resolve.                   *)
    val subs = case scl of
                     NONE => subs
                 |   SOME cl' => if (Clause.equalThms cl cl') then subs
                                 else
                                     Subsume.addDeleted (subs,[(cl',cl)])
    val active = updateSubsume active subs
in
   (active,scl)
end

fun factorOnly active cl =
      if Clause.isContradiction cl then (active,[cl]) else factor active [cl];

fun addAndFactor active cl =
   let
      val active = addClause active cl
      val cls = deduce active (Clause.freshVars cl)
      val (active,cls) = factor active cls
      val cls =  List.mapPartial (total Clause.arith) cls
   in
       (active,cls)
   end

(* -------------------------------------------------------------------- *)
(* Function to check if quotient/equality/square splitting is possible  *)
(* NB this is rather inefficiently done by trying it so the process has *)
(* to be repeated but this can be improved upon if it works  JPB 9.6.11 *)
(* -------------------------------------------------------------------- *)
fun canBQsplit cl =
let
    val cls = check_for_splits cl []
in
    not (null cls)
end


end (* of module Active.sml *)
