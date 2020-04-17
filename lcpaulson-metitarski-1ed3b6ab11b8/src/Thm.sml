(* ========================================================================= *)
(* A LOGICAL KERNEL FOR FIRST ORDER CLAUSAL THEOREMS                         *)
(* Copyright (c) 2001 Joe Hurd, distributed under the MIT license            *)

(* ========================================================================= *)
(* Modified by JPB to add clause labels for the purpose of splitting with    *)
(* backtracking. Clause labels are integer lists of split levels which       *)
(* should always be ordered (higher numbered splits occuring before lower    *)
(* numbered ones). The empty list corresponds to the top level when no splits*)
(* have yet occured. For each inference step labels must be appropriately    *)
(* transferred or modified.                                                  *)
(* Changes begun 24.1.11.                                                    *)
(* ========================================================================= *)
(* Further major change begun 29.3.11 to add a distance measure. The purpose *)
(* is to improve the accuracy for the case of backtracking and splitting.    *)
(* With the present scheme, the distance assigned to clauses on the right    *)
(* split is much greater as the right split is only entered when the left    *)
(* split has reached the empty clause. Additionally the distance measure is  *)
(* lost when clauses are deleted and then reinstated.                        *)
(* ========================================================================= *)
(* Another major change begun 6.5.11 to allow negative values in the clause  *)
(* label to indicate which are associated with hidden literals.              *)
(* ========================================================================= *)
(* 9.6.11 Set of Support feature added by including a SOS flag which is set  *)
(* to true if a clause (thm) is part of the conjecture or derived from it.   *)
(*                                                      This version 8.6.12  *)
(* ========================================================================= *)
structure Thm :> Thm =
struct

open Useful;

(* File name for including in Errors - this needs to be set within Metis.sml *)
val filename : string ref = ref "";


(* ------------------------------------------------------------------------- *)
(* An abstract type of first order logic theorems.                           *)
(* ------------------------------------------------------------------------- *)

type clause = LiteralSet.set;

type clauseLabel = int list;

type SOS = bool;

type clauseDistance = real;  (* measure of distance from the axiom *)

val AxiomDistance = 2.5; (* the minimum distance measure, assigned to axioms *)

datatype inferenceType =
    Axiom
  | Assume
  | Subst
  | Factor
  | Resolve
  | Refl
  | Equality
  | Arith
  | Decision
  | Split
  | Cases
  | CaseSplit

(* the last entry is the map from int label entry to hidden literal associated with the -ve left split   *)
(* it is only added to the final empty clause for passing to Prove.sml etc, the structure is kept in the *)
(* proof state up until then and only changes on splitting anyway.                                       *)
datatype thm = Thm of SOS*clauseDistance * clauseLabel * clause * (inferenceType * thm list)

type inference = inferenceType * thm list;


(* ------------------------------------------------------------------------- *)
(* Theorem destructors and constructors.                                     *)
(* ------------------------------------------------------------------------- *)
fun inSOS (Thm(SOS,_,_,_,_)) = SOS;

fun setSOS (Thm(_,d,l,cl,inf)) = Thm(true,d,l,cl,inf);

fun clearSOS (Thm(_,d,l,cl,inf)) = Thm(false,d,l,cl,inf);

fun isDecision (Thm(_,_,_,_,(Decision,_))) = true
 |  isDecision (_) = false

fun clauseDistance (Thm (_,distance,_,_,_)) = distance;

fun setClauseDistance distance (Thm(SOS,_,label,cl,inf)) = Thm(SOS,distance,label,cl,inf);

fun clauseLabel (Thm (_,_,label,_,_)) = label;

fun clause (Thm (_,_,_,cl,_)) = cl;

fun inference (Thm (_,_,_,_,inf)) = inf

fun parents (Thm (_,_,_,_,(_,parents))) = parents

fun setParents (Thm(SOS,d,l,cl,(inf,_))) parents = Thm(SOS,d,l,cl,(inf,parents));

(* -------------------------------------------------------------------------------------------------- *)
(* function to restore all hidden literals to the clause set for use in generating a split free proof *)
(* -------------------------------------------------------------------------------------------------- *)
fun restoreHiddenLits (Thm(SOS,d,label,cl,inf)) hidden =
let
    fun restore cs l h =
        let
            val co = IntMap.peek h l
            val cs = case co of SOME c => LiteralSet.add cs c
                              | NONE => raise Bug ("\nmissing hidden literal in Thm.restoreHiddenLits\n"
                                              ^ "label entry for missing lit : " ^ (Int.toString l))
        in
            cs
        end
    fun restoreAll cs [] h = cs
     |  restoreAll cs (l::ls) h = if l < 0 then
             restoreAll (restore cs (~l) h) ls h
        else
             restoreAll cs ls h
    val cl = restoreAll cl label hidden
in
    Thm(SOS,d,[],cl,inf)
end;

(* Tautologies *)

fun some_ge0 (true, ("<=",[s,t])) = if Poly.isInt 0 s then SOME t else NONE
  | some_ge0 _ = NONE;

fun some_gt0 (false, ("<=",[t,s])) = if Poly.isInt 0 s then SOME t else NONE
  | some_gt0 _ = NONE;

fun some_le0 (true, ("<=",[t,s])) = if Poly.isInt 0 s then SOME t else NONE
  | some_le0 _ = NONE;

fun some_lt0 (false, ("<=",[s,t])) = if Poly.isInt 0 s then SOME t else NONE
  | some_lt0 _ = NONE;

(*A clause that contains literals of the form x<=0 and x>=0 is a tautology.
  These frequently arise from the division axioms.*)
fun isOrderTaut th =
  let val lits = (LiteralSet.toList o clause) th
      val ge_ts = List.mapPartial some_ge0 lits
      val gt_ts = List.mapPartial some_gt0 lits
      val le_ts = List.mapPartial some_le0 lits
      val lt_ts = List.mapPartial some_lt0 lits
      fun pos (Term.Fn("*", [t,u])) = (pos t andalso pos u) orelse (neg t andalso neg u)
        | pos (Term.Fn("/", [t,u])) = (pos t andalso pos u) orelse (neg t andalso neg u)
        | pos (Term.Fn("cosh", [_])) = true             (*cosh(t) is always positive*)
        | pos (Term.Fn("exp", [_])) = true              (*exp(t) is always positive*)
        | pos (Term.Fn("pow", [_,_])) = true
            (*The function pow is defined by pow(X,Y) = exp(Y*ln(X)).
              It must not be confused with the function ^, which takes integer powers only.*)
        | pos t = List.exists (Term.equal t) le_ts (*assume the negation of other literals*)
      and neg (Term.Fn("*", [t,u])) = (pos t andalso neg u) orelse (neg t andalso pos u)
        | neg (Term.Fn("/", [t,u])) = (pos t andalso neg u) orelse (neg t andalso pos u)
        | neg t = List.exists (Term.equal t) ge_ts
  in  List.exists pos (ge_ts@gt_ts) orelse List.exists neg (le_ts@lt_ts) end;

fun swap_le (true, ("<=",[t,u])) = SOME (true, ("<=",[u,t]))
  | swap_le _ = NONE;

(*A clause that contains literals of the form x<=y and x>=y is a tautology.*)
fun isLinearTaut th =
  let val lset = clause th
      val swaps = List.mapPartial swap_le (LiteralSet.toList lset)
  in  List.exists (fn u => LiteralSet.member u lset) swaps end;

local
  fun chk (_,NONE) = NONE
    | chk ((pol,atm), SOME set) =
      if (pol andalso Atom.isRefl atm) orelse AtomSet.member atm set then NONE
      else SOME (AtomSet.add set atm);
  fun isPropTautology th =
      case LiteralSet.foldl chk (SOME AtomSet.empty) (clause th) of
        SOME _ => false
      | NONE => true;
in
  fun isTautology th =
      isPropTautology th orelse isLinearTaut th orelse isOrderTaut th
      (* *** *)
      (* GOP: Using Mathematica for recognising `semantic tautologies.' *)
      (* orelse inSOS th andalso RCF.isArithTaut (clause th) *)
      (* *** *)
end;

(* Contradictions *)

fun isContradiction th = LiteralSet.null (clause th);

(* Unit theorems *)

fun destUnit (Thm (_,_,_,cl,_)) =
    if LiteralSet.size cl = 1 then LiteralSet.pick cl
    else raise Error "Thm.destUnit";

val isUnit = can destUnit;

(* Unit equality theorems *)

fun destUnitEq th = Literal.destEq (destUnit th);

val isUnitEq = can destUnitEq;

(* Literals *)

fun member lit (Thm (_,_,_,cl,_)) = LiteralSet.member lit cl;

fun negateMember lit (Thm (_,_,_,cl,_)) = LiteralSet.negateMember lit cl;

(* ------------------------------------------------------------------------- *)
(* A total order.                                                            *)
(* ------------------------------------------------------------------------- *)

fun compare (th1,th2) = LiteralSet.compare (clause th1, clause th2);

fun equal th1 th2 = LiteralSet.equal (clause th1) (clause th2);

(* ------------------------------------------------------------------------- *)
(* Free variables.                                                           *)
(* ------------------------------------------------------------------------- *)

fun freeIn v (Thm (_,_,_,cl,_)) = LiteralSet.freeIn v cl;

fun freeVars (Thm (_,_,_,cl,_)) = LiteralSet.freeVars cl;

(* ------------------------------------------------------------------------- *)
(* Pretty-printing.                                                          *)
(* ------------------------------------------------------------------------- *)

fun SOStoString SOS = if SOS then "> In SOS <" else "> Not in SOS <";

fun distanceToString d = "[D:" ^ (realToString 1 d) ^ "]";

fun labelToString [] = ""
  | labelToString label =
  let
    fun f [] = "}-"
     |  f (l::ls) = ":" ^ (Int.toString l) ^ ":" ^ (f ls)
  in
    "{" ^ (f label)
  end

fun inferenceTypeToString Axiom = "Axiom"
  | inferenceTypeToString Arith = "Arith"
  | inferenceTypeToString Decision = "Decision"
  | inferenceTypeToString Split = "Split"
  | inferenceTypeToString Cases = "Cases"
  | inferenceTypeToString CaseSplit = "CaseSplit"
  | inferenceTypeToString Assume = "Assume"
  | inferenceTypeToString Subst = "Subst"
  | inferenceTypeToString Factor = "Factor"
  | inferenceTypeToString Resolve = "Resolve"
  | inferenceTypeToString Refl = "Refl"
  | inferenceTypeToString Equality = "Equality"

fun ppInferenceType inf =
    Print.ppString (inferenceTypeToString inf);

local
  fun toFormula th =
      Formula.listMkDisj
        (map Literal.toFormula (LiteralSet.toList (clause th)));
in
  fun pp th =
    if chatting 3 then
      Print.blockProgram Print.Inconsistent 3
        [Print.addString (SOStoString (inSOS th)),
         Print.addString (distanceToString (clauseDistance th)),
         Print.addString (labelToString (clauseLabel th)),
         Print.addBreak 0,
         Print.addString "|- ",Formula.pp (toFormula th)]
    else
      Print.blockProgram Print.Inconsistent 3
        [Print.addString "|- ",
         Formula.pp (toFormula th)];
end;

val toString = Print.toString pp;

fun parentsToString [] = "\n"
 |  parentsToString (th::ths) = "\n" ^ Print.toString pp th ^ parentsToString ths;

fun inferenceToString ((inf,parents):inference) = "\nInference : " ^ inferenceTypeToString inf ^ "\nParent Clauses : " ^ parentsToString parents

fun extendedToString th = (toString th) ^ (inferenceToString (inference th));



(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(* Merging clauseLabels - these should be ordered int lists (sets with       *)
(* no repeated elements).                                                    *)
(* 6.5.11 now they are ordered in terms of absolute magnitude but some will  *)
(* have negative values. Negative values take priority of positive values so *)
(* e.g. {-5:3:2} merged with {-5:-3:1} should be {-5:-3:2:1}                 *)
(*                                                                           *)
(* ------------------------------------------------------------------------- *)
fun mergeLabels [] [] = []
  | mergeLabels [] l = l
  | mergeLabels l [] = l
  | mergeLabels (l1::ls1) (l2::ls2) =
      if l1 = l2 then l1 :: mergeLabels ls1 ls2
      else if (~l1) = l2 then
                   if l1 < 0 then l1 :: mergeLabels ls1 ls2
                             else l2 :: mergeLabels ls1 ls2
         else if (Int.abs l1) > (Int.abs l2) then l1 :: mergeLabels ls1 (l2::ls2)
         else l2 :: mergeLabels (l1::ls1) ls2;
fun mergeTheoremListLabels [] = []
  | mergeTheoremListLabels (th::[]) = clauseLabel th
  | mergeTheoremListLabels (th1::ths) =
       mergeLabels (clauseLabel th1) (mergeTheoremListLabels ths)

(* Functions to update a clause label *)
fun updateLabel newLabel (Thm (SOS,dist,oldLabel,cl,inf_ths)) = Thm (SOS,dist,newLabel,cl,inf_ths)
fun getLevel (Thm (_,_,[],_,_)) = 0
   |getLevel (Thm (_,_,l::_,_,_)) = Int.abs l;

(* NB in most, if not all, circumstances the new level should be greater than *)
(* any existing level so raise an error if it isn't.                          *)
fun addLevelToLabel l th =
    let
       fun add (Thm (SOS,dist,ls,cl,inf)) = Thm (SOS,dist,l::ls,cl,inf)
       val old = getLevel th
    in
       if old >= (Int.abs l) then raise Error "Thm.addLevelToLabel"
       else add th
    end

fun removeTopLevelFromLabel (Thm (SOS,dist,[],cl,inf_ths)) = Thm (SOS,dist,[],cl,inf_ths)
 |  removeTopLevelFromLabel (Thm (SOS,dist,l::ls,cl,inf_ths)) = Thm (SOS,dist,ls,cl,inf_ths)

fun labelsDifferent (Thm (_,_,l1,_,_)) (Thm (_,_,l2,_,_)) =
   let
      fun diff [] [] = false
       |  diff [] _  = true
       |  diff _ []  = true
       |  diff (x::xs) (y::ys) =
             if (x = y) then diff xs ys else true
   in
      diff l1 l2
   end

fun SOSstatusOfList [] = false
 |  SOSstatusOfList (th::ths) = if (inSOS th) then true else SOSstatusOfList ths


(* --------------------------------------------------------------- *)
(* helper functions to find the maximum distance in a list of thms *)
(* --------------------------------------------------------------- *)
fun maxDistance ths =
  let
     fun maxDist [] max = max
      |  maxDist (th::rest) max =
            let
               val d = clauseDistance th
            in
               if d > max then
                  maxDist rest d
               else
                  maxDist rest max
             end
   in
      maxDist ths 0.0
   end;

fun maxOfPair th1 th2 =
    let
      val d1 = clauseDistance th1
      val d2 = clauseDistance th2
    in
      if d1 > d2 then d1 else d2
    end;

(* ------------------------------------------------------------------------- *)
(* Primitive rules of inference.                                             *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(* ----- axiom C                                                             *)
(*   C                                                                       *)
(* ------------------------------------------------------------------------- *)
(* NB axioms are all on the top level so have the empty list for clause labels
   their distance measure is AxiomDistance (not 0 as the distance is used as a product term
   in the clause weights *)
fun axiom cl = Thm (false,AxiomDistance,[],cl,(Axiom,[]));
fun conjecture cl = Thm(true,AxiomDistance,[],cl,(Axiom,[])); (* conjectures are differentiated from axioms to allow SOS to be applied *)

fun split cl ths =
    let
       val label = mergeTheoremListLabels ths
       val dist =  maxDistance ths
       val SOS = SOSstatusOfList ths
    in
       Thm (SOS,dist,label,cl,(Split,ths))
    end

(* LCP case splitting with variables *)
fun cases cl ths =
     let
        val label = mergeTheoremListLabels ths
        val dist =  maxDistance ths
        val SOS = SOSstatusOfList ths
     in
        Thm(SOS,dist,label,cl,(Cases,ths))
     end

(* case splitting with backtracking *)
(* NB the following is called for the right split prior to the left split being     *)
(* proved so the inference CaseSplit should eventually be replaced by the inference *)
(* Resolution in rightCaseSplit below.                                              *)
fun caseSplit cl ths =
     let
        val label = mergeTheoremListLabels ths (* NB there should be only one parent clause *)
        val dist =  maxDistance ths
        val SOS = SOSstatusOfList ths
     in
        Thm(SOS,dist,label,cl,(CaseSplit,[]))
     end
(* Left case splits are taken as Assume inferences and the labels are made   *)
(* positive (indicating no hidden literals) except for the first entry which *)
(* is negative to indicate the hidden literal consisting of the negated left *)
(* branch but this first entry is added within SplitStack.sml not here.      *)
fun leftCaseSplit cl ths =
     let
        fun abs l = if l < 0 then ~l else l
        fun makePositive [] ls = rev ls
         |  makePositive (l::ls) ps = makePositive ls ((abs l)::ps)
        val label = mergeTheoremListLabels ths (* NB there should be only one parent clause *)
        val label = makePositive label []
        val dist =  maxDistance ths
        val SOS = SOSstatusOfList ths
     in
        Thm(SOS,dist,label,cl,(Assume,[]))
     end

(* Right case splits are taken as the resolution of the negated left split *)
(* with the parent clause.                                                 *)
fun rightCaseSplit rcl leafMarker parent =
    let
       val rclLabel = clauseLabel rcl
       val lm = removeTopLevelFromLabel leafMarker
       val lmLabel = clauseLabel lm
       val label = mergeLabels rclLabel lmLabel
       val cl = clause rcl
       val dist = clauseDistance parent
       val SOS = inSOS parent orelse inSOS leafMarker
    in
       Thm(SOS,dist,label,cl,(Resolve,[parent,leafMarker]))
    end

(* Negative case split - 31.5.12 have a single parent which is the empty clause  *)
(* or leaf marker. NB when the empty clause has the hidden literal restored then *)
(* it will be the same as its child so care must be taken when reproducing the   *)
(* proof to avoid loops.                                                         *)
(* The top level must be removed from the label of the emptyCl or else the new   *)
(* clause will just be deleted, the toplevel label corresponds to the hidden lit *)
(* equal to the negation of the left split anyway for unit clauses.              *)
fun negCaseSplit lits emptyCl =
    let
        val dist = clauseDistance emptyCl
        val label = clauseLabel (removeTopLevelFromLabel emptyCl)
        val inf = (CaseSplit,[emptyCl])
        val SOS = inSOS emptyCl
    in
        Thm(SOS,dist,label,lits,inf)
    end

(* Streamlined version of mergesplit that doesn't merge the labels *)
(* as the th should already be a superset of the leafMarker label  *)
(* but it does update the distance value as ignoring this was      *)
(* found to make a significant difference on some problems e.g.    *)
(* sin-cos-problem-7                                     13.5.11   *)
(* Also the top level of the th label is deleted.                  *)
fun mergeCaseSplit (Thm(SOS,dist,label,cl,inf)) leafMarker =
     let
         val label = tl label
         val ld = clauseDistance leafMarker
         val dist = if (ld > dist) then ld else dist
         val SOS =  SOS orelse (inSOS leafMarker)
      in
         Thm(SOS,dist,label,cl,inf)
      end


(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(* ----------- assume L                                                      *)
(*   L \/ ~L                                                                 *)
(* ------------------------------------------------------------------------- *)
(* assumptions are tautologies so can be created at the top level so given the label [] *)
(* assumptions are NOT derived from the conjecture so SOS is false *)
fun assume lit =
    Thm (false,AxiomDistance,[],LiteralSet.fromList [lit, Literal.negate lit], (Assume,[]));

(* ------------------------------------------------------------------------- *)
(*    C                                                                      *)
(* -------- subst s                                                          *)
(*   C[s]                                                                    *)
(* ------------------------------------------------------------------------- *)

fun subst sub (th as Thm (SOS,dist,label,cl,inf)) =
    let
      val cl' = LiteralSet.subst sub cl
    in
      if Portable.pointerEqual (cl,cl') then th
      else
        case inf of
          (Subst,_) => Thm (SOS,dist,label,cl',inf)
        | _ => Thm (SOS,dist,label,cl',(Subst,[th]))
    end;

(* ------------------------------------------------------------------------- *)
(*   L \/ C    ~L \/ D                                                       *)
(* --------------------- resolve L                                           *)
(*        C \/ D                                                             *)
(*                                                                           *)
(* The literal L must occur in the first theorem, and the literal ~L must    *)
(* occur in the second theorem.                                              *)
(* ------------------------------------------------------------------------- *)

fun resolve lit (th1 as Thm (SOS1,dist1,label1,cl1,_)) (th2 as Thm (SOS2,dist2,label2,cl2,_)) =
    let
      val cl1' = LiteralSet.delete cl1 lit
      and cl2' = LiteralSet.delete cl2 (Literal.negate lit)
      val dist = if dist1 > dist2 then dist1 else dist2
      val SOS = SOS1 orelse SOS2
    in
      Thm (SOS,dist,(mergeLabels label1 label2),LiteralSet.union cl1' cl2', (Resolve,[th1,th2]))
    end;

(*MetisDebug
val resolve = fn lit => fn pos => fn neg =>
    resolve lit pos neg
    handle Error err =>
      raise Error ("Thm.resolve:\nlit = " ^ Literal.toString lit ^
                   "\npos = " ^ toString pos ^
                   "\nneg = " ^ toString neg ^ "\n" ^ err);
*)

(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(* --------- refl t                                                          *)
(*   t = t                                                                   *)
(* ------------------------------------------------------------------------- *)
(* SOS is false *)

fun refl tm = Thm (false,AxiomDistance,[],LiteralSet.singleton (true, Atom.mkRefl tm), (Refl,[])); (* t = t should be true at the top level so label it [] *)

(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(* ------------------------ equality L p t                                   *)
(*   ~(s = t) \/ ~L \/ L'                                                    *)
(*                                                                           *)
(* where s is the subterm of L at path p, and L' is L with the subterm at    *)
(* path p being replaced by t.                                               *)
(* ------------------------------------------------------------------------- *)
fun equality lit path t =
    let
      val s = Literal.subterm lit path

      val lit' = Literal.replace lit (path,t)

      val eqLit = Literal.mkNeq (s,t)

      val cl = LiteralSet.fromList [eqLit, Literal.negate lit, lit']
    in
      Thm (false,AxiomDistance,[],cl,(Equality,[]))        (* again, should be true at the top level so  simply label it [] *)
    end;

(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(* Arithmetic simplification of certain literals                             *)
(*                                                                           *)
(* ------------------------------------------------------------------------- *)


fun arith_with_flag (th as Thm (SOS,dist,label,cl,_)) =
  let val cl' = LiteralSet.fromList (Poly.metis_poly_lits (LiteralSet.toList cl))
  in
    if LiteralSet.equal cl cl' then (th,false) else (Thm (SOS,dist,label,cl',(Arith,[th])),true)

  end;

fun arith th = #1 (arith_with_flag th);

(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(* Creating a clause with the help of a decision procedure                   *)
(*                                                                           *)
(* ------------------------------------------------------------------------- *)

(*Simulated case splitting: to be deleted once the real thing is available.
  This function ensures that case labels used in the derivation are retained.*)
fun addLabels (th, lits) =
      LiteralSet.union lits (LiteralSet.filter Literal.is_label (clause th));

(* Important : cl here is simply a set of literals but it originates in a clause *)
(* so should carry a label with it. To do so would require changes to the        *)
(* Resolution module which I'd prefer to avoid. Within the Resolution module     *)
(* the Qepcad simplification routine calls Thm.resolve via                       *)
(* (new_clause (Thm.resolve e (Clause.thm cl) eth)) where cl is the original     *)
(* clause from which the lit set labelled cl below is derived. Therefore, as     *)
(* long as the Resolution module code is not changed the labels will be ok.      *)
(* This is perhaps a dangerous assumption but one I'll make for the time being.  *)

(* 17.6.11 always place result in SOS as we don't know the SOS status of cl *)

(* 16.8.11 Now calling RCF structure, not just QepcadB, as RCF strategy may vary. -GP *)

fun decision cl ths =
  if RCF.call_rcf_conj cl (map clause ths)
     handle Error e => (chat("Error : "^e^" in Thm.decision called when analysing file : " ^ (!filename) ^" \n");raise Error "Thm.decision")
  then Thm (true, maxDistance ths,
            mergeTheoremListLabels ths,
            foldl addLabels cl ths,
            (Decision,ths))
  else raise Error "Thm.decision";

end

