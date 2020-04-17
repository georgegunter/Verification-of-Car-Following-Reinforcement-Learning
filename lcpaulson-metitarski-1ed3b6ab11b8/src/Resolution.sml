(* ========================================================================= *)
(* THE RESOLUTION PROOF PROCEDURE                                            *)
(* Copyright (c) 2001 Joe Hurd, distributed under the MIT license            *)

(* ========================================================================= *)
(* Modified for splitting with backtracking - this affects the getting of    *)
(* of clauses from the waiting set (using removeIfValid) and conflicting     *)
(* clauses (i.e. the empty clause) may lead to backtracking rather than a    *)
(* final decision.       JPB 1.2.11                   this version 23.5.12   *)
(* ========================================================================= *)

structure Resolution :> Resolution =
struct

open Useful;

val DeltaClauseDistance = 3 (* the amount to increase the distance at each given clause step *)

val algebraic_clauses : Clause.clause list ref = ref [];
val allow_sf_in_algebraic_clauses = ref false; (* allow special functions in the algebraic_clause list *)

val maxStackDepth = ref 0;  (* maximum split stack depth allowed       *)

val max_algebraic_clause_syms = ref 100;  (*maximum number of symbols in an algebraic clause*)

fun set_maxalg k = max_algebraic_clause_syms := k;

(* flag to indicate a 2nd run should be made with a high value for max_algebraic_clause_syms *)
(* on waiting becoming empty.                                                                *)
val reRunWithHighMaxAlg = ref true;
fun rerunWithHighMaxAlg b = reRunWithHighMaxAlg := b;

(* Optional limit on the maximum run of given clauses outside of SOS before giving up *)
val outsideSOSCount = ref 0;
val maxRunOutsideSOS = ref 150; (* ground-problem-21 requires 142 so increased from 140 to 150 *)
fun setMaxRunOutsideSOS k = maxRunOutsideSOS := k;



(* Function to filter algebraic clauses removing any that have deleted *)
(* split levels in their clause labels.                                *)
fun filterAlgebraicClauses stack =
   let
      val _ = algebraic_clauses := (SplitStack.filterClauseList (!algebraic_clauses) stack)
   in
      ()
   end;

(*This option is normally disabled because it is rather inefficient.
  The reduction it yields is often unimpressive anyway.*)
val minimize_proofs = false;

(* ------------------------------------------------------------------------- *)
(* Chatting.                                                                 *)
(* ------------------------------------------------------------------------- *)

fun clause_to_string cl = Print.toString Clause.pp cl;

fun clauses_to_string cls = Print.toString (Print.ppList Clause.pp) cls;

(* ------------------------------------------------------------------------- *)
(* A type of resolution proof procedures.                                    *)
(* ------------------------------------------------------------------------- *)

type parameters =
     {active : Active.parameters,
      waiting : Waiting.parameters};

datatype resolution =
    Resolution of
      {parameters : parameters,
       active : Active.active,
       waiting : Waiting.waiting,
       deleted : SplitStack.deletedClauses,
       stack : SplitStack.splitStack,
       hidden : Literal.literal IntMap.map};

(* ------------------------------------------------------------------------- *)
(* Selecting algebraic clauses.                                              *)
(* ------------------------------------------------------------------------- *)

fun all_clause_lits pred cl = LiteralSet.all pred (Clause.literals cl);

fun any_clause_lits pred cl = List.exists pred (LiteralSet.toList (Clause.literals cl));

fun clause_symbols cl = LiteralSet.foldl (fn (tm,z) => Literal.symbols tm + z) 0 (Clause.literals cl);

fun expNvars n = exp op* 1.2 n 1.0;

fun clause_penalty cl =
      real (clause_symbols cl) *
      expNvars (NameSet.size (LiteralSet.freeSkos (Clause.literals cl)));

fun clause_penalty_below n cl = Real.floor (clause_penalty cl) < n;

(*This measure is simpler than clause_penalty and delivers equally good results.*)
fun is_small_clause cl = clause_symbols cl < !max_algebraic_clause_syms;

fun is_algebraic_clause gnd = all_clause_lits (orf Literal.is_label (Poly.is_algebraic_literal gnd));

fun is_strictly_algebraic_clause gnd = all_clause_lits (orf Literal.is_label (Poly.is_strictly_algebraic_literal gnd));


(*Remove redundant dependencies by trying all possibilities. It would be more efficient
  to do this only after a proof is found.*)
fun min_decision seen lits [] = Thm.decision lits seen
  | min_decision seen lits (th::ths) =
      Thm.decision lits (seen@ths) handle Error _ => min_decision (th::seen) lits ths;

fun decision lits =
  total (if minimize_proofs then min_decision [] lits else Thm.decision lits);

(* ------------------------------------------------------------------------- *)
(* Basic operations.                                                         *)
(* ------------------------------------------------------------------------- *)

val default : parameters =
    {active = Active.default,
     waiting = Waiting.default};

fun new parameters {axioms,conjecture} =
    let
      val {active = activeParm, waiting = waitingParm} = parameters
      val (active, {axioms = ax_cls, conjecture = conj_cls}) =
            Active.new activeParm {axioms = axioms, conjecture = conjecture}
      val waiting = Waiting.new waitingParm {axioms = ax_cls, conjecture = conj_cls}
      val deleted = SplitStack.newDeletedClauses ()
      val stack = SplitStack.newStack ()
      val hidden : (Literal.literal IntMap.map) = IntMap.new ()
    in
      chatting 2 andalso chat ("Axiom clauses:\n" ^ clauses_to_string ax_cls ^ "\n");
      chatting 2 andalso chat ("Conjecture clauses:\n" ^ clauses_to_string conj_cls ^ "\n");
      (* Revert back to the original definition of non ground as we now do NOT allow       *)
      (* free variables so the only variables are originally existentially quantified ones *)
      Poly.ground_only := List.all (all_clause_lits Literal.isGround) conj_cls;
      (* ONLY label the conjecture clauses NOT ground if they contain a Skolem function *)
      (*Poly.ground_only := not (List.exists (any_clause_lits Literal.containsSkolemFunction ) conj_cls);*)
      
      chatting 2 andalso chat ("Conjecture is " ^ (if !Poly.ground_only then "" else "NOT ") ^ "ground.\n");
      algebraic_clauses := [];
      Resolution {parameters = parameters, active = active, waiting = waiting, deleted = deleted, stack = stack, hidden = hidden}
    end;

fun active (Resolution {active = a, ...}) = a;

fun waiting (Resolution {waiting = w, ...}) = w;

val pp =
    Print.ppMap
      (fn Resolution {active,waiting,...} =>
          "Resolution(" ^ Int.toString (Active.size active) ^
          "<-" ^ Int.toString (Waiting.size waiting) ^ ")")
      Print.ppString;

(* ------------------------------------------------------------------------- *)
(* Simplification of clauses.                                                *)
(* ------------------------------------------------------------------------- *)

fun equal_cl cl1 cl2 = Clause.equalThms cl1 cl2;

fun mem_cl x = List.exists (Clause.equalThms x);

fun difference_cl s t =
    foldl (fn (v,x) => if mem_cl v t then x else v :: x) [] (rev s);

fun new_clause thm = Clause.mk {parameters = Clause.default, id = Clause.newId(), thm = thm}

(*The largest literals are deleted first. This heuristic yields uniform and sometimes spectacular benefits.*)
fun decreasingLitSize (t1,t2) = Int.compare (Literal.symbols t2, Literal.symbols t1)

(*Simulated case splitting: to be deleted once the real thing is available.*)
fun labels_among labels cl = LiteralSet.subset (LiteralSet.filter Literal.is_label (Clause.literals cl)) labels;

fun qepcad_arith_simplify_clause cl =
  let val lits = LiteralSet.toList (Clause.literals cl)
      val labels = LiteralSet.filter Literal.is_label (Clause.literals cl)
      val ths = map Clause.thm (List.filter (labels_among labels)(!algebraic_clauses))
      fun decide e lits =
	if Poly.is_algebraic_literal (!Poly.ground_only) e then
	  decision (LiteralSet.fromList (Literal.negate e :: lits)) ths
	else NONE
      fun qepcad_simp_lits_helper cl c [] = cl
        | qepcad_simp_lits_helper cl c (e::l) =
	    case decide e (List.filter (Poly.is_algebraic_literal (!Poly.ground_only)) (c@l)) of
		SOME eth =>
		  (chatting 2 andalso chat ("DELETED literal " ^ Literal.toString e ^ "\nfrom " ^ clause_to_string cl ^ "\n");
		   qepcad_simp_lits_helper (new_clause (Thm.resolve e (Clause.thm cl) eth)) c l)
	      | NONE => qepcad_simp_lits_helper cl (e::c) l
      (* if the clause has been simplified, the original must be stored for possible later *)
      (* restoration on backtracking - this will be done if the label is different         *)
      val new_cl = qepcad_simp_lits_helper cl [] (sort decreasingLitSize lits)
      val cl = if  (equal_cl cl new_cl) then cl else
          let
              val algLabel = Thm.mergeTheoremListLabels (map Clause.thm (!algebraic_clauses))
              val algLabel = Thm.mergeLabels algLabel (Clause.clauseLabel cl)
              val new_cl = Clause.updateLabel new_cl algLabel
          in
              new_cl
          end
  in
    cl
  end;

(*A clause whose algebraic part, when negated, is inconsistent with the other algebraic
  clauses is a logical consequence of them and is therefore redundant.*)
fun clause_is_new cl =
  let val alits = LiteralSet.filter (Poly.is_algebraic_literal (!Poly.ground_only)) (Clause.literals cl)
      val labels = LiteralSet.filter Literal.is_label (Clause.literals cl)
  in if not (LiteralSet.null alits) andalso
        RCF.call_rcf_conj alits
           (map Clause.literals (List.filter (labels_among labels)(!algebraic_clauses)))
     then (chatting 2 andalso chat ("IGNORING [RCF] clause " ^ clause_to_string cl ^ "\n");
	   false)
     else true
  end;

(* Function to check if an algebraic clause is inconsistent with existing algebraic clauses *)
(* if it is then replace it by a suitably labelled empty clause.                            *)
(* This is done by temporarily adding the clause to the algebraic clause and checking for   *)
(* consistency with the empty clause - this avoids various clause negations etc.            *)
fun checkAlgebraicClause cl =
  if is_algebraic_clause (!Poly.ground_only) cl andalso not (Clause.isContradiction cl) then
     case (decision LiteralSet.empty (map Clause.thm (cl::(List.filter (labels_among LiteralSet.empty)(!algebraic_clauses))))) of
	                 SOME ncl =>
                             let
                                 val ncl = new_clause ncl
                                 val _ = chatting 2 andalso chat ("\nclause : " ^ clause_to_string cl ^ "\nis inconsistent with algebraic clauses"
                                                       ^ "\nso has been replaced by : " ^ clause_to_string ncl ^"\n")
                             in
                                ncl
                             end
	               | NONE => cl
  else
    cl;


(* ------------------------------------------------------------------------- *)
(* The main proof loop.                                                      *)
(* ------------------------------------------------------------------------- *)

datatype decision =
    Contradiction of Thm.thm
  | Satisfiable of Thm.thm list;

datatype state =
    Decided of decision
  | Undecided of resolution;

fun iterate resolution =
    let
      val Resolution {parameters,active,waiting,deleted,stack,hidden} = resolution
      val givenClause = if (!outsideSOSCount) > (!maxRunOutsideSOS) then
            (chatting 2 andalso chat ("OutsideSOSCount has reached " ^ Int.toString (!outsideSOSCount) ^
             " which exceeds the limit " ^ Int.toString (!maxRunOutsideSOS) ^ " so giving up.\n"); NONE)
          else Waiting.removeIfValid waiting

(*MetisTrace2
      val () = Print.trace Active.pp "Resolution.iterate: active" active
      val () = Print.trace Waiting.pp "Resolution.iterate: waiting" waiting
*)
    in
      case givenClause of
        NONE =>
           (case (decision LiteralSet.empty (map Clause.thm (List.filter (labels_among LiteralSet.empty)(!algebraic_clauses)))) of
                 SOME cl =>
                     (chatting 2 andalso chat "\nAlgebraic Clauses are inconsistent!!\nNo Clauses in Waiting\n";
	              Undecided (Resolution {parameters = parameters, active = active, waiting = Waiting.add waiting (5.0,[new_clause cl]),
                                                     deleted = deleted, stack = stack, hidden = hidden}))
               | NONE =>
                     (* before giving up, if the number of symbols in algebraic clauses is restricted then remove the restriction *)
                     (* and return all top clauses to waiting.                                                                    *)
                     if (!max_algebraic_clause_syms >= 1000 orelse not (!reRunWithHighMaxAlg)) then
                       Decided (Satisfiable (map Clause.thm (Active.saturation active)))
                     else
                       (* Increase the size of algebraic clause sent to QEPCAD and have another go *)
                       let
			 val _ = chatting 2 andalso chat "Starting second run with maxalg increased to 1001\n"
                         val _ = max_algebraic_clause_syms := 1001
                         val _ = outsideSOSCount := 0
			 val cls = Active.getAllClauses active
			 (* restore any deleted clauses as these might be axioms *)
			 val (deleted,cls) = SplitStack.restoreKeptDeletedClauses deleted cls []
			 fun keep cl = (Clause.getLevel cl) = 0
			 val cls = List.filter keep cls
			 val waiting  = Waiting.new Waiting.default {axioms = [], conjecture = []}
			 val waiting = Waiting.add waiting (~1.0,cls)
			 val parents = SplitStack.returnParents stack
			 val cls = List.filter keep parents
			 val waiting = Waiting.add waiting (~1.0,cls)
			 val active = Active.emptyExisting active
			 val stack = SplitStack.newStack ()
		         (* NB do NOT delete the existing hidden lits as they may be needed for the parents of negated left splits *)
                         (* which may be labelled even when the negated left split itself is top level - see notes 21/9/11         *)
			 (* val hidden : (Literal.literal IntMap.map) = IntMap.new () *)
			 val _ = algebraic_clauses := []
		       in
			   Undecided (Resolution{parameters=parameters,active=active,waiting=waiting,deleted=deleted,stack=stack,hidden=hidden})
		       end)


      | SOME ((w,(d,xcl)),waiting) =>
        let
          val _ = chatting 3 andalso chat ("CLAUSE TAKEN FROM WAITING (" ^ Int.toString (Real.round w) ^ "):\n" ^ clause_to_string xcl ^ "\n")
          val _ = if Clause.inSOS xcl then outsideSOSCount := 0 else outsideSOSCount := (!outsideSOSCount) + 1
          val cl = if  !(maxStackDepth) > 0 then checkAlgebraicClause xcl else xcl (* only do this call if using backtracking splitting *)
          (* if the new given clause xcl has been replaced by the empty clause because it is inconsistent with other algebraic clauses *)
          (* then it needs to be replaced in waiting as backtracking may change the algebraic clauses - see notes dated 27.4.11        *)
          val waiting = if Clause.isContradiction cl andalso not (Clause.isContradiction xcl) then (Waiting.add waiting ((~1.0),[xcl])) else waiting
        in
        if Clause.isContradiction cl then
           if ((Clause.getLevel cl) > 0) then
             let
                 val (cl,SplitStack.ProofState{active = na, waiting = nw, deleted = nd,stack=ns,restored=restored,hidden=hidden}) =
                     SplitStack.backtrack (cl) (SplitStack.ProofState{active=active, waiting=waiting, deleted=deleted, stack=stack, restored=[], hidden=hidden})
                 (* backtracking either returns a top level empty clause or a right branch clause  *)
                 (* for the time being return the right branch to waiting rather than deal with it *)
                 (* immediately.                                                                   *)
                 val result =
                     if (Clause.isContradiction cl) then
                         let
                            (* Restore the hidden literals in cl before returning it *)
                            val th = SplitStack.fullyExpandThm (Clause.thm cl) hidden
                         in
                            Decided (Contradiction th)
                         end
                     else
                        let
                        val _ = chatting 2 andalso not (null restored) andalso
                                             chat ("RESTORED CLAUSES\n" ^ clauses_to_string restored ^ "\n")

                        val _ = chatting 2 andalso chat ("RIGHT BRANCH CLAUSE RETURNED\n" ^ clause_to_string cl ^ "\n")

                        val _ =  filterAlgebraicClauses ns

                        (* 22.3.11 add the right branch clause to the front of the queue *)
                        val nw = Waiting.addToFrontOfQueue cl nw

                         (* add restored and right split clauses into the waiting set *)
                          val nw = Waiting.add nw ((~1.0),restored)
                        in
                            Undecided (Resolution{parameters=parameters,active=na,waiting=nw,deleted=nd,stack=ns,hidden=hidden})
                        end
             in
                 result
             end
          else
             let 
                (* Restore the hidden literals in cl before returning it *)
                val th = SplitStack.fullyExpandThm (Clause.thm cl) hidden
             in
                Decided (Contradiction th)
             end
        else (* Intially test the clause against global algebraic clauses only *)
             if not (clause_is_new cl) then
                (* if the clause is a logical consequence of the existing algebraic clauses it is deleted *)
                (* BUT it must be saved for future possible reinstatement if the algebraic clauses change *)
                (* on backtracking.                                                                       *)
                let
                   val algLabel = Thm.mergeTheoremListLabels (map Clause.thm (!algebraic_clauses))
                   val algLabel = Thm.mergeLabels algLabel (Clause.clauseLabel cl)
                   val new_cl = Clause.updateLabel cl algLabel
                   val deleted = SplitStack.addToDeletedClauses (new_cl,cl) deleted stack
                in
                   Undecided
                        (Resolution
                          {deleted = deleted, stack = stack, parameters = parameters, active = active, waiting = waiting, hidden = hidden})
                end
             else
                let
                   val _ = chatting 2 andalso
                       chat ("GIVEN CLAUSE (" ^ Int.toString (Real.round w) ^ "):\n" ^ clause_to_string cl ^ "\n")
                   val algebraic_cls = if(!allow_sf_in_algebraic_clauses)then
                              List.filter (andf (is_algebraic_clause (!Poly.ground_only))is_small_clause) [cl]
                              else
                              List.filter (andf (is_strictly_algebraic_clause (!Poly.ground_only))is_small_clause) [cl]
                   val algebraic_cls = difference_cl algebraic_cls (!algebraic_clauses)
                   val currentClauseDistance = Clause.clauseDistance cl
                   val _ = chatting 3 andalso
                        chat ("Current Clause Distance : " ^ realToString 1 currentClauseDistance ^ "\n")
                   val _ = algebraic_clauses := algebraic_cls @ (!algebraic_clauses);
                   val _ = (null algebraic_cls orelse
		         chatting 2 andalso
		         chat ("new algebraic clauses\n" ^ clauses_to_string algebraic_cls ^ "\n")
		         andalso
                         chatting 3 andalso
                         chat ("algebraic clauses\n" ^ clauses_to_string (!algebraic_clauses) ^ "\n"))
                  (* -------------------------------------------------------------------------- *)
                  (* attempt to case split the clause and replace it with the left branch split *)
                  (* if possible.                                                               *)
                  (* -------------------------------------------------------------------------- *)
                  (* 16.3.11 this has been changed to a function to allow the splitting to occur *)
                  (* after the call to decision below - this leads to a very small improvement   *)
                   fun splitClause (cl,stack,deleted) =
                         if ((SplitStack.stackDepth stack) < !(maxStackDepth)) then
                            case (Active.caseSplitClause cl) of
                                   NONE => (cl,stack,deleted)
                              |    SOME (clLeft,clRight) =>
                                     let
                                        val _ = chatting 2 andalso chat ("LEFT SPLIT CLAUSE :\n" ^ clause_to_string clLeft ^ "\n")
                                        val _ = chatting 2 andalso chat ("RETAINED RIGHT SPLIT CLAUSE :\n" ^ clause_to_string clRight ^ "\n")
                                        val (cl,stack) = SplitStack.caseSplit (cl, clLeft, clRight, stack)
                                     in
                                        (cl,stack,deleted)
                                     end
                         else
                                     (cl,stack,deleted)
                 (* -------------------------------------------------------------------------- *)
                 (* First attempt to simplify the clause before splitting etc.                 *)
                 (* but only do this if not doing LCP splitting - i.e. if maxStackDepth is > 0 *)
                 (* -------------------------------------------------------------------------- *)
                  val (active,clo) = if !(maxStackDepth) > 0 then Active.simplify active cl else (active,SOME cl)
                  val unsimplified = case clo of NONE => false | SOME cl' => Clause.equalThms cl cl'
                  val (cl',stack,deleted) = case clo of
                             NONE => (cl,stack,deleted)
                           | SOME c => if Clause.isContradiction c then (c,stack,deleted) else splitClause (c,stack,deleted)
                  val (active,cls) = if !(maxStackDepth) = 0 then
                                         (* ----------------------------------------------------------------------- *)
                                         (* for consistency with past code check for inconsistent algebraic clauses *)
                                         (* this is not needed for the backtracking case as a check was done at the *)
                                         (* beginning.                                                              *)
                                         (* ----------------------------------------------------------------------- *)
                                         case decision LiteralSet.empty
                                               (map Clause.thm (List.filter (labels_among LiteralSet.empty)
                                               (!algebraic_clauses))) of
		                                SOME cl => (chatting 2 andalso
		                                   chat "\nAlgebraic Clauses are inconsistent!!\n";(active, [new_clause cl]))
		                              | NONE => Active.add active cl
                                     else
                                        case clo of NONE => (active,[]) | SOME c =>
                                              if Clause.isContradiction c then (active,[c]) else
                                              if unsimplified then Active.addAndFactor active cl' else Active.factorOnly active cl'
                (* ---------------------------------------------------------------------------------------- *)
                (* any clause simplified by qepcad in the context of the current algebraic clauses may need *)
                (* to be reinstated on backtracking so must be saved.                                       *)
                (* ---------------------------------------------------------------------------------------- *)
                (* val cls = map qepcad_arith_simplify_clause cls *)
                 val (cls,deleted) =
                   let
                      fun process [] done deleted = (done,deleted)
                       |  process (c::rest) done deleted =
                          let
                            (* try to simplify with only the global (top split level) clauses first *)
                             val qc = qepcad_arith_simplify_clause c
                             val deleted =
                                  if Clause.labelsDifferent qc c then
                                      (SplitStack.addToDeletedClauses (qc,c) deleted stack)
                                  else
                                      deleted
                          in
                            process rest (qc::done) deleted
                          end
                  in
                     process cls [] deleted
                  end
                val _ = chatting 2 andalso not (null cls) andalso
                        chat ("NEW CLAUSES\n" ^ clauses_to_string cls ^ "\n")
               (* ------------------------------------------------- *)
               (* Update the distance value for all the new clauses *)
               (* ------------------------------------------------- *)
                val newDistance = if !(maxStackDepth) = 0 then
                          currentClauseDistance + (Math.ln (Real.fromInt (length cls))*1.5)
                       else
                          currentClauseDistance + (Real.fromInt (((List.length cls)+1) div 2))

                val cls = Clause.setClauseListDistance newDistance cls
                val waiting = Waiting.add waiting (d,cls)
               (* ------------------------------------------------------------------------- *)
               (* transfer any deleted clauses from the subs structure to the deleted list  *)
               (* this is done on backtracking but is also done here to prevent the deleted *)
               (* list getting too big within the subs structure.                           *)
               (* ------------------------------------------------------------------------- *)
                val (SplitStack.ProofState{active=active, waiting=waiting , deleted=deleted ,stack=stack, hidden=hidden, ...}) =
                     SplitStack.transferDeletedClauses (SplitStack.ProofState{active=active, waiting=waiting , deleted=deleted ,stack=stack,
                                                                                restored = [],hidden = hidden})
            in
                 Undecided(Resolution
                        {deleted = deleted, stack = stack, parameters = parameters, active = active, waiting = waiting, hidden = hidden})
            end
         end
    end;

fun loop resolution =
    case iterate resolution of
      Decided decision => decision
    | Undecided resolution => loop resolution;

end
