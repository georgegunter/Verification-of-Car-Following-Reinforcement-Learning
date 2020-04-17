(* ========================================================================= *)
(* THE WAITING SET OF CLAUSES                                                *)
(* Copyright (c) 2001 Joe Hurd, distributed under the MIT license            *)

(* ========================================================================= *)
(* Modified to allow for clause deletion when a split level is removed.      *)
(* Rather than deleting clauses from the heap, instead a list of deleted     *)
(* levels is kept and a new function removeIfValid is provided that checks   *)
(* clause labels against the deleted list.      JPB 21.2.11                  *)
(* ========================================================================= *)
(* modified 22.3.11 to allow clauses to be added to the front of the Queue   *)
(* ========================================================================= *)
(* Modified 31.3.11 to deal with multiple empty clauses and to ensure there  *)
(* is one empty clause which is removed first before even priority clauses.  *)
(* ========================================================================= *)
(* Modified 9.5.11 to deal with labels with -ve entries which were           *)
(* introduced to mark hidden lits for later restoration in the final proof.  *)
(* ========================================================================= *)
(* Non SOS clauses have an extra weighting factor. This version 22.6.11      *)
(* ========================================================================= *)

structure Waiting :> Waiting =
struct

open Useful;

(* ------------------------------------------------------------------------- *)
(* A type of waiting sets of clauses.                                        *)
(* ------------------------------------------------------------------------- *)

type weight = real;

type modelParameters =
     {model : Model.parameters,
      initialPerturbations : int,
      maxChecks : int option,
      perturbations : int,
      weight : weight}

type parameters =
     {symbolsWeight : weight,
      variablesWeight : weight,
      literalsWeight : weight,
      labelWeight : weight,
      models : modelParameters list};

(* Modified to make type visible to SplitStack.sml JPB 8.2.11 *)
type distance = real;

type deletedSplits = int list;

datatype waiting =
    Waiting of
      {parameters : parameters,
       deletedSplits : deletedSplits,
       clauses : (weight * (distance * Clause.clause)) Heap.heap,
       priorityClauses : Clause.clause list, (* introduced to allow clauses to be put in the front of the queue *)
       emptyClause : Clause.clause option, (* only the empty clause with the shortest label is kept *)
       models : Model.model list};


(* Weighting factor to be applied to clauses not in the SOS *)
val SOSweightFactor = ref 2.0


(* ------------------------------------------------------------------------- *)
(* Basic operations.                                                         *)
(* ------------------------------------------------------------------------- *)

val default : parameters =
     {symbolsWeight = 1.0,
      literalsWeight = 0.1,  (*Many of our proofs involve clauses with six literals or more*)
      variablesWeight = 0.4,
      labelWeight = 0.0,
      models = []};  (*LCP: Getting rid of models makes a big, overall improvement*)

fun size (Waiting {clauses,...}) = Heap.size clauses;

val pp =
    Print.ppMap
      (fn w => "Waiting{" ^ Int.toString (size w) ^ "}")
      Print.ppString;

(*MetisDebug
val pp =
    Print.ppMap
      (fn Waiting {clauses,...} =>
          map (fn (w,(_,cl)) => (w, Clause.id cl, cl)) (Heap.toList clauses))
      (Print.ppList (Print.ppTriple Print.ppReal Print.ppInt Clause.pp));
*)

(* ------------------------------------------------------------------------- *)
(* Perturbing the models.                                                    *)
(* ------------------------------------------------------------------------- *)

type modelClause = NameSet.set * Thm.clause;

fun mkModelClause cl =
    let
      val lits = Clause.literals cl
      val fvs = LiteralSet.freeVars lits
    in
      (fvs,lits)
    end;

val mkModelClauses = map mkModelClause;

fun perturbModel M cls =
    if null cls then K ()
    else
    let
        val N = {size = Model.size M}

      fun perturbClause (fv,cl) =
          let
              val V = Model.randomValuation N fv
          in
              if Model.interpretClause M V cl then ()
              else Model.perturbClause M V cl
          end

        fun perturbClauses () = app perturbClause cls
            in
        fn n => funpow n perturbClauses ()
    end;

fun initialModel axioms conjecture parm =
    let
      val {model,initialPerturbations,...} : modelParameters = parm
      val m = Model.new model
      val () = perturbModel m conjecture initialPerturbations
      val () = perturbModel m axioms initialPerturbations
    in
      m
    end;

(* ------------------------------------------------------------------------- *)
(* Clause weights.                                                           *)
(* ------------------------------------------------------------------------- *)

local
  fun clauseSymbols cl = Real.fromInt (LiteralSet.typedSymbols cl) / 100.0;

  fun clauseVariables cl =
      Real.fromInt (NameSet.size (LiteralSet.freeVars cl) + 1);

  fun clauseLiterals cl = Real.fromInt (LiteralSet.size cl);

  fun priority cl = Math.ln (Real.fromInt (Clause.id cl)) / 10.0;  (*LCP*)
in
  fun clauseWeight (parm : parameters) mods dist mcl cl =
      let
         (* ---------------------------------------------------------------------------------- *)
         (* 8.4.11 try to split the clause and use only the left split to calculate the weight *)
         (* ---------------------------------------------------------------------------------- *)
         (* this proved a slightly retrograde step - on the 31 problems it proves only 19
            down from 23 and on the full set it proves 601 instead of 602 but is rather slower...
         val cl = case (Active.caseSplitClause cl) of
                                   NONE => cl
                              |    SOME (clLeft,_) => clLeft
         *)
         (* ----------------------------------------------------------------------------------- *)
(*MetisTrace3
        val () = Print.trace Clause.pp "Waiting.clauseWeight: cl" cl
*)
        val {symbolsWeight,variablesWeight,literalsWeight,labelWeight,models,...} = parm
        val labelLength = 1.0 + Real.fromInt (Clause.clauseLabelLength cl)
        val lits = Clause.literals cl
        val symbolsW = Math.pow (clauseSymbols lits, symbolsWeight)
        val variablesW = Math.pow (clauseVariables lits, variablesWeight)
        val literalsW = Math.pow (clauseLiterals lits, literalsWeight)
        (* val labelW = Math.pow (labelLength, labelWeight) *)
        (* Set the distance from the clause itself *)
         val dist =  Clause.clauseDistance cl

(*MetisTrace4
        val () = trace ("Waiting.clauseWeight: dist = " ^
                        Real.toString dist ^ "\n")
        val () = trace ("Waiting.clauseWeight: symbolsW = " ^
                        Real.toString symbolsW ^ "\n")
        val () = trace ("Waiting.clauseWeight: variablesW = " ^
                        Real.toString variablesW ^ "\n")
        val () = trace ("Waiting.clauseWeight: literalsW = " ^
                        Real.toString literalsW ^ "\n")
        val () = trace ("Waiting.clauseWeight: modelsW = " ^
                        Real.toString modelsW ^ "\n")
*)
        val weight = (* labelW * *) dist * symbolsW * variablesW * literalsW  + priority cl

       (* Increase the weight of clauses not in SOS *)
        val weight = if (not (Clause.inSOS cl)) then (!SOSweightFactor) * weight else weight

(*MetisTrace3
        val () = trace ("Waiting.clauseWeight: weight = " ^
                        Real.toString weight ^ "\n")
*)
      in
        weight
      end;
end;

(* ------------------------------------------------------------------------- *)
(* Adding new clauses.                                                       *)
(* ------------------------------------------------------------------------- *)

(*Limiting the weight of retained clauses reduces memory usage, which can be critical
  when multiple jobs are executed. The maximum weight observed in a proof is 905.
  We choose a limit ample for the great majority of problems.*)
val maxweight = ref 1000.0;     
val maxweight_used = ref 0.0;
val maxweightSet = ref false;

fun set_maxweight w = let val _ = maxweightSet := true in maxweight := Real.fromInt w end;
  
fun add' waiting dist mcls cls =
    let
      val Waiting {deletedSplits,parameters,clauses,models,priorityClauses,emptyClause} = waiting
      val {models = modelParameters, ...} = parameters

      val dist = (if dist < 0.0 (*from new*) then 2.5
                  else dist + Math.ln (Real.fromInt (length cls))*1.5)


      fun addCl ((mcl,cl),acc) =
          let
            val weight = clauseWeight parameters models dist mcl cl
          in
            if weight > !maxweight then acc else Heap.add acc (weight,(dist,cl))
          end

      val clauses = List.foldl addCl clauses (zip mcls cls)
    in
      Waiting {deletedSplits = deletedSplits, parameters = parameters, clauses = clauses, models = models,
               priorityClauses = priorityClauses, emptyClause = emptyClause}
    end;


(* fun to add an empty clause but only if its label is shorter than that of any *)
(* existing empty clause.                                                       *)

fun addEmptyClause cl (waiting as Waiting {parameters,clauses,models,deletedSplits,priorityClauses,emptyClause}) =
    case emptyClause of
        NONE =>
           let
             val waiting =
                    Waiting
                       ({parameters = parameters, clauses = clauses, models = models,
                         deletedSplits = deletedSplits, priorityClauses = priorityClauses,
                         emptyClause = (SOME cl)})
           in
              waiting
           end
      | SOME cl' =>
           let
              val label = Clause.clauseLabel cl
              val label' = Clause.clauseLabel cl'
              val waiting = if ((List.length label) < (List.length label')) then
                                Waiting
                                ({parameters = parameters, clauses = clauses, models = models,
                                  deletedSplits = deletedSplits, priorityClauses = priorityClauses,
                                  emptyClause = (SOME cl)})
                            else
                                waiting
            in
                waiting
            end;  

(* fun to look for any empty clauses in the clause list *)
fun dealWithEmptyClauses waiting [] = waiting
 |  dealWithEmptyClauses waiting (cl::rest) =
        if Clause.isContradiction cl then dealWithEmptyClauses (addEmptyClause cl waiting) rest
                                     else dealWithEmptyClauses waiting rest;


fun add waiting (_,[]) = waiting
  | add waiting (dist,cls) =
    let
(*MetisTrace3
      val () = Print.trace pp "Waiting.add: waiting" waiting
      val () = Print.trace (Print.ppList Clause.pp) "Waiting.add: cls" cls
*)

      val waiting = dealWithEmptyClauses waiting cls
      val waiting = add' waiting dist (mkModelClauses cls) cls

(*MetisTrace3
      val () = Print.trace pp "Waiting.add: waiting" waiting
*)
    in
      waiting
    end;

(* Add a clause to the front of the queue by adding it to priorityClauses rather than the heap *)



local
  fun cmp ((w1,_),(w2,_)) = Real.compare (w1,w2);

  fun empty parameters axioms conjecture =
      let
        val {models = modelParameters, ...} = parameters
        val clauses = Heap.new cmp
        and models = map (initialModel axioms conjecture) modelParameters
      in
        Waiting {parameters = parameters, clauses = clauses, models = models,
                 deletedSplits = [], priorityClauses = [], emptyClause = NONE}
      end;
in
  fun new parameters {axioms,conjecture} =
      let
        val mAxioms = mkModelClauses axioms
        and mConjecture = mkModelClauses conjecture

        val waiting = empty parameters mAxioms mConjecture
      in
        add' waiting ~1.0 (mAxioms @ mConjecture) (axioms @ conjecture)
      end;
end;

(* ------------------------------------------------------------------------- *)
(* Removing the lightest clause.                                             *)
(* ------------------------------------------------------------------------- *)

fun remove (Waiting {parameters,clauses,models,deletedSplits,priorityClauses,emptyClause}) =
    (* first check if there is an empty clause waiting to pop out *)
    case emptyClause of
        SOME cl =>
             let
               val waiting =
                        Waiting
                        {parameters = parameters, clauses = clauses, models = models,
                         deletedSplits = deletedSplits, priorityClauses=priorityClauses, emptyClause = NONE}
             in
                SOME ((0.0,(0.0,cl)),waiting)
             end
       |  NONE =>
    (* if no empty clause look first in the priority clause list *)
    if (List.null priorityClauses) then
       if Heap.null clauses then
           NONE
       else
          let
            val ((w,dcl),clauses) = Heap.remove clauses
            val () = maxweight_used := Real.max (!maxweight_used,w)
            val waiting =
               Waiting
               {parameters = parameters, clauses = clauses, models = models,
                deletedSplits = deletedSplits, priorityClauses=priorityClauses, emptyClause = NONE}
          in
               SOME ((w,dcl),waiting)
          end
     else
          let
              val cl = hd priorityClauses
              val priorityClauses = tl priorityClauses
              val waiting =  
               Waiting
               {parameters = parameters, clauses = clauses, models = models,
                deletedSplits = deletedSplits, priorityClauses=priorityClauses, emptyClause = NONE}
          in
               SOME ((0.0,(0.0,cl)),waiting)
          end;

fun removeIfValid (waiting as Waiting{deletedSplits,...}) =
    let
       fun deleted cl =
          let
              val label = Clause.clauseLabel cl
              fun mem x [] = false
                 |mem x (y::xs) = if (Int.abs x)=(Int.abs y) then true
                       else mem x xs
              fun oneCommon _ [] = false
                 |oneCommon [] _ = false
                 |oneCommon (x::xs) l =
                     if mem x l then true
                     else oneCommon xs l
           in
               oneCommon label deletedSplits
           end
     in
       case remove (waiting) of
            NONE => NONE
         | SOME ((w,(d,wcl)),wset) =>
                if deleted wcl then removeIfValid (wset)
                else SOME ((w,(d,wcl)),wset)
     end

(* Deleting invalid clauses - clauses made invalid by the deletion of *)
(* a split on which they are dependent for existence! At present a    *)
(* lazy approach is used by which the split level is just added to    *)
(* a list and the clauses are only deleted when they are extracted by *)
(* the function removeIfValid.                                        *)

fun deleteClauses split (Waiting {parameters,clauses,models,deletedSplits,priorityClauses,emptyClause}) =
   let
      val deletedSplits = split :: deletedSplits
      val waiting =
          Waiting
            ({parameters = parameters, clauses = clauses, models = models,
              deletedSplits = deletedSplits, priorityClauses = priorityClauses,
              emptyClause = emptyClause})
    in
      waiting
    end

fun addToFrontOfQueue cl (Waiting {parameters,clauses,models,deletedSplits,priorityClauses,emptyClause}) =
   let
      val priorityClauses = cl::priorityClauses
      val waiting =
          Waiting
            ({parameters = parameters, clauses = clauses, models = models,
              deletedSplits = deletedSplits, priorityClauses = priorityClauses,
              emptyClause = emptyClause})
    in
      waiting
    end

                    
(* DEBUG CODE *)
fun printDeletedSplits (waiting as Waiting {parameters,clauses,models,deletedSplits,priorityClauses,emptyClause}) message =
   let
     fun splitsToString [] = ""
       | splitsToString (spl::spls) = ":" ^ (Int.toString spl) ^ ":" ^ (splitsToString spls)
     val _ = print ("\n***************************************\nDeleted Splits " ^ message ^ " : " 
                    ^ (splitsToString deletedSplits) ^ "\n***************************************\n")
   in
     waiting
   end

 
         
end




 
