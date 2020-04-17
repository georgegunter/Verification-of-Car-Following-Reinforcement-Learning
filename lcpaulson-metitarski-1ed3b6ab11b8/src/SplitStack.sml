(* =========================================================================== *)
(* Code to operate the split stack               JPB 31/1/11                   *)
(* The split stack is in two parts with the deleted clauses and their          *)
(* associated levels kept separately from the main split stack.                *)
(* This version  13.1.12                                                       *)
(* =========================================================================== *)
(* 1st March 2011 - changed the deletedClauses to contain the subsuming clause *)
(* rather than the level, with appropriate changes to the reinstatement        *)
(* routines.                                                                   *)
(* ___________________________________________________________________________ *)
(* 11th March 2011 - added to the ProofState datatype to include a list of     *)
(* clauses to be restored, this allows them to be filtered with QEPCAD by      *)
(* Resolution.sml before they are added back into waiting.                     *)
(* --------------------------------------------------------------------------- *)
(* 6th May 2011 - modified to allow for new type of clause labels which can    *)
(* contain negative elements to indicate hidden literals (which are restored   *)
(* at the end of the search when the proof is produced).                       *)
(* --------------------------------------------------------------------------- *)
(* 16th May 2012 - modified to allow splitting of algebraic clauses to remove  *)
(* single literals which "probably" can be deleted - these are split off as    *)
(* right case splits and then are tested only if the left case split (the rest *)
(* of the clause) is reduced to the empty clause.                              *)
(* --------------------------------------------------------------------------- *)


structure SplitStack :> SplitStack =
struct

open Useful; (* don't know if this is needed yet *)

(* Flags to indicate type of proof reconstruction to be used *)
val breadthFirstProof =  ref false;
val replayProofDecisions = ref false;



(* ---------------------------------------- *)
(* types of deleted clauses and split stack *)
(* ---------------------------------------- *)

type deletedClauses = (Thm.clauseLabel * Clause.clause) list

(* the set B of blocked clauses can contain zero (if it is a right branch), *)
(* one (just the right branch clause) NB blocked negated left clause is kept*)
(* in positive form and negated when it is added back in as the negated form*)
(* is a list of clauses and the empty clause that becomes the leaf marker   *)
(* is also needed as a parent clause so negation is done when the enterRight*)
(* operation is performed.                                                  *)
(* For simplicity the two clauses will be separate entries.                 *)
(* The parent clause is explicitly stored as it is given special treatment. *)

datatype stackEntry = StackEntry of {level : int,
                   blockedRB : Clause.clause option,
                   blockedLB : Clause.clause option,
                   parent : Clause.clause option,
                   leafMarker : Thm.thm option};

type splitStack = stackEntry list;


datatype proofState = ProofState of { active : Active.active,
                        waiting : Waiting.waiting,
                        deleted : deletedClauses,
                        stack : splitStack,
                        restored : Clause.clause list,
                        hidden : Literal.literal IntMap.map}; (* hidden lits from negated splits are added here indexed by their split label *)
(* newID from Clause slightly modified to increment by 2 *)
val nextLeft =
    let
      val r = ref 1
    in
      fn () => case r of ref n => let val () = r := n + 2 in n end
    end;

fun newStack () = [StackEntry{level = 0,blockedRB = NONE,blockedLB = NONE,parent = NONE, leafMarker = NONE}];

fun newDeletedClauses () = [];

fun newHiddenLiterals () = IntMap.new ();

fun newProofState ps = ProofState(ps);

fun stackDepth stack = (List.length stack) - 1;

(* ------------------------------------------------------------------------- *)
(* Chatting.                                                                 *)
(* ------------------------------------------------------------------------- *)

fun literal_to_string cl = Print.toString Literal.pp cl;

fun clause_to_string cl = Print.toString Clause.pp cl (* ^ Thm.inferenceToString (Thm.inference (Clause.thm cl))*);

 fun clauses_to_string cls = Print.toString (Print.ppList Clause.pp) cls;
(*fun clauses_to_string [] = "\n============= END OF CLAUSES ===============\n"
 |  clauses_to_string (cl::cls) = clause_to_string cl ^ clauses_to_string cls;
*)

fun thm_to_string th = Print.toString Thm.pp th ^ Thm.inferenceToString (Thm.inference th);
fun thms_to_string [] = "\n=============== END OF THMS ===================\n"
 |  thms_to_string (th::ths) = thm_to_string th ^ thms_to_string ths;


(* ------------------------------------------------------------------------ *)
(* 14.4.11 Function to check if a parent clause already exists on the stack *)
(*         used in multi-splitting to stop duplication of parent clauses on *)
(*         backtracking. The clause is identified by its id (suprisingly!)  *)
(* ------------------------------------------------------------------------ *)

fun alreadyInStack id [] = false
 |  alreadyInStack id (e::es) =
    let
        val StackEntry{parent,...} = e
    in
        case parent of
           NONE => alreadyInStack id es
         | SOME cl =>
             if (id = Clause.id cl) then true
             else alreadyInStack id es
    end;



(* a couple of useful functions for checking labels *)
(* labels are ordered lists of ints with the max as *)
(* the first element.                               *)
(* 9.5.11 some may have a -ve sign but are still    *)
(* ordered in terms of magnitude.                   *)
fun isInLabel i [] = false
 |  isInLabel i (j::rest) =
       if (Int.abs i) > (Int.abs j) then false
       else
          if (Int.abs i) = (Int.abs j) then true
          else
              isInLabel i rest

fun isSubLabel [] _ = true
 |  isSubLabel (i::rest) label =
       isInLabel i label andalso isSubLabel rest label

fun stackToLabel stack =
    let
        fun getLevel (StackEntry {level,...}) = level
        fun process [] label = label
         |  process (e::rest) label =
                    process rest ((getLevel e)::label)
        val label = rev (process stack [])
    in
       label
    end

(**************************************************************)
(* Function to filter out clauses from a list that are not    *)
(* valid due to their labels containing deleted stack levels. *)
(**************************************************************)
fun filterClauseList cls stack =
   let
      val stackLabel = stackToLabel stack
      fun filter [] fcls = fcls
       |  filter (cl::rest) fcls =
          let
             val label = Clause.clauseLabel cl
          in
             if isSubLabel label stackLabel then
                filter rest (cl::fcls)
             else
                filter rest fcls
           end
   in
      filter cls []
   end;


(*************************************************************)
(* Function to filter a rewrite structure removing equations *)
(* that are not valid due to their labels containing deleted *)
(* stack levels.                                             *)
(*************************************************************)
fun filterRewrite rw stackLabel =
   let
       val rw = Rewrite.reduce rw (* ensure it is reduced to start *)
       val known = Rewrite.getKnown rw
       val order = Rewrite.getOrder rw
       val rwl = IntMap.toList known
       val nrw = Rewrite.new order
       fun eqnLabel (_,thm) = Thm.clauseLabel thm
       fun filter [] frw = frw
        |  filter ((id,(eqn,ort))::rest) frw =
              let
                 val label = eqnLabel eqn
                 val frw =
                     if isSubLabel label stackLabel then
                        Rewrite.add frw (id,eqn)
                     else
                        frw
              in
                 filter rest frw
              end
        val rw = filter rwl nrw
        val rw = Rewrite.reduce rw (* reduce it again at the end *)
     in
        rw
     end;

(* DEBUG CODE to print out the stack *)

(* val debug = ref true; *)

fun printSubsumedClauses (ProofState {active,...})=
   let
       fun printSub (scl,cl) =
          "Subsuming clause : \n" ^ Print.toString Clause.pp scl ^ "\nSubsumed Clause : \n" ^ Print.toString Clause.pp cl ^ "\n"
       fun printAllSub [] = "\n++++++++++++++++++++++++++\n"
        |  printAllSub (sp::sps) =
              printSub sp ^ printAllSub sps
       val (_,dc) = Active.extractDeleted active
       val s = "\nSubsuming and Subsumed clauses : \n+++++++++++++++++++++++++++\n" ^ printAllSub dc
    in
       print s
    end



fun printStackLevel (StackEntry({level, blockedRB, blockedLB, parent, leafMarker})) =
let
    val s = "\nStack entry : level : " ^ (Int.toString level) ^ "\n"
    val s = if isSome (blockedRB) then s ^ "RB Clause : " ^ Print.toString Clause.pp (Option.valOf blockedRB)  ^ "\n"
                                  else s ^ "no blocked RB clause\n"
    val s = if isSome (blockedLB) then s ^ "LB Clause : "^ Print.toString Clause.pp (Option.valOf blockedLB) ^ "\n"
                                   else s ^ "no blocked NLB clause\n"
    val s = if isSome (parent) then s ^ "parent Clause : " ^ Print.toString Clause.pp (Option.valOf parent) ^ "\n"
                               else s ^ "no parent clause\n"
    val s = if isSome (leafMarker) then s ^ "leaf marker Clause : " ^ Print.toString Thm.pp (Option.valOf leafMarker) ^ "\n"
                                   else s ^ "no leaf marker clause\n"
in
    s
end

fun dumpStack [] = "end of stack dump\n"
   |dumpStack (e::es) = (printStackLevel e) ^ (dumpStack es)

fun printStack message stack =
    let
       val s = message ^  dumpStack stack
    in
       print s
    end

fun printTheorem thm =
   let
      val s = "Current thm : " ^ Print.toString Thm.pp thm ^ "\n"
   in
      print s
   end

fun printMessageAndTheorem message thm =
   let
      val s = "\n" ^ message ^ Print.toString Thm.pp thm ^ "\n"
   in
     print s
   end

fun printLevel l =
   let
      val s = "Level : " ^ (Int.toString l) ^ "\n"
   in
      print s
   end
fun printLabel l =
  let
    fun pr [] = "}\n"
      | pr (l::ls) = ":" ^ (Int.toString l) ^ pr ls
    val s = "{" ^ pr l
  in
    print s
  end

fun printDeleted (ProofState {deleted,...}) =
  let
     val s = "\n*************************\nCurrently saved deleted clauses : \n"
     fun pd [] = "\n************************\n"
      |  pd ((scl,cl)::rest) = "\nSubsuming clause label : " ^  (Thm.labelToString scl) ^
                            "\nSubsumed clause : " ^ Print.toString Clause.pp cl ^ pd rest
     val s = s ^ (pd deleted)
  in
     print s
  end

fun clauseListToString [] = ">>>>>>> End of Clause List <<<<<<<<<<\n"
 |  clauseListToString (cl::cls) = Print.toString Clause.pp cl ^ "\n" ^ clauseListToString cls


fun printClauseList message cls =
    let
        val s = message ^ clauseListToString cls
    in
        print s
    end

(* END OF DEBUG CODE *)
(* ----------------------------------------------------------------------------------- *)
(* Function to restore all hidden literals once the final empty clause has been found  *)
(* the code to do this has been added here as I had problems in adding it to Proof.sml *)
(* JPB 11.5.11                                                                         *)
(* 16.5.11 Code rewritten to do the job in two phases - phase 1 is collecting all      *)
(* unique literal sets with associated thms (the LAST thm encountered with that set   *)
(* of literals - no attempt to optimise in terms of number of parents etc). To produce *)
(* a full proof the literal sets could be named as part of this process. During phase 1*)
(* the thms will also be placed in a list waiting to be processed. In phase 2 the list *)
(* is processed (should be in one pass).              The processing consists of       *)
(* transferring any thm with all parents already in a new "known" map to the "known"   *)
(* map. Any parent thm whose literal set is in "known" will be replaced by the thm in  *)
(* "known" with the same literal set thus ensuring all ancestors are also "known". The *)
(* replacement of parents will occur for thms in the list to be processed even if all  *)
(* parents are not yet in "known". Obviously the only thms to added to "known"         *)
(* initially will be those with no parents (e.g. axioms and assumes).                  *)
(* ----------------------------------------------------------------------------------- *)
local
  val emptyThms : Thm.thm LiteralSetMap.map = LiteralSetMap.new ();

 (* ------------------------------------------------------------------------------------ *)
 (* functions to minimise the number of algebraic clauses listed as parents in decisions *)
 (* ------------------------------------------------------------------------------------ *)

  fun decision lits thms = SOME (Thm.decision lits thms) handle Error _ => NONE

  fun decisionValid lits thms = case decision lits thms of SOME _ => true | NONE => false

  fun reduceParents lits needed [] flag = (needed,flag)
   |  reduceParents lits needed (p::ps) flag =
        if decisionValid lits (needed @ ps) then
                 reduceParents lits needed ps true
        else
                 reduceParents lits (p::needed) ps flag;

  fun minimizeParents lits parents flag =
      if flag then
         let
            val (parents,flag) = reduceParents lits [] parents false
         in
            minimizeParents lits parents flag
         end
      else
         parents;

  fun replay_decision th =
     if(Thm.isDecision th) then
        let
           val _ = chatting 2 andalso chat ("\nBefore minimization : \n" ^ Thm.extendedToString th)
           val parents = minimizeParents (Thm.clause th) (Thm.parents th) true
           val th = Thm.setParents th parents
           val _ = chatting 2 andalso chat ("\nAfter minimization : \n" ^ Thm.extendedToString th)
           val _ = if decisionValid (Thm.clause th) parents then () else raise Error "Decision invalid!!\n"
        in
           th
        end
     else
        (chatting 3 andalso chat ("\nClause returned without rerunning decision : \n" ^ Thm.extendedToString th);th);

  (* --------------------------------------------------------------------------------- *)
(* -------------------------------------------------------------------------------------- *)
(* Stack and Queue implemented as 2 maps, same structure is used for both as clause count *)
(* ensures that the latest clause goes on the end and then if it is a queue the oldest    *)
(* clause is removed and if it is a stack the most recent clause is removed.              *)
(* -------------------------------------------------------------------------------------- *)
datatype thmQueueOrStack = ThmQueueOrStack of ((Thm.thm * Int.int) LiteralSetMap.map) * (LiteralSet.set IntMap.map);

val emptyThmMap : (Thm.thm * Int.int) LiteralSetMap.map = LiteralSetMap.new ()
val emptyLitMap : LiteralSet.set IntMap.map = IntMap.new ()
val emptyStack  = ThmQueueOrStack(emptyThmMap,emptyLitMap);
val emptyQueue = emptyStack;

fun addThm hidden (qORs as ThmQueueOrStack (thmMap,litMap)) (th,count) =
   let
       val lits = Thm.clause (Thm.restoreHiddenLits th hidden)
   in
       case LiteralSetMap.peek thmMap lits of 
            SOME (thx,cx) => if cx < count then
                                     (* replace - need to delete old *)
                                      let
                                          val litMap = IntMap.delete litMap cx
                                          val litMap = IntMap.insert litMap (count,lits)
                                          val thmMap = LiteralSetMap.insert thmMap (lits,(th,count))
                                      in
                                          ThmQueueOrStack(thmMap,litMap)
                                      end
                              else ThmQueueOrStack(thmMap,litMap) (* don't replace *)
         | NONE  => (* new so can just insert *)
                    let
                        val litMap = IntMap.insert litMap (count,lits)
                        val thmMap = LiteralSetMap.insert thmMap (lits,(th,count))
                    in
                        ThmQueueOrStack(thmMap,litMap)
                    end
     end;

fun addThmList hidden thmQorS [] count = (thmQorS,count)
 |  addThmList hidden thmQorS (th::ths) count = addThmList hidden (addThm hidden thmQorS (th,count)) ths (count+1);

fun deQueueThm (ThmQueueOrStack(thmMap,litMap)) =
    if (IntMap.size litMap) < 1 then NONE else
    let
	val (count,lits) = IntMap.nth litMap 0
        val litMap = IntMap.delete litMap count
        val (thx,cx) = LiteralSetMap.get thmMap lits
        val thmMap = LiteralSetMap.delete thmMap lits
        val _ = if cx = count then () else raise Error "SplitStack.deQueueThm structure corrupt"
    in
        SOME (ThmQueueOrStack(thmMap,litMap),thx,cx)
    end;

fun popThm (ThmQueueOrStack(thmMap,litMap)) =
    let
       val size = IntMap.size litMap
    in
       if size < 1 then NONE else
          let
              val n = size-1
              val (count,lits) = IntMap.nth litMap n
              val litMap = IntMap.delete litMap count
              val (thx,cx) = LiteralSetMap.get thmMap lits
              val thmMap = LiteralSetMap.delete thmMap lits
              val _ = if cx = count then () else raise Error "SplitStack.popThm structure corrupt"
          in
              SOME (ThmQueueOrStack(thmMap,litMap),thx,cx)
          end
     end;

(* function to replace a th with a matching one from the stack *)
(* the major change being in the parents and ancestors         *)
fun replaceThm hidden (ThmQueueOrStack(thmMap,_)) th =
    case LiteralSetMap.peek thmMap (Thm.clause (Thm.restoreHiddenLits th hidden)) of
         SOME (thx,cx) => thx
      |  NONE => th;    

fun replaceThmList hidden stack [] done = done
 |  replaceThmList hidden stack (th::ths) done =
        replaceThmList hidden stack ths ((replaceThm hidden stack th)::done);    

fun thmInStack hidden (ThmQueueOrStack(thmMap,_)) th =
    case LiteralSetMap.peek thmMap (Thm.clause (Thm.restoreHiddenLits th hidden)) of
         SOME (thx,cx) => true
      |  NONE => false;    
              
fun checkStack hidden (qORs as ThmQueueOrStack(thmMap,litMap)) =
    let
        val lst = LiteralSetMap.toList thmMap
        fun allParents [] pars = pars
         |  allParents ((_,(th,_))::rest) pars =
               allParents rest pars@(Thm.parents th)
        val parents = allParents lst []
        fun checkParent [] = ()
         |  checkParent (p::ps) =
              let
                 val _ = if (thmInStack hidden qORs p) then ()
                         else
                             print("parent : " ^ (Thm.toString p) ^ " NOT found in stack\n")
               in
                  checkParent ps
               end
     in
        checkParent parents
     end;
(* ------------------------------------------------------------------------ *)
(* Breadth first functions for both restoring hidden literals and also for  *)
(* replaying decisions to minimize the number of algebraic parents required *)
(* ------------------------------------------------------------------------ *)

(* second pass - unwinding the stack *)
fun leaves2root hidden thm_stack unknown known =
    case popThm thm_stack of
         NONE => known
     |   SOME (thm_stack,th,cx) =>
               let
                  val lits = Thm.clause th
                  val th = case LiteralSetMap.peek known lits of
                                SOME th' => th'
                             |  NONE => th
                  val parents = Thm.parents th
                  fun expand hidden [] done = done
                   |  expand hidden (p::ps) done = expand hidden ps ((Thm.restoreHiddenLits p hidden)::done)
                  val parents = expand hidden parents []
                  fun isKnown thx = LiteralSetMap.inDomain (Thm.clause thx) known
                  val known =
                      if (List.all isKnown parents) then
                             let
                                 fun replace thx = case LiteralSetMap.peek known (Thm.clause thx) of
                                                        SOME th' => th'
                                                      | NONE =>  raise Error 
                                                              ("known parent clause NOT found in known clause set!!!"
                                                                ^ Thm.extendedToString thx)
                                 val parents = map replace parents
                                 val th = Thm.setParents th parents
                                 val _ = chatting 2 andalso chat("new th added to known : "^(Thm.extendedToString th))
                              in
                                  LiteralSetMap.insert known (lits,th)
                              end
                       else
                              raise Error ("Unknown parents for clause : " ^ (Thm.extendedToString th) ^ "\n")
                in
                   leaves2root hidden thm_stack unknown known
                end

(* first pass from root (empty clause) back up to the leaves via breadth first search *)
(* but with only unique clauses retained in the queue and the stack.                  *)              
fun root2leaves hidden thm_queue thm_stack clause_count =
    case deQueueThm thm_queue of
         NONE => 
               let
                  val _ = chatting 2 andalso chat ("Clause count : " ^ (Int.toString clause_count) ^ "\n")
                  val ThmQueueOrStack(thmMap,litMap) = thm_stack
                  val size = IntMap.size (litMap)
                  val _ = chatting 2 andalso chat ("Size of stack : " ^ (Int.toString size) ^ "\n")
               in
                  leaves2root hidden thm_stack emptyQueue emptyThms
               end
     |   SOME (thm_queue,th,cx) =>
               let
                  val th = if (!replayProofDecisions) then replay_decision th else th
                  val th = Thm.restoreHiddenLits th hidden 
                  val thm_stack = addThm hidden thm_stack (th,cx)
                  val parents = Thm.parents th
		  val (thm_queue,clause_count) = addThmList hidden thm_queue parents clause_count
                  val thm_stack = addThm hidden thm_stack (th,cx)
               in
                  root2leaves hidden thm_queue thm_stack clause_count
               end;
                  
fun processEmptyClause hidden th =
    let
       val thm_stack = emptyStack
       val thm_queue = emptyQueue
       val clause_count = 0
       val th = Thm.restoreHiddenLits th hidden
       val thm_queue = addThm hidden thm_queue (th,clause_count)
    in
       root2leaves hidden thm_queue thm_stack (clause_count+1)
    end;

(* ------------------------------------------------------------------------------------------------------- *)  

  fun findUniqueClauses hidden th clauseSet acc =
   let
       val th = Thm.restoreHiddenLits th hidden
       val lits = Thm.clause th
   in
       if (LiteralSetMap.inDomain lits clauseSet) then
              (clauseSet,acc)
       else
               let
                  val pars = Thm.parents th
                  fun procParent (p,(cs,ac)) = findUniqueClauses hidden p cs ac
                  val (clauseSet,acc) = foldl procParent (clauseSet,acc) pars
                in
                  (* IMPORTANT don't add to map until all ancestors have been checked *)
                  (* and then only add if no ancestor has taken its place - we want   *)
                  (* the unique theorm to be that nearest the axioms not the empty    *)
                  (* clause to avoid unpleasent loops.                                *)
                   if (LiteralSetMap.inDomain lits clauseSet) then (clauseSet,acc)
                      else ((LiteralSetMap.insert clauseSet (lits,th)),(th::acc))
               end
    end;

  fun processClauses hidden unique known [] [] = known
   |  processClauses hidden unique known [] done =
          let
            val _ = chatting 2 andalso chat("\nPass completed, number of clauses still to process = " ^
                         (Int.toString (List.length done)) ^ "\n")
          in
                processClauses hidden unique known (rev done) []
          end
   |  processClauses hidden unique known (th::ths) done =
        let
           val lits = Thm.clause th
           (* must replace th by the version in the unique map else the parents *)
           (* may be wrong and lead to unpleasent loops !!!                     *)
           val th = case (LiteralSetMap.peek unique lits) of
                         SOME th' => th'
                     |   NONE => raise Error ("th not found in the unique set in processClauses in SplitStack.sml!\n")
           val pars = Thm.parents th
           fun process  [] newPars allKnown = (rev newPars,allKnown)
            |  process  (p::ps) newPars allKnown =
               let
                  val p = Thm.restoreHiddenLits p hidden
                  val pLits = Thm.clause p
                  val p = case (LiteralSetMap.peek unique pLits) of
                               SOME th' => th'
                           |   NONE => raise Error ("p not found in the unique set in processClauses in SplitStack.sml!\n")
                  val (pars,allKnown) =
                      case (LiteralSetMap.peek known pLits) of
                         SOME newP => process ps (newP::newPars) allKnown
                       | NONE => process ps (p::newPars) false
                in
                   (pars,allKnown)
                end

          val (pars,allKnown) = process pars [] true
          val th = Thm.setParents th pars
          val (known,done) = if (allKnown) then ((LiteralSetMap.insert known (lits,th)),done)
                                          else (known,(th::done))
        in
          processClauses hidden unique known ths done
        end;

in
    fun fullyExpandThm thm hidden =
       if (!breadthFirstProof) then
           let
               val known = processEmptyClause hidden thm
               val thm = Thm.restoreHiddenLits thm hidden
               val lits = Thm.clause thm
               val thO = LiteralSetMap.peek known lits
	   in
               case thO of
                    SOME th => th
	        |   NONE => raise Error "\nEmpty Clause not found in known after call to fullyExpandThm in SplitStack.sml\n"
	   end
       else
	   let
               val thm = Thm.restoreHiddenLits thm hidden (* NB the empty clause should remain the empty clause! *)
               val lits = Thm.clause thm (* there should be no lits in the empty clause, of course *)
               val _ = chatting 2 andalso chat("\nAbout to look for unique clauses\n")
               val (uniqueClauses,toBeProcessed) =  findUniqueClauses hidden thm emptyThms []
               val toBeProcessed = rev toBeProcessed (* important to process the clauses in the same order in which they were found *)
               val _ = chatting 2 andalso chat("\nUnique clauses found, about to process " ^ (Int.toString (List.length toBeProcessed)) ^ " clauses\n")
               val known = processClauses hidden uniqueClauses emptyThms toBeProcessed []
               val _ = chatting 2 andalso chat("\nAll clauses processed\n")
               val thO = LiteralSetMap.peek known lits
	   in
               case thO of
                    SOME th => th
                |   NONE => raise Error "\nEmpty Clause not found in known after call to fullyExpandThm in SplitStack.sml\n"
	   end;
end


(* function to transfer subsumed clauses from subs within active to deleted     *)
(* only transfer clauses that have been subsumed by a clause at a different     *)
(* level and at a level below top (0) as these are the only clauses that might  *)
(* be restored.                                                                 *)
(* JPB 25.2.11                                                                  *)
(* Modified 1st March 2011 to check that the consuming clause label is not a    *)
(* subset of the consumed clause label and that both clause labels are subsets  *)
(* of the label generated from the current stack. It should never be the case   *)
(* that they aren't as this would indicate that the clause deletion on          *)
(* backtracking had gone wrong.                                                 *)
(* Further modified 13.1.12 to only store the subsuming clause's label.         *)
fun transferDeletedClauses (ProofState {active,waiting,deleted,stack,restored,hidden}) =
   let
      val stackLabel = stackToLabel stack
      (* DEBUG *)
(*
      val _ = print "stack label : "
      val _ = printLabel stackLabel
*)
      (* END DEBUG *)
      fun transfer [] dc = ([],dc)
       |  transfer ((scl,cl)::rest) dc =
             let
                 val subLabel = Clause.clauseLabel scl
                 val sumedLabel = Clause.clauseLabel cl
                 val ok = (isSubLabel subLabel stackLabel) andalso
                          (isSubLabel sumedLabel stackLabel)
                 val skip = isSubLabel subLabel sumedLabel
             in
                 if ok then
                    if  skip then
                       transfer rest dc
                    else
                       transfer rest (((Clause.clauseLabel scl),cl)::dc)
                 else
                    raise Error "label problem in SplitStack.transferDeletedClauses "
             end
      val (active,dc) = Active.extractDeleted active
      val (_,deleted) = transfer dc deleted
    in
      ProofState {active = active,waiting = waiting, deleted = deleted, stack = stack,
                             restored = restored, hidden = hidden}
    end;

(* Simple function to update deleted clauses by adding a new pair *)
(* but need to perform checks as to the clause labels             *)
fun addToDeletedClauses (cl,dcl) deleted stack =
  let
     val stackLabel = stackToLabel stack
     val deletingClauseLabel = Clause.clauseLabel cl
     val deletedClauseLabel = Clause.clauseLabel dcl
     val ok = (isSubLabel deletingClauseLabel stackLabel) andalso
                  (isSubLabel deletedClauseLabel stackLabel)
     val skip = isSubLabel deletingClauseLabel deletedClauseLabel
     in
        if ok then
           if  skip then
                deleted
            else
                (((Clause.clauseLabel cl),dcl)::deleted)
        else
            raise Error "label problem in SplitStack.addToDeletedClauses "
     end


(* update the split stack for a new case split - the actual splitting *)
(* of the clauses is done prior to this function being called e.g. in *)
(* the module Active.sml.                                             *)
(* The left clause is returned with an updated label and the right    *)
(* clause is added to the stack as a blocked clause.                  *)
(* 1.3.11 : nextLeft added to make sure all left splits increase in   *)
(*          index number even after backtracking to avoid problems    *)
(*          with the lazy deletion in Waiting.                        *)
(* 9.5.11 : NB the negated left split could be adden to the hidden    *)
(*          lits structure in this routine but it would be a bit      *)
(*          wastefull as some splits are deleted on backtracking and  *)
(*          will not be part of the final proof.                      *)

fun caseSplit (parentCl : Clause.clause, leftCl : Clause.clause, rightCl : Clause.clause, stk as  (hd::_) : splitStack) =
        let
           val StackEntry{level = l,...} = hd
           val nl = nextLeft ()
           (* DEBUG *)
(*
           val _ = print ("\n==================================================================> new split at level : " ^ Int.toString nl ^ "\n")
*)
           (* END DEBUG *)
           val nr = nl + 1
           (* 9.5.11 the level added to the left split is negated to indicate a hidden literal is associated with it *)
           val left = Clause.addLevelToLabel (~nl) leftCl
           val right = Clause.addLevelToLabel nr rightCl
           (* the blockedLB should have the RIGHT new level added to its label otherwise it will get deleted on the Right Branch being entered *)
           (* and its negated value being restored to the clause set.                                                                          *)
           (* val blockedLeft = Clause.addLevelToLabel nr leftCl     4.5.11 - I now think it should have neither left nor right level added....*)
           val blockedLeft = leftCl
           val newEntry = StackEntry{level = nl, blockedRB = SOME right, blockedLB = SOME blockedLeft, parent = SOME parentCl, leafMarker = NONE}
           val newStk = (newEntry::stk)
        in
           (left, newStk)
        end
|caseSplit (parent : Clause.clause, leftCl : Clause.clause, rightCl : Clause.clause, stk as [] : splitStack)=
          raise Error "SplitStack.caseSplit empty stack!";
       (* the stack should never be empty - it always should have at least one entry for the top level *)

(******************************************************************************************)
(* 11.3.11 functions to delete clauses all moved here out of fun deleteTopLevel and made  *)
(* to work on multiple level deletions so as to allow just one clean up to be done before *)
(* returning rather than doing expensive operations several times.                        *)
(******************************************************************************************)
fun deleteActive active stackLabel =
   let
     fun clausePred cl = isSubLabel (Clause.clauseLabel cl) stackLabel

     fun thmPred th = isSubLabel (Thm.clauseLabel th) stackLabel

    val Active.Active
             {parameters,
              clauses,
              units,
              rewrite,
              subsume,
              literals,
              equations,
              subterms,
              allSubterms} = active

   (* the following is taken (with modifications) from original code *)
   (* in Active.sml.                                                 *)
    val clauses = IntMap.filter (clausePred o snd) clauses
    and subsume = Subsume.filter clausePred subsume
    and literals = LiteralNet.filter (clausePred o #1) literals
    and equations = TermNet.filter (clausePred o #1) equations
    and subterms = TermNet.filter (clausePred o #1) subterms
    and allSubterms = TermNet.filter (clausePred o fst) allSubterms

   (* the following is added to filter the units and the rewrites which *)
   (* are separate objects.                                             *)
    val units = Units.filter units (thmPred o snd)

   (* I'm still slightly doubtful about rewrites *)
   (* val rewrite = filterRewrite rewrite stackLabel *) (* don't need to do this as no non top level clauses added *)

    in
       (Active.Active
         {parameters = parameters,
          clauses = clauses,
          units = units,
          rewrite = rewrite,
          subsume = subsume,
          literals = literals,
          equations = equations,
          subterms = subterms,
          allSubterms = allSubterms})
    end;
   (* Function to delete (permanently) any clauses in the kept DeletedClauses set   *)
   (* that are dependent on deleted levels                                          *)
   (* NB the deleted clauses list is reversed in the process but this doesn't       *)
   (* matter as it will be reversed again by the function that restores the         *)
   (* deleted clauses.                                                              *)
   (* Anyway, the ordering doesn't matter as it is messed up by the transfer from   *)
   (* the subsumed clause structure.                                                *)
   fun deleteKeptDeletedClauses deleted stackLabel =
      let
         fun process [] done = done
           | process ((d as (_,cl))::ds) done =
             if isSubLabel (Clause.clauseLabel cl) stackLabel then
                process ds (d::done)
             else
                process ds done
     in
        process deleted []
     end


  (* Function to restore all kept deleted clauses. The deleted clause     *)
   (* list is reversed in the process but this doesn't matter as it simply *)
   (* restores the list that was reversed by deleteKeptDeletedClauses.     *)
   (* 13.1.12 simplified as DeletedClauses now stores only the label of the subsuming clause *)
   fun restoreKeptDeletedClauses deleted restored stackLabel =
      let
         fun process [] done waitQ = (done,waitQ)
           | process ((label,cl)::rest) done waitQ =
                if isSubLabel label stackLabel then
                   process rest ((label,cl)::done) waitQ
                else
                   process rest done (cl::waitQ)
         val (deleted,restored) = process deleted [] restored
      in
         (deleted,restored)
      end






fun deleteTopLevel (ProofState({active,waiting,deleted,stack,restored,hidden}),restoreParent : bool) =
(* ------------------------------------------------------------------------------- *)
(*                                                                                 *)
(* functions to delete the top stack entry and follow through all the consequences *)
(* if the boolean parameter restoreParent is true then the original parent clause  *)
(* is restored along with the other kept deletedClauses                            *)
(*                                                                                 *)
(* ------------------------------------------------------------------------------- *)
let

  (* Obtain the level of the top entry in the stack and the parent clause    *)
  (* NB for any stack entry being deleted there should be SOME parent clause *)
   val StackEntry{level=level, parent= parent, ...} = hd stack
   val parent = if isSome parent then Option.valOf parent else raise Error ((dumpStack stack) ^ "no parent found in deleteTopLevel")
   val stack = tl stack
   val restored = if restoreParent then (parent::restored) else restored
   (* Need also to delete clauses in waiting - though this is done in a lazy manner *)
   val waiting =  Waiting.deleteClauses level waiting
   val newState = ProofState{active=active,waiting=waiting,deleted=deleted,stack=stack,restored=restored,hidden=hidden}
in
    newState
end

(* Back jump function - keeps deleting levels above the level of *)
(* the current empty clause (which is passed as level)           *)
(* at the end of the process the highest level in the stack      *)
(* should be level.                                              *)
fun backJump level (state as ProofState({stack,...})) =
let
(*
    val _ = if !debug then ((printLevel level), (printStack "\n====================================\nstart of backJump\n===========================\n" stack)) else ((),())
*)
    val StackEntry{level=topLevel,...} = hd stack
    val remove = topLevel > level
    val newState = if remove then
                       deleteTopLevel (state,true) (* true indicates parent clause to be restored *)
                   else
                       state
    val ProofState({stack=newStack,...}) = newState
(*
    val _ = if !debug then (printStack "\n=============================\nend of backJump\n=================================\n" newStack) else ()
*)
    in
        if remove then
            backJump level newState
        else
            newState
    end


(* Branch condense fuction - keeps deleting levels from the top of *)
(* the stack while they are left levels and whilst they do not     *)
(* contribute to the (empty) clause label.  Left levels that are   *)
(* contributers are temporarily placed on another stack and then   *)
(* put back when the first right level is found.                   *)
fun branchCondense label (state as ProofState({active,waiting,deleted,stack,restored,hidden})) =
let
 (*   val _ = if !debug then ((printLabel label),(printStack "\n================================\nstart of branchCondense\n============================\n" stack)) else ((),())
  *)
   fun inLabel l [] = false
      | inLabel l (lh::ls) =
          if (Int.abs l) = (Int.abs lh) then
             true
          else
             inLabel l ls
     fun isLeft l = (((Int.abs l) mod 2) = 1)
     fun isRight l = (((Int.abs l) mod 2) = 0)
     fun top (ProofState({stack,...})) =
        let
           val StackEntry{level=topLevel,...} = hd stack
        in
           topLevel
        end
     (* function to go down a stack level without deleting - top of stack *)
     (* is transferred to another stack for future restoration            *)
     fun goDown (ProofState({stack = (top::rest),active,waiting,deleted,restored,hidden}),saved) =
                (ProofState({stack=rest,active=active,waiting=waiting,deleted=deleted,restored=restored,hidden=hidden}),(top::saved))
        |goDown (ProofState({stack = [],...}),_) = raise Error "empty stack in branchCondense"
     (* restore restores all the saved levels produced by successive calls to goDown *)
     fun restore (state,[]) = (state,[])
       | restore (ProofState({stack=s,active=a,waiting=w,deleted=d,restored=r,hidden=h}),(top::rest)) =
                 restore(ProofState({stack=(top::s),active=a,waiting=w,deleted=d,restored=r,hidden=h}),rest)
     (* delete removes a level and restores the parent clause *)
     fun delete (state,saved) =
          (deleteTopLevel (state,true), saved)

     fun process (state,saved) =
         let
             val l = top state
             val (newState,newSaved) =
                 if (isRight l) then
                    restore (state,saved)
                 else if (inLabel l label) then
                    process (goDown (state,saved))
                 else
                    process (delete (state,saved))
         in
              (newState, newSaved)
         end
    val (newState,_) = process(state,[])
(*
    val (ProofState({stack=newStack,...})) = newState
    val _ = if !debug then ((printLabel label), (printStack "\n=============================\nend of branchCondense\n===============================\n" newStack)) else ((),())
*)
in
     newState
end


(* Right collapse function - merges the empty clause with the     *)
(* leaf marker to produce a new empty clause, deletes the top     *)
(* of the stack and returns the new empty clause for reprocessing *)
(* by the main backtracking routine - NB the resultant empty      *)
(* clause has the top two levels removed from the combined label  *)
(* so eventually a top level empty clause should result.          *)
(* 9.5.11 addition to the code made to save the negated left split*)
(* to the hidden lits structure for future reinstatement in the   *)
(* final proof also don't merge with leafmarker as label should   *)
(* already contain the appropriate levels.                        *)
fun rightCollapse th (state as ProofState({active,waiting,deleted,stack,restored,hidden})) =
let
(*  val _ = if !debug then ((printTheorem th),(printStack "\n===========================\nstart of rightCollapse\n==========================\n" stack)) else ((),()) *)
    val StackEntry{level = level,leafMarker = leafMarker,blockedLB = blockedLB,...} = hd stack
    val lm = if isSome leafMarker then
                     Option.valOf leafMarker
              else
                    raise Error ((dumpStack stack) ^ "no LeafMarker in rightCollapse")
    val newTh = Thm.mergeCaseSplit th lm
    val newState = deleteTopLevel (state,true)   (* DO 3.3.11 restore the parent clause when deleting top level *)
in
    (newTh, newState)
end


(* Enter Right function - the input is a labelled empty clause *)
(* which is used as a leaf marker in the new stack entry.      *)
(* blocked clauses are restored and the parent clause from the *)
(* level below before is transferred then the level is deleted *)
(* The return values are the right split clause and new proof  *)
(* state.                                                      *)
fun enterRight th (state as ProofState({active,waiting,deleted,stack,restored,hidden})) =
let
   (*
   val _ = if !debug then (printTheorem th, (printStack "\n\n==========================\nstart of enterRight\n===========================\n" stack)) else ((),())
   val _ = if !debug then printMessageAndTheorem "current value of th :\n" th else ()
   *)
   val StackEntry{level,parent,blockedRB,blockedLB,leafMarker} = hd stack
   (* increment the level and check that the previous level was a left one *)
   val newLevel = if (level mod 2 = 1) then (level+1) else raise Error ("Enter Right in Split Stack" ^ dumpStack stack)
   (* negate the stored left clause (if it is ground) and add the resultant list of clauses to active *)
   val ncls = if isSome blockedLB then Clause.negateClauseIfGround (Option.valOf blockedLB) th
                               else NONE
   val _ = chatting 2 andalso
       chat("Left Branch Clause : " ^ clause_to_string (Option.valOf blockedLB) ^ "\nNegated clauses : \n" ^ clauses_to_string (Option.valOf ncls) ^ "\n")

   val negated = case ncls of NONE => [] | SOME cls => cls

   (* get the right split clause to return - if it exists else raise an error *)
    val rightCl = if isSome blockedRB then
                        Option.valOf blockedRB
                  else
                         raise Error ("Enter Right : no right split clause!" ^ dumpStack stack)
   (* 17.3.11 make sure the label of the right clause reflects the label of the leaf marker minus its top level *)
   val rightCl = Clause.rightCaseSplit rightCl th (Clause.thm (Option.valOf parent))

   (* 16.5.12 the hidden lit associated with the Right Case Split is EITHER the negation of the left case split *)
   (* where we have a unit clause for the left case split and, in proofs only, take the right case to be the    *)
   (* right half of a split following a A v ~A assume OR it is the right case split itself where the right case *)
   (* is a unit clause arising from doing a split following from a "probable" literal deletion as the result of *)
   (* quick RCF procedures - a full RCF being done on it only if it is needed in the proof.                     *)
   val hlits = if List.length negated = 1 then LiteralSet.toList (Clause.literals (hd negated)) else
               LiteralSet.toList (Clause.literals rightCl)
    val hlit = if (null hlits) orelse (List.length hlits > 1) then raise Error ((dumpStack stack) ^ "there is not one and only one hidden lit in enterRight\n")
               else hd hlits
    val hidden = IntMap.insert hidden (level,hlit)
    val newEntry = StackEntry{level = newLevel, parent = parent, blockedRB = NONE,
                                                                blockedLB = NONE, leafMarker =  SOME th}

   (* add the negated list of clauses to waiting *)
   val waiting = Waiting.add waiting ((~1.0),negated)

    (* Update the proof state with negative clauses etc otherwise these get lost !*)
    val state = ProofState{active=active,waiting=waiting,deleted=deleted,stack=stack,restored=restored,hidden=hidden}

    (* delete the top, left entry *)
    val state = deleteTopLevel (state, false)  (* false means don't restore parent clause *)

    (* perform the branch condense operation *)
    val ProofState({active,waiting,deleted,stack,restored,hidden}) = branchCondense (Thm.clauseLabel th) state

    (* add the new stack level *)
    val stack = (newEntry :: stack)

    (* delete any clauses made redundant by changes in the stack *)
    val stackLabel = stackToLabel stack
    val active = deleteActive active stackLabel
    val deleted = deleteKeptDeletedClauses deleted stackLabel

    (* get any extra clauses to be restored *)
    val (deleted,restored) = restoreKeptDeletedClauses deleted restored stackLabel


    val newState = ProofState({active=active,waiting=waiting,deleted=deleted,stack=stack,restored=restored,hidden=hidden})
    (*
    val _ = if !debug then (printTheorem th, (printStack "\n=====================\nend of enterRight\n========================\n" stack)) else ((),())
    *)
in
    (rightCl, newState)
end



(* clause cl is a conflicting clause i.e. the empty clause but it has a label *)
(* containing at least one undeleted split (otherwise it would not have been  *)
(* passed by the function Waiting.removeIfValid) - therefore backtracking is  *)
(* required.                                                                  *)
(* Backtracking should return (cl,state) where cl is either a top level empty *)
(* clause or a right split clause.                                            *)
fun backtrack (cl : Clause.clause) (state : proofState) =
let
    (* first transfer any subsumed clauses in the subsume structure over to the deleted clause list *)
    val state = transferDeletedClauses state

    (* Debug code *)
    (*
    val _ = if !debug then
               print "\n>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>> Back Track Entered <<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<\n"
             else
               ()
    val _ = if !debug then
	let
            val inference = Proof.thmToInference (Clause.thm cl)
            val parents = Proof.parents inference
            fun printParents [] = "\n"
             |  printParents (t::ts) = (Print.toString Thm.pp t) ^ "\n" ^ printParents ts
            val s = "\nInference : " ^ Proof.inferenceToString inference
            val s = s ^ "\nParent clauses : \n"
            val s = s ^ printParents parents
         in
             print s
         end
    else
         ()
    val (ProofState ({stack=stack,...})) = state
    val _ = if !debug then (printTheorem (Clause.thm cl), (printStack "!!!!!! stack state on entering backtracking !!!!!!\n" stack)) else ((),())
    *)
    (* end of debug code *)
    val label = Clause.clauseLabel cl
    val th = Clause.thm cl
    fun getLevel [] = 0
     |  getLevel (l::_) = (Int.abs l)
    val level = getLevel label
in
    if level = 0 then
        (cl,state)
    else
      let
        val state = backJump level state
        fun isRight level = ((level mod 2)=0)
      in
        if isRight level then
           let
              val (th,state) = rightCollapse th state
              val {parameters,thm,...} = Clause.dest cl
              val cl = Clause.mk {parameters = parameters,
	               id = Clause.newId(),thm = th}
            in
              backtrack cl state
            end
         else
            enterRight th state
      end
end

(* function to backtrack and undo splits without an empty clause having been reached *)
(* the purpose is to release clauses when the waiting clause set is empty and the    *)
(* prover would otherwise giveup.                                                    *)

fun unforcedBacktrack  (state : proofState) =
let
    (* first transfer any subsumed clauses in the subsume structure over to the deleted clause list *)
    val state = transferDeletedClauses state
    val ProofState{stack=stack,...} = state
    val stackLabel = stackToLabel stack
    val level = hd stackLabel
    (* delete at least one level releasing the parent *)
    val state = if(level > 0) then deleteTopLevel (state,true) else state
    (* if the top level was a right branch then delete the             *)
    (* associated left branch as well (but do not release the parent)  *)
    val state =  if((level mod 2) = 0) andalso level > 0 then deleteTopLevel (state,false) else state

    val ProofState{active,waiting,deleted,stack,restored,hidden} = state

    (* delete any clauses made redundant by changes in the stack *)
    val stackLabel = stackToLabel stack
    val active = deleteActive active stackLabel
    val deleted = deleteKeptDeletedClauses deleted stackLabel

    (* get any extra clauses to be restored *)
    val (deleted,restored) = restoreKeptDeletedClauses deleted restored stackLabel
in
    ProofState{active=active,waiting=waiting,deleted=deleted,stack=stack,restored=restored,hidden=hidden}
end

(* A debug functions to dump clauses to output in cnf format *)
(* so they can be piped to a file and treated as axioms.     *)
local
  fun toFormula th =
      Formula.listMkDisj
        (map Literal.toFormula (LiteralSet.toList (Thm.clause th)));

  fun stripLeadingZeroes [] = []
   |  stripLeadingZeroes (c::cs) =
      if c = #"0" then stripLeadingZeroes cs else (c::cs)

  fun replaceNames clause =
      let
          fun process [] l = rev l
           |  process (c::cs) l =
           if c = #"$" then
              if (hd cs) = #"_" then
                 process (stripLeadingZeroes (tl cs)) ((#"V")::l)
              else
                 process cs l
           else
              process cs (c::l)
          val clause = process clause []
      in
          clause
      end

  fun moveToMatchingRightBracket [] seen =
      let
         val _ = print("seen : " ^ (implode seen) ^ "\n")
      in
         raise Bug "missing right bracket in SplitStack.clauseDump"
      end
   |  moveToMatchingRightBracket (c::cs) seen =
      if (c = #")") then ((c::cs),seen)
      else if (c = #"(") then
        let
            val (u,s) = moveToMatchingRightBracket cs (c::seen)
            val (x,xs) = if not (null u) then (hd u,tl u) else raise Bug "error in SplitStack.clauseDump"
        in
            moveToMatchingRightBracket xs (x::s)
        end
      else
            moveToMatchingRightBracket cs (c::seen)

  fun removeNotBrackets [] seen = rev seen
   |  removeNotBrackets (c::cs) seen =
      if (c = #"~" andalso (hd cs) = #"(" ) then
         let
             val (u,seen) = moveToMatchingRightBracket (tl cs) (c::seen)
             val (c,cs) = if not (null u) then (hd u,tl u) else raise Bug "error in SplitStack.clauseDump"
          in
             removeNotBrackets cs seen
          end
      else
          removeNotBrackets cs (c::seen)
in

fun clauseToCNFstring cl =
    let
      val th = Clause.thm cl
      val clause = Formula.toString (toFormula th)
      val clause = explode clause
      val clause = replaceNames clause
      (* val clause = removeNotBrackets clause [] *)
      val clause = implode clause
      val name = Int.toString (Clause.id cl)
    in
      if (String.isSubstring "sko" clause) then
          "cnf(id_" ^ name ^ ",negated_conjecture,(" ^ clause ^ ")).\n"
       else
           "cnf(id_" ^ name ^ ",axiom,(" ^ clause ^ ")).\n"
    end

end

fun dumpClauseListToFile activeCls waitingCls name =
    let
       val fout =  TextIO.openOut name
       val _ = TextIO.output (fout,("% File name : " ^ name ^ "\n"))
       fun write [] fout = ()
        |  write (cl::rest) fout =
           let
               val _ = TextIO.output (fout,(clauseToCNFstring cl))
           in
               write rest fout
           end
       val _ = TextIO.output (fout,"% Active set clauses\n")
       val _ = write activeCls fout
       val _ = TextIO.output (fout,"% Waiting set clauses\n")
       val _ = write waitingCls fout
    in
       TextIO.closeOut fout
    end;

fun dumpClauses active waiting fileName =
   let
      val activeCls = Active.getAllClauses active
      fun getWaitingClauses waiting cls =
          case Waiting.removeIfValid waiting of
             NONE => cls
           | SOME ((_,(_,cl)),waiting) => getWaitingClauses waiting (cl::cls);
      val waitingCls = getWaitingClauses waiting []
   in
      dumpClauseListToFile activeCls waitingCls fileName
   end

(* function to return all parents from a stack *)
fun returnParents stack =
  let
     fun level (StackEntry {level=l,...}) = l
     fun parent (StackEntry {parent=SOME p,...}) = p
      |  parent _ = raise Error "parent missing in SplitStack.returnParents"
     fun process [] parents = parents
      |  process (e::rest) parents =
         if ((level e) mod 2) = 1 then
             process rest ((parent e)::parents)
         else
             process rest parents
  in
     process stack []
  end;


end (* of module *)
