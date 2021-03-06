(* ========================================================================= *)
(* PROOFS IN FIRST ORDER LOGIC                                               *)
(* Copyright (c) 2001 Joe Hurd, distributed under the MIT license            *)

(* ========================================================================= *)
(* Modified 9.5.11 to reinstate hidden lits that arise from case splitting.  *)
(* ------------------------------------------------------------------------- *)

structure Proof :> Proof =
struct

open Useful;

(* ------------------------------------------------------------------------- *)
(* A type of first order logic proofs.                                       *)
(* ------------------------------------------------------------------------- *)

datatype inference =
    Axiom of LiteralSet.set
  | Arith of LiteralSet.set * Thm.thm
  | Decision of LiteralSet.set * Thm.thm list
  | Split of LiteralSet.set * Thm.thm list
  | Cases of LiteralSet.set * Thm.thm list
  | CaseSplit of LiteralSet.set * Thm.thm list
  | Assume of Atom.atom
  | Subst of Subst.subst * Thm.thm
  | Resolve of Atom.atom * Thm.thm * Thm.thm
  | Refl of Term.term
  | Equality of Literal.literal * Term.path * Term.term;

type proof = (Thm.thm * inference) list;

(* ------------------------------------------------------------------------- *)
(* Printing.                                                                 *)
(* ------------------------------------------------------------------------- *)

fun inferenceType (Axiom _) = Thm.Axiom
  | inferenceType (Arith _) = Thm.Arith
  | inferenceType (Decision _) = Thm.Decision
  | inferenceType (Split _) = Thm.Split
  | inferenceType (Cases _) = Thm.Cases
  | inferenceType (CaseSplit _) = Thm.CaseSplit
  | inferenceType (Assume _) = Thm.Assume
  | inferenceType (Subst _) = Thm.Subst
  | inferenceType (Resolve _) = Thm.Resolve
  | inferenceType (Refl _) = Thm.Refl
  | inferenceType (Equality _) = Thm.Equality;

local
  fun ppAssume atm = Print.sequence (Print.addBreak 1) (Atom.pp atm);

  fun ppArith ppThm (_,thm) =
      Print.sequence (Print.addBreak 1)
        (Print.blockProgram Print.Inconsistent 1
           [Print.addString "{",
            Print.ppOp2 " =" Print.ppString ppThm ("arith",thm),
            Print.addString "}"]);

  fun ppRCF ppThm (_,thms) =
      Print.sequence (Print.addBreak 1)
        (Print.blockProgram Print.Inconsistent 1
           [Print.addString "{",
            Print.ppOp2 " =" Print.ppString (Print.ppList ppThm) ("decision",thms),
            Print.addString "}"]);

  fun ppMagic ppThm (_,thms) =
      Print.sequence (Print.addBreak 1)
        (Print.blockProgram Print.Inconsistent 1
           [Print.addString "{",
            Print.ppOp2 " =" Print.ppString (Print.ppList ppThm) ("split",thms),
            Print.addString "}"]);

  fun ppCaseSplit ppThm (_,thms) =
      Print.sequence (Print.addBreak 1)
        (Print.blockProgram Print.Inconsistent 1
           [Print.addString "{",
            Print.ppOp2 " =" Print.ppString (Print.ppList ppThm) ("case split",thms),
            Print.addString "}"]);


  fun ppSubst ppThm (sub,thm) =
      Print.sequence (Print.addBreak 1)
        (Print.blockProgram Print.Inconsistent 1
           [Print.addString "{",
            Print.ppOp2 " =" Print.ppString Subst.pp ("sub",sub),
            Print.addString ",",
            Print.addBreak 1,
            Print.ppOp2 " =" Print.ppString ppThm ("thm",thm),
            Print.addString "}"]);

  fun ppResolve ppThm (res,pos,neg) =
      Print.sequence (Print.addBreak 1)
        (Print.blockProgram Print.Inconsistent 1
           [Print.addString "{",
            Print.ppOp2 " =" Print.ppString Atom.pp ("res",res),
            Print.addString ",",
            Print.addBreak 1,
            Print.ppOp2 " =" Print.ppString ppThm ("pos",pos),
            Print.addString ",",
            Print.addBreak 1,
            Print.ppOp2 " =" Print.ppString ppThm ("neg",neg),
            Print.addString "}"]);

  fun ppRefl tm = Print.sequence (Print.addBreak 1) (Term.pp tm);

  fun ppEquality (lit,path,res) =
      Print.sequence (Print.addBreak 1)
        (Print.blockProgram Print.Inconsistent 1
           [Print.addString "{",
            Print.ppOp2 " =" Print.ppString Literal.pp ("lit",lit),
            Print.addString ",",
            Print.addBreak 1,
            Print.ppOp2 " =" Print.ppString Term.ppPath ("path",path),
            Print.addString ",",
            Print.addBreak 1,
            Print.ppOp2 " =" Print.ppString Term.pp ("res",res),
            Print.addString "}"]);

  fun ppInf ppAxiom ppThm inf =
      let
        val infString = Thm.inferenceTypeToString (inferenceType inf)
      in
        Print.block Print.Inconsistent 2
          (Print.sequence
             (Print.addString infString)
             (case inf of
                Axiom cl => ppAxiom cl
	      | Arith x => ppArith ppThm x
	      | Decision x => ppRCF ppThm x
	      | Split x => ppMagic ppThm x
	      | Cases x => ppMagic ppThm x
              | CaseSplit x => ppCaseSplit ppThm x
              | Assume x => ppAssume x
              | Subst x => ppSubst ppThm x
              | Resolve x => ppResolve ppThm x
              | Refl x => ppRefl x
              | Equality x => ppEquality x))
      end;

  fun ppAxiom cl =
      Print.sequence
        (Print.addBreak 1)
        (Print.ppMap
           LiteralSet.toList
           (Print.ppBracket "{" "}" (Print.ppOpList "," Literal.pp)) cl);
in
  val ppInference = ppInf ppAxiom Thm.pp;

  fun pp prf =
      let
        fun thmString n = "(" ^ Int.toString n ^ ")"

        val prf = enumerate prf

        fun ppThm th =
            Print.addString
            let
              val cl = Thm.clause th

              fun pred (_,(th',_)) = LiteralSet.equal (Thm.clause th') cl
            in
              case List.find pred prf of
                NONE => "(?)"
              | SOME (n,_) => thmString n
            end

        fun ppStep (n,(th,inf)) =
            let
              val s = thmString n
            in
              Print.sequence
                (Print.blockProgram Print.Consistent (1 + size s)
                   [Print.addString (s ^ " "),
                    Thm.pp th,
                    Print.addBreak 2,
                    Print.ppBracket "[" "]" (ppInf (K Print.skip) ppThm) inf])
                Print.addNewline
            end
      in
        Print.blockProgram Print.Consistent 0
          [Print.addString "START OF PROOF",
           Print.addNewline,
           Print.program (map ppStep prf),
           Print.addString "END OF PROOF"]
      end
(*MetisDebug
      handle Error err => raise Bug ("Proof.pp: shouldn't fail:\n" ^ err);
*)

end;

val inferenceToString = Print.toString ppInference;

val toString = Print.toString pp;

(* ------------------------------------------------------------------------- *)
(* Reconstructing single inferences.                                         *)
(* ------------------------------------------------------------------------- *)

fun parents (Axiom _) = []
  | parents (Arith (_,th)) = [th]
  | parents (Decision (_,ths)) = ths
  | parents (Split (_,ths)) = ths
  | parents (Cases (_,ths)) = ths
  | parents (CaseSplit (_,ths)) = ths
  | parents (Assume _) = []
  | parents (Subst (_,th)) = [th]
  | parents (Resolve (_,th,th')) = [th,th']
  | parents (Refl _) = []
  | parents (Equality _) = [];

fun inferenceToThm (Axiom cl) = Thm.axiom cl
  | inferenceToThm (Arith (cl,th)) = Thm.arith th
  | inferenceToThm (Decision (cl,ths)) = Thm.decision cl ths
  | inferenceToThm (Split (cl,ths)) = Thm.split cl ths
  | inferenceToThm (Cases (cl,ths)) = Thm.cases cl ths
  | inferenceToThm (CaseSplit (cl,ths)) = Thm.caseSplit cl ths
  | inferenceToThm (Assume atm) = Thm.assume (true,atm)
  | inferenceToThm (Subst (sub,th)) = Thm.subst sub th
  | inferenceToThm (Resolve (atm,th,th')) = Thm.resolve (true,atm) th th'
  | inferenceToThm (Refl tm) = Thm.refl tm
  | inferenceToThm (Equality (lit,path,r)) = Thm.equality lit path r;

local
  fun reconstructSubst cl cl' =
      let
        fun recon [] =
            let
(*MetisTrace3
              val () = Print.trace LiteralSet.pp "reconstructSubst: cl" cl
              val () = Print.trace LiteralSet.pp "reconstructSubst: cl'" cl'
*)
            in
              raise Bug "can't reconstruct Subst rule"
            end
          | recon (([],sub) :: others) =
            if LiteralSet.equal (LiteralSet.subst sub cl) cl' then sub
            else recon others
          | recon ((lit :: lits, sub) :: others) =
            let
              fun checkLit (lit',acc) =
                  case total (Literal.match sub lit) lit' of
                    NONE => acc
                  | SOME sub => (lits,sub) :: acc
            in
              recon (LiteralSet.foldl checkLit others cl')
            end
      in
        Subst.normalize (recon [(LiteralSet.toList cl, Subst.empty)])
      end
(*MetisDebug
      handle Error err =>
        raise Bug ("Proof.recontructSubst: shouldn't fail:\n" ^ err);
*)

  fun reconstructResolvant cl1 cl2 cl =
      (if not (LiteralSet.subset cl1 cl) then
         LiteralSet.pick (LiteralSet.difference cl1 cl)
       else if not (LiteralSet.subset cl2 cl) then
         Literal.negate (LiteralSet.pick (LiteralSet.difference cl2 cl))
       else
         (* A useless resolution, but we must reconstruct it anyway *)
         let
           val cl1' = LiteralSet.negate cl1
           and cl2' = LiteralSet.negate cl2
           val lits = LiteralSet.intersectList [cl1,cl1',cl2,cl2']
         in
           if not (LiteralSet.null lits) then LiteralSet.pick lits
           else raise Bug "can't reconstruct Resolve rule"
         end)
(*MetisDebug
      handle Error err =>
        raise Bug ("Proof.recontructResolvant: shouldn't fail:\n" ^ err);
*)

  fun reconstructEquality cl =
      let
(*MetisTrace3
        val () = Print.trace LiteralSet.pp "Proof.reconstructEquality: cl" cl
*)

        fun sync s t path (f,a) (f',a') =
            if f <> f' orelse length a <> length a' then NONE
            else
              let
                val itms = enumerate (zip a a')
              in
                case List.filter (not o uncurry Term.equal o snd) itms of
                  [(i,(tm,tm'))] =>
                  let
                    val path = i :: path
                  in
                    if Term.equal tm s andalso Term.equal tm' t then
                      SOME (rev path)
                    else
                      case (tm,tm') of
                        (Term.Fn f_a, Term.Fn f_a') => sync s t path f_a f_a'
                      | _ => NONE
                  end
                | _ => NONE
              end

        fun recon (neq,(pol,atm),(pol',atm')) =
            if pol = pol' then NONE
            else
              let
                val (s,t) = Literal.destNeq neq

                val path =
                    if not (Term.equal s t) then sync s t [] atm atm'
                    else if not (Atom.equal atm atm') then NONE
                    else Atom.find (Term.equal s) atm
              in
                case path of
                  SOME path => SOME ((pol',atm),path,t)
                | NONE => NONE
              end

        val candidates =
            case List.partition Literal.isNeq (LiteralSet.toList cl) of
              ([l1],[l2,l3]) => [(l1,l2,l3),(l1,l3,l2)]
            | ([l1,l2],[l3]) => [(l1,l2,l3),(l1,l3,l2),(l2,l1,l3),(l2,l3,l1)]
            | ([l1],[l2]) => [(l1,l1,l2),(l1,l2,l1)]
            | _ => raise Bug "reconstructEquality: malformed"

(*MetisTrace3
        val ppCands =
            Print.ppList (Print.ppTriple Literal.pp Literal.pp Literal.pp)
        val () = Print.trace ppCands
                   "Proof.reconstructEquality: candidates" candidates
*)
      in
        case first recon candidates of
          SOME info => info
        | NONE => raise Bug "can't reconstruct Equality rule"
      end
(*MetisDebug
      handle Error err =>
        raise Bug ("Proof.recontructEquality: shouldn't fail:\n" ^ err);
*)

  fun reconstruct cl (Thm.Axiom,[]) = Axiom cl
    | reconstruct cl (Thm.Arith,[th]) = Arith (cl,th)
    | reconstruct cl (Thm.Decision,ths) = Decision (cl,ths)
    | reconstruct cl (Thm.Split,ths) = Split (cl,ths)
    | reconstruct cl (Thm.Cases,ths) = Cases (cl,ths)
    | reconstruct cl (Thm.CaseSplit,ths) = CaseSplit (cl,ths)
    | reconstruct cl (Thm.Assume,[]) =
      (case LiteralSet.findl Literal.positive cl of
         SOME (_,atm) => Assume atm
       | NONE => raise Bug "malformed Assume inference")
    | reconstruct cl (Thm.Subst,[th]) =
      Subst (reconstructSubst (Thm.clause th) cl, th)
    | reconstruct cl (Thm.Resolve,[th1,th2]) =
      let
        val cl1 = Thm.clause th1
        and cl2 = Thm.clause th2
        val (pol,atm) = reconstructResolvant cl1 cl2 cl
      in
        if pol then Resolve (atm,th1,th2) else Resolve (atm,th2,th1)
      end
    | reconstruct cl (Thm.Refl,[]) =
      (case LiteralSet.findl (K true) cl of
         SOME lit => Refl (Literal.destRefl lit)
       | NONE => raise Bug "malformed Refl inference")
    | reconstruct cl (Thm.Equality,[]) = Equality (reconstructEquality cl)
    | reconstruct _ _ = raise Bug "malformed inference";
in
  fun thmToInference th =
      let
(*MetisTrace3
        val () = Print.trace Thm.pp "Proof.thmToInference: th" th
*)

        val cl = Thm.clause th

        val thmInf = Thm.inference th

(*MetisTrace3
        val ppThmInf = Print.ppPair Thm.ppInferenceType (Print.ppList Thm.pp)
        val () = Print.trace ppThmInf "Proof.thmToInference: thmInf" thmInf
*)

        val inf = reconstruct cl thmInf

(*MetisTrace3
        val () = Print.trace ppInference "Proof.thmToInference: inf" inf
*)
(*MetisDebug
        val () =
            let
              val th' = inferenceToThm inf
            in
              if LiteralSet.equal (Thm.clause th') cl then ()
              else
                raise
                  Bug
                    ("Proof.thmToInference: bad inference reconstruction:" ^
                     "\n  th = " ^ Thm.toString th ^
                     "\n  inf = " ^ inferenceToString inf ^
                     "\n  inf th = " ^ Thm.toString th')
            end
*)
      in
        inf
      end
(*MetisDebug
      handle Error err =>
        raise Bug ("Proof.thmToInference: shouldn't fail:\n" ^ err);
*)
end;

(* ------------------------------------------------------------------------- *)
(* Reconstructing whole proofs.                                              *)
(* ------------------------------------------------------------------------- *)

local
  val emptyThms : Thm.thm LiteralSetMap.map = LiteralSetMap.new ();

  fun addThms (th,ths) =
      let
        val cl = Thm.clause th
      in
        if LiteralSetMap.inDomain cl ths then ths
        else
          let
            val (_,pars) = Thm.inference th
            val ths = List.foldl addThms ths pars
          in
            if LiteralSetMap.inDomain cl ths then ths
            else LiteralSetMap.insert ths (cl,th)
          end
      end;

  fun mkThms th = addThms (th,emptyThms);

  fun addProof (th,(ths,acc)) =
      let
        val cl = Thm.clause th
      in
        case LiteralSetMap.peek ths cl of
          NONE => (ths,acc)
        | SOME th =>
          let
            val (_,pars) = Thm.inference th
            val (ths,acc) = List.foldl addProof (ths,acc) pars
            val ths = LiteralSetMap.delete ths cl
            val acc = (th, thmToInference th) :: acc
          in
            (ths,acc)
          end
      end;

  fun mkProof ths th =
      let
        val (_,acc) = addProof (th,(ths,[]))
(*MetisTrace4
        val () = Print.trace Print.ppInt "Proof.proof: unnecessary clauses" (LiteralSetMap.size ths)
*)
      in
        rev acc
      end;
in
  fun proof th =
      let
(*MetisTrace3
        val () = Print.trace Thm.pp "Proof.proof: th" th
*)
        val ths = mkThms th
        val infs = mkProof ths th
(*MetisTrace3
        val () = Print.trace Print.ppInt "Proof.proof: size" (length infs)
*)
      in
        infs
      end;
end;

(* ------------------------------------------------------------------------- *)
(* Free variables.                                                           *)
(* ------------------------------------------------------------------------- *)

fun freeIn v =
    let
      fun free th_inf =
          case th_inf of
            (_, Axiom lits) => LiteralSet.freeIn v lits
          | (_, Arith (lits,_)) => LiteralSet.freeIn v lits
          | (_, Decision (lits,_)) => LiteralSet.freeIn v lits
          | (_, Split (lits,_)) => LiteralSet.freeIn v lits
          | (_, Cases (lits,_)) => LiteralSet.freeIn v lits
          | (_, CaseSplit (lits,_)) => LiteralSet.freeIn v lits
          | (_, Assume atm) => Atom.freeIn v atm
          | (th, Subst _) => Thm.freeIn v th
          | (_, Resolve _) => false
          | (_, Refl tm) => Term.freeIn v tm
          | (_, Equality (lit,_,tm)) =>
            Literal.freeIn v lit orelse Term.freeIn v tm
    in
      List.exists free
    end;

val freeVars =
    let
      fun inc (th_inf,set) =
          NameSet.union set
          (case th_inf of
             (_, Axiom lits) => LiteralSet.freeVars lits
           | (_, Arith (lits,_)) => LiteralSet.freeVars lits
           | (_, Decision (lits,_)) => LiteralSet.freeVars lits
           | (_, Split (lits,_)) => LiteralSet.freeVars lits
           | (_, Cases (lits,_)) => LiteralSet.freeVars lits
           | (_, CaseSplit (lits,_)) => LiteralSet.freeVars lits
           | (_, Assume atm) => Atom.freeVars atm
           | (th, Subst _) => Thm.freeVars th
           | (_, Resolve _) => NameSet.empty
           | (_, Refl tm) => Term.freeVars tm
           | (_, Equality (lit,_,tm)) =>
             NameSet.union (Literal.freeVars lit) (Term.freeVars tm))
    in
      List.foldl inc NameSet.empty
    end;

end
