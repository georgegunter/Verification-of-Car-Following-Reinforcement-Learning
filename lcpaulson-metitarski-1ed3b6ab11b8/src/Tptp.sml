(* ========================================================================= *)
(* THE TPTP PROBLEM FILE FORMAT                                              *)
(* Copyright (c) 2001 Joe Hurd, distributed under the MIT license            *)

(* ========================================================================= *)

structure Tptp :> Tptp =
struct

val standardTSTP = ref false;   (*True = Standard TSTP, False = infix notation, etc.*)
val fullProofs = ref false;     (*True = include variable instantiations in proofs*)

open Useful;

(*LCP:  modified parsing*)
(* ------------------------------------------------------------------------- *)
(* Default TPTP function and relation name mapping.                          *)
(* ------------------------------------------------------------------------- *)

val defaultFunctionMapping =
    [(* Mapping TPTP functions to infix symbols *)
     {name = "~", arity = 1, tptp = "negate"},
     {name = "*", arity = 2, tptp = "multiply"},
     {name = "/", arity = 2, tptp = "divide"},
     {name = "+", arity = 2, tptp = "add"},
     {name = "-", arity = 2, tptp = "subtract"},
     {name = "-", arity = 1, tptp = "neg"},		(*LCP: needed for Metis-RCF*)
     {name = "^", arity = 2, tptp = "power"},		(*LCP: needed for Metis-RCF*)
     {name = "::", arity = 2, tptp = "cons"},
     {name = ",", arity = 2, tptp = "pair"},
     (* Expanding HOL symbols to TPTP alphanumerics *)
     {name = ":", arity = 2, tptp = "has_type"},
     {name = ".", arity = 2, tptp = "apply"},
     {name = "<=", arity = 0, tptp = "less_equal"}];

val defaultRelationMapping =
    [(* Mapping TPTP relations to infix symbols *)
     {name = "=", arity = 2, tptp = "="},  (* this preserves the = symbol *)
     {name = "==", arity = 2, tptp = "equalish"},
     {name = "<=", arity = 2, tptp = "less_equal"},
     {name = "<", arity = 2, tptp = "less_than"},
     {name = ">=", arity = 2, tptp = "greater_equal"},
     {name = ">", arity = 2, tptp = "greater_than"},
     (* Expanding HOL symbols to TPTP alphanumerics *)
     {name = "{}", arity = 1, tptp = "bool"}];

(* ------------------------------------------------------------------------- *)
(* Interpreting TPTP functions and relations in a finite model.              *)
(* ------------------------------------------------------------------------- *)

val defaultFunctionModel =
    [{name = "~", arity = 1, model = Model.negName},
     {name = "*", arity = 2, model = Model.multName},
     {name = "/", arity = 2, model = Model.divName},
     {name = "+", arity = 2, model = Model.addName},
     {name = "-", arity = 2, model = Model.subName},
     {name = "::", arity = 2, model = Model.consName},
     {name = "@", arity = 2, model = Model.appendName},
     {name = ":", arity = 2, model = Term.hasTypeFunctionName},
     {name = "additive_identity", arity = 0, model = Model.numeralName 0},
     {name = "app", arity = 2, model = Model.appendName},
     {name = "complement", arity = 1, model = Model.complementName},
     {name = "difference", arity = 2, model = Model.differenceName},
     {name = "divide", arity = 2, model = Model.divName},
     {name = "empty_set", arity = 0, model = Model.emptyName},
     {name = "identity", arity = 0, model = Model.numeralName 1},
     {name = "identity_map", arity = 1, model = Model.projectionName 1},
     {name = "intersection", arity = 2, model = Model.intersectName},
     {name = "minus", arity = 1, model = Model.negName},
     {name = "multiplicative_identity", arity = 0, model = Model.numeralName 1},
     {name = "n0", arity = 0, model = Model.numeralName 0},
     {name = "n1", arity = 0, model = Model.numeralName 1},
     {name = "n2", arity = 0, model = Model.numeralName 2},
     {name = "n3", arity = 0, model = Model.numeralName 3},
     {name = "n4", arity = 0, model = Model.numeralName 4},
     {name = "n5", arity = 0, model = Model.numeralName 5},
     {name = "n6", arity = 0, model = Model.numeralName 6},
     {name = "n7", arity = 0, model = Model.numeralName 7},
     {name = "n8", arity = 0, model = Model.numeralName 8},
     {name = "n9", arity = 0, model = Model.numeralName 9},
     {name = "nil", arity = 0, model = Model.nilName},
     {name = "null_class", arity = 0, model = Model.emptyName},
     {name = "singleton", arity = 1, model = Model.singletonName},
     {name = "successor", arity = 1, model = Model.sucName},
     {name = "symmetric_difference", arity = 2,
      model = Model.symmetricDifferenceName},
     {name = "union", arity = 2, model = Model.unionName},
     {name = "universal_class", arity = 0, model = Model.universeName}];

val defaultRelationModel =
    [{name = "=", arity = 2, model = Atom.eqRelationName},
     {name = "==", arity = 2, model = Atom.eqRelationName},
     {name = "<=", arity = 2, model = Model.leName},
     {name = "<", arity = 2, model = Model.ltName},
     {name = ">=", arity = 2, model = Model.geName},
     {name = ">", arity = 2, model = Model.gtName},
     {name = "divides", arity = 2, model = Model.dividesName},
     {name = "element_of_set", arity = 2, model = Model.memberName},
     {name = "equal", arity = 2, model = Atom.eqRelationName},
     {name = "equal_elements", arity = 2, model = Atom.eqRelationName},
     {name = "equal_sets", arity = 2, model = Atom.eqRelationName},
     {name = "equivalent", arity = 2, model = Atom.eqRelationName},
     {name = "less", arity = 2, model = Model.ltName},
     {name = "less_or_equal", arity = 2, model = Model.leName},
     {name = "member", arity = 2, model = Model.memberName},
     {name = "subclass", arity = 2, model = Model.subsetName},
     {name = "subset", arity = 2, model = Model.subsetName}];

(* ------------------------------------------------------------------------- *)
(* Helper functions.                                                         *)
(* ------------------------------------------------------------------------- *)

fun isHdTlString hp tp s =
    let
      fun ct 0 = true
        | ct i = tp (String.sub (s,i)) andalso ct (i - 1)

      val n = size s
    in
      n > 0 andalso hp (String.sub (s,0)) andalso ct (n - 1)
    end;

fun variant avoid s =
    if not (StringSet.member s avoid) then s
    else
      let
        val s = stripSuffix Char.isDigit s

        fun var i =
            let
              val s_i = s ^ Int.toString i
            in
              if not (StringSet.member s_i avoid) then s_i else var (i + 1)
            end
      in
        var 0
      end;

(* ------------------------------------------------------------------------- *)
(* Mapping to legal TPTP names.                                              *)
(* ------------------------------------------------------------------------- *)

local
  fun nonEmptyPred p l =
      case l of
        [] => false
      | c :: cs => p (c,cs);

  fun existsPred l x = List.exists (fn p => p x) l;

  fun isTptpChar #"_" = true
    | isTptpChar c = Char.isAlphaNum c;

  fun isTptpName l s = nonEmptyPred (existsPred l) (explode s);

  fun isRegular (c,cs) =
      Char.isLower c andalso List.all isTptpChar cs;

  fun isNumber (c,cs) =
      Char.isDigit c andalso List.all Char.isDigit cs;

  fun isDefined (c,cs) =
      c = #"$" andalso nonEmptyPred isRegular cs;

  fun isSystem (c,cs) =
      c = #"$" andalso nonEmptyPred isDefined cs;
in
  fun mkTptpVarName s =
      let
        val s =
            case List.filter isTptpChar (explode s) of
              [] => [#"X"]
            | l as c :: cs =>
              if Char.isUpper c then l
              else if Char.isLower c then Char.toUpper c :: cs
              else #"X" :: l
      in
        implode s
      end;

  val isTptpConstName = isTptpName [isRegular,isNumber,isDefined,isSystem]
  and isTptpFnName = isTptpName [isRegular,isDefined,isSystem]
  and isTptpPropName = isTptpName [isRegular,isDefined,isSystem]
  and isTptpRelName = isTptpName [isRegular,isDefined,isSystem];

  val isTptpFormulaName = isTptpName [isRegular,isNumber];
      end;

(* ------------------------------------------------------------------------- *)
(* Mapping to legal TPTP variable names.                                     *)
(* ------------------------------------------------------------------------- *)

datatype varToTptp = VarToTptp of StringSet.set * string NameMap.map;

val emptyVarToTptp = VarToTptp (StringSet.empty, NameMap.new ());

fun addVarToTptp vm v =
    let
      val VarToTptp (avoid,mapping) = vm
    in
      if NameMap.inDomain v mapping then vm
      else
        let
          val s = variant avoid (mkTptpVarName (Name.toString v))

          val avoid = StringSet.add avoid s
          and mapping = NameMap.insert mapping (v,s)
        in
          VarToTptp (avoid,mapping)
        end
    end;

local
  fun add (v,vm) = addVarToTptp vm v;
in
  val addListVarToTptp = List.foldl add;

  val addSetVarToTptp = NameSet.foldl add;
end;

fun getVarToTptp vm v =
    let
      val VarToTptp (_,mapping) = vm
    in
      case NameMap.peek mapping v of
        SOME s => s
      | NONE => die ("Unknown variable: " ^ v ^ ". Check the scope of quantifiers.")
    end;

(* ------------------------------------------------------------------------- *)
(* Mapping from TPTP variable names.                                         *)
(* ------------------------------------------------------------------------- *)

fun getVarFromTptp s = Name.fromString s;

(* ------------------------------------------------------------------------- *)
(* Mapping to TPTP function and relation names.                              *)
(* ------------------------------------------------------------------------- *)

datatype nameToTptp = NameToTptp of string NameArityMap.map;

local
  val emptyNames : string NameArityMap.map = NameArityMap.new ();

  fun addNames ({name,arity,tptp},mapping) =
      NameArityMap.insert mapping ((name,arity),tptp);

  val fromListNames = List.foldl addNames emptyNames;
in
  fun mkNameToTptp mapping = NameToTptp (fromListNames mapping);
end;

local
  fun escapeChar c =
      case c of
        #"\\" => "\\\\"
      | #"'" => "\\'"
      | #"\n" => "\\n"
      | #"\t" => "\\t"
      | _ => str c;

  val escapeString = String.translate escapeChar;
in
  fun singleQuote s = "'" ^ escapeString s ^ "'";
end;

fun getNameToTptp isTptp s = if isTptp s then s else singleQuote s;

fun getNameArityToTptp isZeroTptp isPlusTptp (NameToTptp mapping) na =
      case NameArityMap.peek mapping na of
        SOME s => s
      | NONE =>
        let
          val (n,a) = na
        val isTptp = if a = 0 then isZeroTptp else isPlusTptp
          val s = Name.toString n
        in
        getNameToTptp isTptp s
        end;

(* ------------------------------------------------------------------------- *)
(* Mapping from TPTP function and relation names.                            *)
(* ------------------------------------------------------------------------- *)

datatype nameFromTptp = NameFromTptp of (string * int, Name.name) Map.map;

local
  val stringArityCompare = prodCompare String.compare Int.compare;

  val emptyStringArityMap = Map.new stringArityCompare;

  fun addStringArityMap ({name,arity,tptp},mapping) =
      Map.insert mapping ((tptp,arity),name);

  val fromListStringArityMap =
      List.foldl addStringArityMap emptyStringArityMap;
in
  fun mkNameFromTptp mapping = NameFromTptp (fromListStringArityMap mapping);
end;

fun getNameFromTptp (NameFromTptp mapping) sa =
    case Map.peek mapping sa of
      SOME n => n
    | NONE =>
      let
        val (s,_) = sa
      in
        Name.fromString s
      end;

(* ------------------------------------------------------------------------- *)
(* Mapping to and from TPTP variable, function and relation names.           *)
(* ------------------------------------------------------------------------- *)

datatype mapping =
    Mapping of
      {varTo : varToTptp,
       fnTo : nameToTptp,
       relTo : nameToTptp,
       fnFrom : nameFromTptp,
       relFrom : nameFromTptp};

fun mkMapping mapping =
    let
      val {functionMapping,relationMapping} = mapping

      val varTo = emptyVarToTptp
      val fnTo = mkNameToTptp functionMapping
      val relTo = mkNameToTptp relationMapping

      val fnFrom = mkNameFromTptp functionMapping
      val relFrom = mkNameFromTptp relationMapping
    in
      Mapping
        {varTo = varTo,
         fnTo = fnTo,
         relTo = relTo,
         fnFrom = fnFrom,
         relFrom = relFrom}
    end;

fun addVarListMapping mapping vs =
    let
      val Mapping
            {varTo,
             fnTo,
             relTo,
             fnFrom,
             relFrom} = mapping

      val varTo = addListVarToTptp varTo vs
    in
      Mapping
        {varTo = varTo,
         fnTo = fnTo,
         relTo = relTo,
         fnFrom = fnFrom,
         relFrom = relFrom}
    end;

fun addVarSetMapping mapping vs =
    let
      val Mapping
            {varTo,
             fnTo,
             relTo,
             fnFrom,
             relFrom} = mapping

      val varTo = addSetVarToTptp varTo vs
    in
      Mapping
        {varTo = varTo,
         fnTo = fnTo,
         relTo = relTo,
         fnFrom = fnFrom,
         relFrom = relFrom}
    end;

fun varToTptp mapping v =
    let
      val Mapping {varTo,...} = mapping
    in
      getVarToTptp varTo v
    end;

fun fnToTptp mapping fa =
    let
      val Mapping {fnTo,...} = mapping
    in
      getNameArityToTptp isTptpConstName isTptpFnName fnTo fa
    end;

fun relToTptp mapping ra =
    let
      val Mapping {relTo,...} = mapping
    in
      getNameArityToTptp isTptpPropName isTptpRelName relTo ra
    end;

fun varFromTptp (_ : mapping) v = getVarFromTptp v;

fun fnFromTptp mapping fa =
    let
      val Mapping {fnFrom,...} = mapping
    in
      getNameFromTptp fnFrom fa
    end;

fun relFromTptp mapping ra =
    let
      val Mapping {relFrom,...} = mapping
    in
      getNameFromTptp relFrom ra
    end;

val defaultMapping =
    let
      fun lift {name,arity,tptp} =
          {name = Name.fromString name, arity = arity, tptp = tptp}

      val functionMapping = map lift defaultFunctionMapping
      and relationMapping = map lift defaultRelationMapping

      val mapping =
          {functionMapping = functionMapping,
           relationMapping = relationMapping}
    in
      mkMapping mapping
    end;

(* ------------------------------------------------------------------------- *)
(* Interpreting TPTP functions and relations in a finite model.              *)
(* ------------------------------------------------------------------------- *)

fun mkFixedMap funcModel relModel =
    let
      fun mkEntry {name,arity,model} = ((Name.fromString name, arity), model)

      fun mkMap l = NameArityMap.fromList (map mkEntry l)
    in
      {functionMap = mkMap funcModel,
       relationMap = mkMap relModel}
    end;

val defaultFixedMap = mkFixedMap defaultFunctionModel defaultRelationModel;

val defaultModel =
    let
      val {size = N, fixed = fix} = Model.default

      val fix = Model.mapFixed defaultFixedMap fix
    in
      {size = N, fixed = fix}
    end;

local
  fun toTptpMap toTptp =
      let
        fun add ((src,arity),dest,m) =
            let
              val src = Name.fromString (toTptp (src,arity))
            in
              NameArityMap.insert m ((src,arity),dest)
            end
      in
        fn m => NameArityMap.foldl add (NameArityMap.new ()) m
      end;

  fun toTptpFixedMap mapping fixMap =
      let
        val {functionMap = fnMap, relationMap = relMap} = fixMap

        val fnMap = toTptpMap (fnToTptp mapping) fnMap
        and relMap = toTptpMap (relToTptp mapping) relMap
      in
        {functionMap = fnMap,
         relationMap = relMap}
      end;
in
  fun ppFixedMap mapping fixMap =
      Model.ppFixedMap (toTptpFixedMap mapping fixMap);
end;

(* ------------------------------------------------------------------------- *)
(* TPTP roles.                                                               *)
(* ------------------------------------------------------------------------- *)

datatype role =
    AxiomRole
  | ConjectureRole
  | DefinitionRole
  | NegatedConjectureRole
  | PlainRole
  | TheoremRole
  | OtherRole of string;

fun isCnfConjectureRole role =
    case role of
      NegatedConjectureRole => true
    | _ => false;

fun isFofConjectureRole role =
    case role of
      ConjectureRole => true
    | _ => false;

fun toStringRole role =
    case role of
      AxiomRole => "axiom"
    | ConjectureRole => "conjecture"
    | DefinitionRole => "definition"
    | NegatedConjectureRole => "negated_conjecture"
    | PlainRole => "plain"
    | TheoremRole => "theorem"
    | OtherRole s => s;

fun fromStringRole s =
    case s of
      "axiom" => AxiomRole
    | "conjecture" => ConjectureRole
    | "definition" => DefinitionRole
    | "negated_conjecture" => NegatedConjectureRole
    | "plain" => PlainRole
    | "theorem" => TheoremRole
    | _ => OtherRole s;

val ppRole = Print.ppMap toStringRole Print.ppString;

(* ------------------------------------------------------------------------- *)
(* SZS statuses.                                                             *)
(* ------------------------------------------------------------------------- *)

datatype status =
    CounterSatisfiableStatus
  | TheoremStatus
  | SatisfiableStatus
  | UnknownStatus
  | GaveUpStatus
  | SyntaxErrorStatus
  | TimeoutStatus
  | ErrorStatus
  | UserStatus
  | UnsatisfiableStatus;

fun toStringStatus status =
    case status of
      CounterSatisfiableStatus => "CounterSatisfiable"
    | TheoremStatus => "Theorem"
    | SatisfiableStatus => "Satisfiable"
    | UnknownStatus => "Unknown"
    | GaveUpStatus => "GaveUp"
    | SyntaxErrorStatus => "SyntaxError"
    | TimeoutStatus => "Timeout"
    | ErrorStatus => "Error"
    | UserStatus => "User"
    | UnsatisfiableStatus => "Unsatisfiable";

val ppStatus = Print.ppMap toStringStatus Print.ppString;

(* ------------------------------------------------------------------------- *)
(* TPTP literals.                                                            *)
(* ------------------------------------------------------------------------- *)

datatype literal =
    Boolean of bool
  | Literal of Literal.literal;

fun destLiteral lit =
    case lit of
      Literal l => l
    | _ => raise Error "Tptp.destLiteral";

fun isBooleanLiteral lit =
    case lit of
      Boolean _ => true
    | _ => false;

fun equalBooleanLiteral b lit =
    case lit of
      Boolean b' => b = b'
    | _ => false;

fun negateLiteral (Boolean b) = (Boolean (not b))
  | negateLiteral (Literal l) = (Literal (Literal.negate l));

fun functionsLiteral (Boolean _) = NameAritySet.empty
  | functionsLiteral (Literal lit) = Literal.functions lit;

fun relationLiteral (Boolean _) = NONE
  | relationLiteral (Literal lit) = SOME (Literal.relation lit);

fun literalToFormula (Boolean true) = Formula.True
  | literalToFormula (Boolean false) = Formula.False
  | literalToFormula (Literal lit) = Literal.toFormula lit;

fun literalFromFormula Formula.True = Boolean true
  | literalFromFormula Formula.False = Boolean false
  | literalFromFormula fm = Literal (Literal.fromFormula fm);

fun freeVarsLiteral (Boolean _) = NameSet.empty
  | freeVarsLiteral (Literal lit) = Literal.freeVars lit;

(* ------------------------------------------------------------------------- *)
(* Printing formulas using TPTP syntax.                                      *)
(* ------------------------------------------------------------------------- *)

fun ppVar mapping v =
    let
      val s = varToTptp mapping v
    in
      Print.addString s
    end;

val fixMinus = String.translate (fn c => if c = #"~" then "-" else str c);

val iTokens = Print.tokensInfixes Term.infixes

fun destI (Term.Fn (f,[a,b])) =
      if StringSet.member f iTokens then SOME (f,a,b) else NONE
  | destI _ = NONE

fun isI tm = Option.isSome (destI tm)

fun ppTerm_infix mapping =
  let fun funargs f tms =
	    Print.blockProgram Print.Inconsistent (String.size f + 1)
	       [Print.addString (f ^ "("),
		Print.ppOpList "," term tms,
		Print.addString ")"]

      and basic (Term.Var v) = ppVar mapping v
	| basic (Term.Fn (c,[])) = Print.addString c
	| basic (Term.Fn ("-",[tm])) =
	    Print.blockProgram Print.Inconsistent 0
	       [Print.addString "-",
		molecule (tm,false)]
	| basic (Term.Rat r) =
	   (case Rat.quotient_of_rat r of
	        (m,1) => Print.addString (fixMinus (IntInf.toString m))
	      | (m,n) => Print.blockProgram Print.Inconsistent 0
			    [Print.addString (fixMinus (IntInf.toString m)),
			     Print.addString "/",
			     Print.addBreak 0,
			     Print.addString (IntInf.toString n)])
	| basic (Term.Fn (f,tms)) = funargs f tms
      and molecule (tm,_) =
	    if isI tm then Print.ppBracket "(" ")" term tm
	    else basic tm
      and term tm = Print.ppInfixes Term.infixes destI molecule (tm,false)
in Print.block Print.Inconsistent 0 o term end;

fun ppFnName mapping fa = Print.addString (fnToTptp mapping fa);

fun ppConst mapping c = ppFnName mapping (c,0);


fun ppTerm_plain mapping =
    let
      fun int n =
	if n<0 then "neg(" ^ IntInf.toString (~n) ^ ")" else IntInf.toString n
      fun rat2 (p,1) = int p
	| rat2 (p,q) = "divide(" ^ int p ^ "," ^ IntInf.toString q ^ ")"
      fun term tm =
          case tm of
            Term.Var v => ppVar mapping v
          | Term.Rat r => Print.addString (rat2 (Rat.quotient_of_rat r))
          | Term.Fn (f,tms) =>
            case length tms of
              0 => ppConst mapping f
            | a =>
              Print.blockProgram Print.Inconsistent 2
                [ppFnName mapping (f,a),
                 Print.addString "(",
                 Print.ppOpList "," term tms,
                 Print.addString ")"]
    in
      Print.block Print.Inconsistent 0 o term
    end;

fun ppRelName mapping ra = Print.addString (relToTptp mapping ra);

fun ppTerm t = if !standardTSTP then ppTerm_plain t else ppTerm_infix t;

fun ppProp mapping p = ppRelName mapping (p,0);

fun ppAtom mapping (r,tms) =
  if !standardTSTP then
    case length tms of
      0 => ppProp mapping r
    | a =>
      Print.blockProgram Print.Inconsistent 2
        [ppRelName mapping (r,a),
         Print.addString "(",
         Print.ppOpList "," (ppTerm mapping) tms,
         Print.addString ")"]
  else ppTerm_infix mapping (Term.Fn (r,tms));

local
  val neg = Print.addString "~ ";   (*LCP: no break*)

  fun fof mapping fm =
      case fm of
        Formula.And _ => assoc_binary mapping ("&", Formula.stripConj fm)
      | Formula.Or _ => assoc_binary mapping ("|", Formula.stripDisj fm)
      | Formula.Imp a_b => nonassoc_binary mapping ("=>",a_b)
      | Formula.Iff a_b => nonassoc_binary mapping ("<=>",a_b)
      | _ => unitary mapping fm

  and nonassoc_binary mapping (s,a_b) =
      Print.ppOp2 (" " ^ s) (unitary mapping) (unitary mapping) a_b

  and assoc_binary mapping (s,l) = Print.ppOpList (" " ^ s) (unitary mapping) l

  and unitary mapping fm =
      case fm of
        Formula.True => Print.addString "$true"
      | Formula.False => Print.addString "$false"
      | Formula.Forall _ => quantified mapping ("!", Formula.stripForall fm)
      | Formula.Exists _ => quantified mapping ("?", Formula.stripExists fm)
      | Formula.Not (Formula.Atom ("<=",[t,u])) =>
           Print.ppOp2 " <" (ppTerm mapping) (ppTerm mapping) (u,t)
      | Formula.Not (Formula.Atom ("=",[t,u])) =>
           Print.ppOp2 " !=" (ppTerm mapping) (ppTerm mapping) (t,u)
      | Formula.Not _ =>
	 let val (n,fm) = Formula.stripNeg fm
	 in
	    Print.blockProgram Print.Inconsistent 2
	      [Print.duplicate n neg, unitary mapping fm]
	 end
      | Formula.Atom atm => ppAtom mapping atm
      | _ =>
        Print.blockProgram Print.Inconsistent 1
          [Print.addString "(",
           fof mapping fm,
           Print.addString ")"]

  and quantified mapping (q,(vs,fm)) =
      let
        val mapping = addVarListMapping mapping vs
      in
        Print.blockProgram Print.Inconsistent 2
          [Print.addString q,
           Print.addString " ",
           Print.blockProgram Print.Inconsistent (String.size q)
             [Print.addString "[",
              Print.ppOpList "," (ppVar mapping) vs,
              Print.addString "] :"],
           Print.addBreak 1,
           unitary mapping fm]
      end;
in
  fun ppFof mapping fm = Print.block Print.Inconsistent 0 (fof mapping fm);
end;

(* ------------------------------------------------------------------------- *)
(* Lexing TPTP files.                                                        *)
(* ------------------------------------------------------------------------- *)

datatype token =
    AlphaNum of string
  | Punct of char
  | Quote of string;

fun isAlphaNum #"_" = true
  | isAlphaNum c = Char.isAlphaNum c;

local
  open Parse;

  infixr 9 >>++
  infixr 8 ++
  infixr 7 >>
  infixr 6 ||

  val alphaNumToken = atLeastOne (some isAlphaNum) >> (AlphaNum o implode);

  val punctToken =
      let
        val punctChars = "<>=-*+/\\?@|!$%&#^:;~()[]{}.,"
      in
        some (Char.contains punctChars) >> Punct
      end;

  val quoteToken =
      let
        val escapeParser =
            some (equal #"'") >> singleton ||
            some (equal #"\\") >> singleton

        fun stopOn #"'" = true
          | stopOn #"\n" = true
          | stopOn _ = false

        val quotedParser =
            some (equal #"\\") ++ escapeParser >> op:: ||
            some (not o stopOn) >> singleton
      in
        exactChar #"'" ++ many quotedParser ++ exactChar #"'" >>
        (fn (_,(l,_)) => Quote (implode (List.concat l)))
      end;

  val lexToken = alphaNumToken || punctToken || quoteToken;

  val space = many (some Char.isSpace) >> K ();
in
  val lexer = (space ++ lexToken ++ space) >> (fn ((),(tok,())) => tok);
end;

(* ------------------------------------------------------------------------- *)
(* TPTP clauses.                                                             *)
(* ------------------------------------------------------------------------- *)

type clause = literal list;

val clauseFunctions =
    let
      fun funcs (lit,acc) = NameAritySet.union (functionsLiteral lit) acc
    in
      foldl funcs NameAritySet.empty
    end;

val clauseRelations =
    let
      fun rels (lit,acc) =
          case relationLiteral lit of
            NONE => acc
          | SOME r => NameAritySet.add acc r
    in
      foldl rels NameAritySet.empty
    end;

val clauseFreeVars =
    let
      fun fvs (lit,acc) = NameSet.union (freeVarsLiteral lit) acc
    in
      foldl fvs NameSet.empty
    end;

fun clauseToFormula lits = Formula.listMkDisj (map literalToFormula lits);

fun clauseFromFormula fm = map literalFromFormula (Formula.stripDisj fm);

fun clauseFromLiteralSet cl =
    clauseFromFormula
      (Formula.listMkDisj (LiteralSet.transform Literal.toFormula cl));

fun ppClause mapping = Print.ppMap clauseToFormula (ppFof mapping);

(* ------------------------------------------------------------------------- *)
(* TPTP formula names.                                                       *)
(* ------------------------------------------------------------------------- *)

datatype formulaName = FormulaName of string;

datatype formulaNameSet = FormulaNameSet of formulaName Set.set;

fun compareFormulaName (FormulaName s1, FormulaName s2) =
    String.compare (s1,s2);

fun toTptpFormulaName (FormulaName s) =
    getNameToTptp isTptpFormulaName s;

val ppFormulaName = Print.ppMap toTptpFormulaName Print.ppString;

val emptyFormulaNameSet = FormulaNameSet (Set.empty compareFormulaName);

fun memberFormulaNameSet n (FormulaNameSet s) = Set.member n s;

fun addFormulaNameSet (FormulaNameSet s) n = FormulaNameSet (Set.add s n);

fun addListFormulaNameSet (FormulaNameSet s) l =
    FormulaNameSet (Set.addList s l);

(* ------------------------------------------------------------------------- *)
(* TPTP formula bodies.                                                      *)
(* ------------------------------------------------------------------------- *)

datatype formulaBody =
    CnfFormulaBody of literal list
  | FofFormulaBody of Formula.formula;

fun formulaBodyFunctions body =
    case body of
      CnfFormulaBody cl => clauseFunctions cl
    | FofFormulaBody fm => Formula.functions fm;

fun formulaBodyRelations body =
    case body of
      CnfFormulaBody cl => clauseRelations cl
    | FofFormulaBody fm => Formula.relations fm;

fun formulaBodyFreeVars body =
    case body of
      CnfFormulaBody cl => clauseFreeVars cl
    | FofFormulaBody fm => Formula.freeVars fm;

fun formulaBodyFreeVarsFOFonly body =
    case body of
      CnfFormulaBody cl => NameSet.empty
    | FofFormulaBody fm => Formula.freeVars fm;

fun ppFormulaBody mapping body =
    case body of
      CnfFormulaBody cl => ppClause mapping cl
    | FofFormulaBody fm => ppFof mapping (Formula.generalize fm);

(* ------------------------------------------------------------------------- *)
(* TPTP formula sources.                                                     *)
(* ------------------------------------------------------------------------- *)

datatype formulaSource =
    NoFormulaSource
  | StripFormulaSource of
      {inference : string,
       parents : formulaName list}
  | NormalizeFormulaSource of
      {inference : Normalize.inference,
       parents : formulaName list}
  | ProofFormulaSource of
      {inference : Proof.inference,
       parents : formulaName list};

fun isNoFormulaSource source =
    case source of
      NoFormulaSource => true
    | _ => false;

fun functionsFormulaSource source =
    case source of
      NoFormulaSource => NameAritySet.empty
    | StripFormulaSource _ => NameAritySet.empty
    | NormalizeFormulaSource data =>
      let
        val {inference = inf, parents = _} = data
      in
        case inf of
          Normalize.Axiom fm => Formula.functions fm
        | Normalize.Definition (_,fm) => Formula.functions fm
        | _ => NameAritySet.empty
      end
    | ProofFormulaSource data =>
      let
        val {inference = inf, parents = _} = data
      in
        case inf of
          Proof.Axiom cl => LiteralSet.functions cl
        | Proof.Arith (cl,_) => LiteralSet.functions cl
        | Proof.Decision (cl,_) => LiteralSet.functions cl
        | Proof.Split (cl,_) => LiteralSet.functions cl
        | Proof.Cases (cl,_) => LiteralSet.functions cl
        | Proof.CaseSplit (cl,_) => LiteralSet.functions cl
        | Proof.Assume atm => Atom.functions atm
        | Proof.Subst (sub,_) => Subst.functions sub
        | Proof.Resolve (atm,_,_) => Atom.functions atm
        | Proof.Refl tm => Term.functions tm
        | Proof.Equality (lit,_,tm) =>
          NameAritySet.union (Literal.functions lit) (Term.functions tm)
      end;

fun relationsFormulaSource source =
    case source of
      NoFormulaSource => NameAritySet.empty
    | StripFormulaSource _ => NameAritySet.empty
    | NormalizeFormulaSource data =>
      let
        val {inference = inf, parents = _} = data
      in
        case inf of
          Normalize.Axiom fm => Formula.relations fm
        | Normalize.Definition (_,fm) => Formula.relations fm
        | _ => NameAritySet.empty
      end
    | ProofFormulaSource data =>
      let
        val {inference = inf, parents = _} = data
      in
        case inf of
          Proof.Axiom cl => LiteralSet.relations cl
        | Proof.Arith (cl,_) => LiteralSet.relations cl
        | Proof.Decision (cl,_) => LiteralSet.relations cl
        | Proof.Split (cl,_) => LiteralSet.relations cl
        | Proof.Cases (cl,_) => LiteralSet.relations cl
        | Proof.CaseSplit (cl,_) => LiteralSet.relations cl
        | Proof.Assume atm => NameAritySet.singleton (Atom.relation atm)
        | Proof.Subst _ => NameAritySet.empty
        | Proof.Resolve (atm,_,_) => NameAritySet.singleton (Atom.relation atm)
        | Proof.Refl _ => NameAritySet.empty
        | Proof.Equality (lit,_,_) =>
          NameAritySet.singleton (Literal.relation lit)
      end;

fun freeVarsFormulaSource source =
    case source of
      NoFormulaSource => NameSet.empty
    | StripFormulaSource _ => NameSet.empty
    | NormalizeFormulaSource _ => NameSet.empty
    | ProofFormulaSource data =>
      let
        val {inference = inf, parents = _} = data
      in
        case inf of
          Proof.Axiom cl => LiteralSet.freeVars cl
        | Proof.Arith (cl,_) => LiteralSet.freeVars cl
        | Proof.Decision (cl,_) => LiteralSet.freeVars cl
        | Proof.Split (cl,_) => LiteralSet.freeVars cl
        | Proof.Cases (cl,_) => LiteralSet.freeVars cl
        | Proof.CaseSplit (cl,_) => LiteralSet.freeVars cl
        | Proof.Assume atm => Atom.freeVars atm
        | Proof.Subst (sub,_) => Subst.freeVars sub
        | Proof.Resolve (atm,_,_) => Atom.freeVars atm
        | Proof.Refl tm => Term.freeVars tm
        | Proof.Equality (lit,_,tm) =>
          NameSet.union (Literal.freeVars lit) (Term.freeVars tm)
      end;

local
  val GEN_INFERENCE = "inference"
  and GEN_INTRODUCED = "introduced";

  fun nameStrip inf = inf;

  fun ppStrip _ _ = Print.skip;

  fun nameNormalize inf =
      case inf of
        Normalize.Axiom _ => "canonicalize"
      | Normalize.Definition _ => "canonicalize"
      | Normalize.Simplify _ => "simplify"
      | Normalize.Conjunct _ => "conjunct"
      | Normalize.Specialize _ => "specialize"
      | Normalize.Skolemize _ => "skolemize"
      | Normalize.Clausify _ => "clausify";

  fun ppNormalize _ _ = Print.skip;

  fun nameProof inf =
      case inf of
        Proof.Axiom _ => "canonicalize"
      | Proof.Arith _ => "arithmetic"
      | Proof.Decision _ => "decision"
      | Proof.Split _ => "split"
      | Proof.Cases _ => "cases"
      | Proof.CaseSplit _ => "caseSplit"
      | Proof.Assume _ => "assume"
      | Proof.Subst _ => "subst"
      | Proof.Resolve _ => "resolve"
      | Proof.Refl _ => "refl"
      | Proof.Equality _ => "equality";

  local
    fun ppTermInf mapping = ppTerm mapping;

    fun ppAtomInf mapping atm =
        case total Atom.destEq atm of
          SOME (a,b) => ppAtom mapping (Name.fromString "$equal", [a,b])
        | NONE => ppAtom mapping atm;

    fun ppLiteralInf mapping (pol,atm) =
        Print.sequence
          (if pol then Print.skip else Print.addString "~ ")
          (ppAtomInf mapping atm);
  in
    fun ppProofTerm mapping =
        Print.ppBracket "$fot(" ")" (ppTermInf mapping);

    fun ppProofAtom mapping =
        Print.ppBracket "$cnf(" ")" (ppAtomInf mapping);

    fun ppProofLiteral mapping =
        Print.ppBracket "$cnf(" ")" (ppLiteralInf mapping);
  end;

  val ppProofVar = ppVar;

  val ppProofPath = Term.ppPath;

  fun ppProof mapping inf =
      Print.blockProgram Print.Inconsistent 1
        [Print.addString "[",
         (case inf of
            Proof.Axiom _ => Print.skip
	  | Proof.Arith (_,_) => Print.skip
	  | Proof.Decision (_,_) => Print.skip
	  | Proof.Split (_,_) => Print.skip
	  | Proof.Cases (_,_) => Print.skip
          | Proof.CaseSplit (_,_) => Print.skip
          | Proof.Assume atm => ppProofAtom mapping atm
          | Proof.Subst _ => Print.skip
          | Proof.Resolve (atm,_,_) => if !fullProofs then ppProofAtom mapping atm else Print.skip
          | Proof.Refl tm => ppProofTerm mapping tm
          | Proof.Equality (lit,path,tm) =>
            Print.program
              [ppProofLiteral mapping lit,
               Print.addString ",",
               Print.addBreak 1,
               ppProofPath path,
               Print.addString ",",
               Print.addBreak 1,
               ppProofTerm mapping tm]),
         Print.addString "]"];

  val ppParent = ppFormulaName;

  fun ppProofSubst mapping =
      Print.ppMap Subst.toList
        (Print.ppList
           (Print.ppBracket "bind(" ")"
              (Print.ppOp2 "," (ppProofVar mapping)
                 (ppProofTerm mapping))));

  fun ppProofParent mapping (p,s) =
      if Subst.null s orelse not (!fullProofs) then ppParent p
      else Print.ppOp2 " :" ppParent (ppProofSubst mapping) (p,s);
in
  fun ppFormulaSource mapping source =
      case source of
        NoFormulaSource => Print.skip
      | StripFormulaSource {inference,parents} =>
        let
          val gen = GEN_INFERENCE

          val name = nameStrip inference
        in
          Print.blockProgram Print.Inconsistent (size gen + 1)
            [Print.addString gen,
             Print.addString "(",
             Print.addString name,
             Print.addString ",",
             Print.addBreak 1,
             Print.ppBracket "[" "]" (ppStrip mapping) inference,
             Print.addString ",",
             Print.addBreak 1,
             Print.ppList ppParent parents,
             Print.addString ")"]
        end
      | NormalizeFormulaSource {inference,parents} =>
        let
          val gen = GEN_INFERENCE

          val name = nameNormalize inference
        in
          Print.blockProgram Print.Inconsistent (size gen + 1)
            [Print.addString gen,
             Print.addString "(",
             Print.addString name,
             Print.addString ",",
             Print.addBreak 1,
             Print.ppBracket "[" "]" (ppNormalize mapping) inference,
             Print.addString ",",
             Print.addBreak 1,
             Print.ppList ppParent parents,
             Print.addString ")"]
        end
      | ProofFormulaSource {inference,parents} =>
        let
          val isTaut = null parents

          val gen = if isTaut then GEN_INTRODUCED else GEN_INFERENCE

          val name = nameProof inference

          val parents =
              let
                val sub =
                    case inference of
                      Proof.Subst (s,_) => s
                    | _ => Subst.empty
              in
                map (fn parent => (parent,sub)) parents
              end
        in
          Print.blockProgram Print.Inconsistent (size gen + 1)
            ([Print.addString gen,
              Print.addString "("] @
             (if isTaut then
                [Print.addString "tautology",
                 Print.addString ",",
                 Print.addBreak 1,
                 Print.blockProgram Print.Inconsistent 1
                  ([Print.addString "[", Print.addString name] @
                   (if !fullProofs then
		     [Print.addString ",",
		      Print.addBreak 1,
		      ppProof mapping inference,
		      Print.addString "]"]
		   else [Print.addString "]"]))
                ]
              else
                [Print.addString name,
                 Print.addString ",",
                 Print.addBreak 1,
                 ppProof mapping inference,
                 Print.addString ",",
                 Print.addBreak 1,
                 Print.ppList (ppProofParent mapping) parents]) @
             [Print.addString ")"])
        end
end;

(* ------------------------------------------------------------------------- *)
(* TPTP formulas.                                                            *)
(* ------------------------------------------------------------------------- *)

datatype formula =
    Formula of
      {name : formulaName,
       role : role,
       body : formulaBody,
       source : formulaSource};

fun nameFormula (Formula {name,...}) = name;

fun roleFormula (Formula {role,...}) = role;

fun bodyFormula (Formula {body,...}) = body;

fun sourceFormula (Formula {source,...}) = source;

fun functionsFormula fm =
    let
      val bodyFns = formulaBodyFunctions (bodyFormula fm)
      and sourceFns = functionsFormulaSource (sourceFormula fm)
    in
      NameAritySet.union bodyFns sourceFns
    end;

fun relationsFormula fm =
    let
      val bodyRels = formulaBodyRelations (bodyFormula fm)
      and sourceRels = relationsFormulaSource (sourceFormula fm)
    in
      NameAritySet.union bodyRels sourceRels
    end;

fun freeVarsFormula fm =
    let
      val bodyFvs = formulaBodyFreeVars (bodyFormula fm)
      and sourceFvs = freeVarsFormulaSource (sourceFormula fm)
    in
      NameSet.union bodyFvs sourceFvs
    end;

fun freeVarsFormulaFOFonly fm =
    let
      val bodyFvs = formulaBodyFreeVarsFOFonly (bodyFormula fm)
    in
      bodyFvs
    end;

val freeVarsListFormula =
    let
      fun add (fm,vs) = NameSet.union vs (freeVarsFormula fm)
    in
      List.foldl add NameSet.empty
    end;

val freeVarsListFormulaFOFonly =
    let
      fun add (fm,vs) = NameSet.union vs (freeVarsFormulaFOFonly fm)
    in
      List.foldl add NameSet.empty
    end;

fun isCnfConjectureFormula fm =
    case fm of
      Formula {role, body = CnfFormulaBody _, ...} => isCnfConjectureRole role
    | _ => false;

fun isFofConjectureFormula fm =
    case fm of
      Formula {role, body = FofFormulaBody _, ...} => isFofConjectureRole role
    | _ => false;

fun isConjectureFormula fm =
    isCnfConjectureFormula fm orelse
    isFofConjectureFormula fm;

(* Parsing and pretty-printing *)

fun ppFormula mapping fm =
    let
      val Formula {name,role,body,source} = fm

      val gen =
          case body of
            CnfFormulaBody _ => "cnf"
          | FofFormulaBody _ => "fof"
    in
      Print.blockProgram Print.Inconsistent (size gen + 1)
        ([Print.addString gen,
          Print.addString "(",
          ppFormulaName name,
          Print.addString ",",
          Print.addBreak 1,
          ppRole role,
          Print.addString ",",
          Print.addBreak 1,
          Print.blockProgram Print.Consistent 1
            [Print.addString "(",
             ppFormulaBody mapping body,
             Print.addString ")"]] @
         (if isNoFormulaSource source then []
          else
            [Print.addString ",",
             Print.addBreak 1,
             ppFormulaSource mapping source]) @
         [Print.addString ")."])
    end;

fun formulaToString mapping = Print.toString (ppFormula mapping);

(* ------------------------------------------------------------------------- *)
(* Include declarations.                                                     *)
(* ------------------------------------------------------------------------- *)

fun ppInclude i =
    Print.blockProgram Print.Inconsistent 2
      [Print.addString "include('",
       Print.addString i,
       Print.addString "')."];

val includeToString = Print.toString ppInclude;

(* ------------------------------------------------------------------------- *)
(* Clause information.                                                       *)
(* ------------------------------------------------------------------------- *)

datatype clauseSource =
    CnfClauseSource of formulaName * literal list
  | FofClauseSource of Normalize.thm;

type 'a clauseInfo = 'a LiteralSetMap.map;

type clauseNames = formulaName clauseInfo;

type clauseRoles = role clauseInfo;

type clauseSources = clauseSource clauseInfo;

val noClauseNames : clauseNames = LiteralSetMap.new ();

val allClauseNames : clauseNames -> formulaNameSet =
    let
      fun add (_,n,s) = addFormulaNameSet s n
    in
      LiteralSetMap.foldl add emptyFormulaNameSet
    end;

val noClauseRoles : clauseRoles = LiteralSetMap.new ();

val noClauseSources : clauseSources = LiteralSetMap.new ();

(* ------------------------------------------------------------------------- *)
(* Comments.                                                                 *)
(* ------------------------------------------------------------------------- *)

fun mkLineComment "" = "%"
  | mkLineComment line = "% " ^ line;

fun destLineComment cs =
    case cs of
      [] => ""
    | #"%" :: #" " :: rest => implode rest
    | #"%" :: rest => implode rest
    | _ => raise Error "Tptp.destLineComment";

val isLineComment = can destLineComment;

(* ------------------------------------------------------------------------- *)
(* TPTP problems.                                                            *)
(* ------------------------------------------------------------------------- *)

type comments = string list;

type includes = string list;

datatype item = Comment of string | Include of string | Fml of formula;

datatype problem =
    Problem of
      {comments : comments,
       includes : includes,
       formulas : formula list};

fun hasCnfConjecture (Problem {formulas,...}) =
    List.exists isCnfConjectureFormula formulas;

fun hasFofConjecture (Problem {formulas,...}) =
    List.exists isFofConjectureFormula formulas;

fun hasConjecture (Problem {formulas,...}) =
    List.exists isConjectureFormula formulas;

fun freeVars (Problem {formulas,...}) = freeVarsListFormula formulas;


(* version of freeVars which only looks at fofs not cnfs *)
fun freeVarsFOFonly (Problem {formulas,...}) = freeVarsListFormulaFOFonly formulas
       



local
  fun bump n avoid =
      let
        val s = FormulaName (Int.toString n)
      in
        if memberFormulaNameSet s avoid then bump (n + 1) avoid
        else (s, n, addFormulaNameSet avoid s)
      end;

  fun fromClause defaultRole names roles cl (n,avoid) =
      let
        val (name,n,avoid) =
            case LiteralSetMap.peek names cl of
              SOME name => (name,n,avoid)
            | NONE => bump n avoid

        val role = Option.getOpt (LiteralSetMap.peek roles cl, defaultRole)

        val body = CnfFormulaBody (clauseFromLiteralSet cl)

        val source = NoFormulaSource

        val formula =
            Formula
              {name = name,
               role = role,
               body = body,
               source = source}
      in
        (formula,(n,avoid))
      end;
in
  fun mkProblem {comments,includes,names,roles,problem} =
      let
        fun fromCl defaultRole = fromClause defaultRole names roles

        val {axioms,conjecture} = problem

        val n_avoid = (0, allClauseNames names)

        val (axiomFormulas,n_avoid) = maps (fromCl AxiomRole) axioms n_avoid

        val (conjectureFormulas,_) =
            maps (fromCl NegatedConjectureRole) conjecture n_avoid

        val formulas = axiomFormulas @ conjectureFormulas
      in
        Problem
          {comments = comments,
           includes = includes,
           formulas = formulas}
      end;
end;

type normalization =
     {problem : Problem.problem,
      sources : clauseSources};

val initialNormalization : normalization =
    {problem = {axioms = [], conjecture = []},
     sources = noClauseSources};

datatype problemGoal =
    NoGoal
  | CnfGoal of (formulaName * clause) list
  | FofGoal of (formulaName * Formula.formula) list;

local
  fun partitionFormula (formula,(cnfAxioms,fofAxioms,cnfGoals,fofGoals)) =
      let
        val Formula {name,role,body,...} = formula
      in
        case body of
          CnfFormulaBody cl =>
          if isCnfConjectureRole role then
            let
              val cnfGoals = (name,cl) :: cnfGoals
            in
              (cnfAxioms,fofAxioms,cnfGoals,fofGoals)
            end
          else
            let
              val cnfAxioms = (name,cl) :: cnfAxioms
            in
              (cnfAxioms,fofAxioms,cnfGoals,fofGoals)
            end
        | FofFormulaBody fm =>
          if isFofConjectureRole role then
            let
              val fofGoals = (name,fm) :: fofGoals
            in
              (cnfAxioms,fofAxioms,cnfGoals,fofGoals)
            end
          else
            let
              val fofAxioms = (name,fm) :: fofAxioms
            in
              (cnfAxioms,fofAxioms,cnfGoals,fofGoals)
            end
      end;

  fun partitionFormulas fms =
      let
        val (cnfAxioms,fofAxioms,cnfGoals,fofGoals) =
            List.foldl partitionFormula ([],[],[],[]) fms

        val goal =
            case (rev cnfGoals, rev fofGoals) of
              ([],[]) => NoGoal
            | (cnfGoals,[]) => CnfGoal cnfGoals
            | ([],fofGoals) => FofGoal fofGoals
            | (_ :: _, _ :: _) =>
              raise Error "TPTP problem has both cnf and fof conjecture formulas"
      in
        {cnfAxioms = rev cnfAxioms,
         fofAxioms = rev fofAxioms,
         goal = goal}
      end;

  fun addClauses role clauses acc : normalization =
      let
        fun addClause (cl_src,sources) =
            LiteralSetMap.insert sources cl_src

        val {problem,sources} : normalization = acc
        val {axioms,conjecture} = problem

        val cls = map fst clauses
        val (axioms,conjecture) =
            if isCnfConjectureRole role then (axioms, cls @ conjecture)
            else (cls @ axioms, conjecture)

        val problem = {axioms = axioms, conjecture = conjecture}
        and sources = List.foldl addClause sources clauses
      in
        {problem = problem,
         sources = sources}
      end;

  fun addCnf role ((name,clause),(norm,cnf)) =
      if List.exists (equalBooleanLiteral true) clause then (norm,cnf)
      else
        let
          val cl = List.mapPartial (total destLiteral) clause
          val cl = LiteralSet.fromList cl

          val src = CnfClauseSource (name,clause)

          val norm = addClauses role [(cl,src)] norm
        in
          (norm,cnf)
        end;

  val addCnfAxiom = addCnf AxiomRole;

  val addCnfGoal = addCnf NegatedConjectureRole;

  fun addFof role (th,(norm,cnf)) =
      let
        fun sourcify (cl,inf) = (cl, FofClauseSource inf)

        val (clauses,cnf) = Normalize.addCnf th cnf
        val clauses = map sourcify clauses
        val norm = addClauses role clauses norm
      in
        (norm,cnf)
      end;

  fun addFofAxiom ((_,fm),acc) =
      addFof AxiomRole (Normalize.mkAxiom fm, acc);

  fun normProblem subgoal (norm,_) =
      let
        val {problem,sources} = norm
        val {axioms,conjecture} = problem
        val problem = {axioms = rev axioms, conjecture = rev conjecture}
      in
        {subgoal = subgoal,
         problem = problem,
         sources = sources}
      end;

  val normProblemFalse = normProblem (Formula.False,[]);

  fun splitProblem acc =
      let
        fun mk parents subgoal =
            let
              val subgoal = Formula.generalize subgoal

              val th = Normalize.mkAxiom (Formula.Not subgoal)

              val acc = addFof NegatedConjectureRole (th,acc)
            in
              normProblem (subgoal,parents) acc
            end

        fun split (name,goal) =
            let
              val subgoals = Formula.splitGoal goal
              val subgoals =
                  if null subgoals then [Formula.True] else subgoals

              val parents = [name]
            in
              map (mk parents) subgoals
            end
      in
        fn goals => List.concat (map split goals)
      end;

  fun clausesToGoal cls =
      let
        val cls = map (Formula.generalize o clauseToFormula o snd) cls
      in
        Formula.listMkConj cls
      end;

  fun formulasToGoal fms =
      let
        val fms = map (Formula.generalize o snd) fms
      in
        Formula.listMkConj fms
      end;
in
  fun goal (Problem {formulas,...}) =
      let
        val {cnfAxioms,fofAxioms,goal} = partitionFormulas formulas

        val fm =
            case goal of
              NoGoal => Formula.False
            | CnfGoal cls => Formula.Imp (clausesToGoal cls, Formula.False)
            | FofGoal goals => formulasToGoal goals

        val fm =
            if null fofAxioms then fm
            else Formula.Imp (formulasToGoal fofAxioms, fm)

        val fm =
            if null cnfAxioms then fm
            else Formula.Imp (clausesToGoal cnfAxioms, fm)
      in
        fm
      end;

  fun normalize (Problem {formulas,...}) =
      let
        val {cnfAxioms,fofAxioms,goal} = partitionFormulas formulas

        val acc = (initialNormalization, Normalize.initialCnf)
        val acc = List.foldl addCnfAxiom acc cnfAxioms
        val acc = List.foldl addFofAxiom acc fofAxioms
      in
        case goal of
          NoGoal => [normProblemFalse acc]
        | CnfGoal cls => [normProblemFalse (List.foldl addCnfGoal acc cls)]
        | FofGoal goals => splitProblem acc goals
      end;
end;

local
  val newline = Stream.singleton "\n";

  fun spacer top = if top then Stream.Nil else newline;

  fun mkComment comment = mkLineComment comment ^ "\n";

  fun mkInclude inc = includeToString inc ^ "\n";

  fun formulaStream _ _ [] = Stream.Nil
    | formulaStream mapping top (h :: t) =
      Stream.append
        (Stream.concatList
           [spacer top,
            Stream.singleton (formulaToString mapping h),
            newline])
        (fn () => formulaStream mapping false t);
in
  fun write {problem,mapping,filename} =
      let
        val Problem {comments,includes,formulas} = problem

        val includesTop = null comments
        val formulasTop = includesTop andalso null includes
      in
        Stream.toTextFile
          {filename = filename}
          (Stream.concatList
             [Stream.map mkComment (Stream.fromList comments),
              spacer includesTop,
              Stream.map mkInclude (Stream.fromList includes),
              formulaStream mapping formulasTop formulas])
      end;
end;

(* ------------------------------------------------------------------------- *)
(* TSTP proofs.                                                              *)
(* ------------------------------------------------------------------------- *)

local
  fun newName avoid prefix =
      let
        fun bump i =
            let
              val name = FormulaName (prefix ^ Int.toString i)
              val i = i + 1
            in
              if memberFormulaNameSet name avoid then bump i else (name,i)
            end
      in
        bump
      end;

  fun lookupClauseSource sources cl =
      case LiteralSetMap.peek sources cl of
        SOME src => src
      | NONE => raise Bug "Tptp.lookupClauseSource";

  fun lookupFormulaName fmNames fm =
      case FormulaMap.peek fmNames fm of
        SOME name => name
      | NONE => raise Bug "Tptp.lookupFormulaName";

  fun lookupClauseName clNames cl =
      case LiteralSetMap.peek clNames cl of
        SOME name => name
      | NONE => raise Bug "Tptp.lookupClauseName";

  fun lookupClauseSourceName sources fmNames cl =
      case lookupClauseSource sources cl of
        CnfClauseSource (name,_) => name
      | FofClauseSource th =>
        let
          val (fm,_) = Normalize.destThm th
        in
          lookupFormulaName fmNames fm
        end;

  fun collectProofDeps sources ((_,inf),names_ths) =
      case inf of
        Proof.Axiom cl =>
        let
          val (names,ths) = names_ths
        in
          case lookupClauseSource sources cl of
            CnfClauseSource (name,_) =>
            let
              val names = addFormulaNameSet names name
            in
              (names,ths)
            end
          | FofClauseSource th =>
            let
              val ths = th :: ths
            in
              (names,ths)
            end
        end
      | _ => names_ths;

  fun collectNormalizeDeps ((_,inf,_),fofs_defs) =
      case inf of
        Normalize.Axiom fm =>
        let
          val (fofs,defs) = fofs_defs
          val fofs = FormulaSet.add fofs fm
        in
          (fofs,defs)
        end
      | Normalize.Definition n_d =>
        let
          val (fofs,defs) = fofs_defs
          val defs = StringMap.insert defs n_d
        in
          (fofs,defs)
        end
      | _ => fofs_defs;

  fun collectSubgoalProofDeps subgoalProof (names,fofs,defs) =
      let
        val {subgoal,sources,refutation} = subgoalProof

        val names = addListFormulaNameSet names (snd subgoal)

        val proof = Proof.proof refutation

        val (names,ths) =
            List.foldl (collectProofDeps sources) (names,[]) proof

        val normalization = Normalize.proveThms (rev ths)

        val (fofs,defs) =
            List.foldl collectNormalizeDeps (fofs,defs) normalization

        val subgoalProof =
            {subgoal = subgoal,
             normalization = normalization,
             sources = sources,
             proof = proof}
      in
        (subgoalProof,(names,fofs,defs))
      end;

  fun addProblemFormula names fofs (formula,(avoid,formulas,fmNames)) =
      let
        val name = nameFormula formula

        val avoid = addFormulaNameSet avoid name

        val (formulas,fmNames) =
            if memberFormulaNameSet name names then
              (formula :: formulas, fmNames)
            else
              case bodyFormula formula of
                CnfFormulaBody _ => (formulas,fmNames)
              | FofFormulaBody fm =>
                if not (FormulaSet.member fm fofs) then (formulas,fmNames)
                else (formula :: formulas, FormulaMap.insert fmNames (fm,name))
      in
        (avoid,formulas,fmNames)
      end;

  fun addDefinitionFormula avoid (_,def,(formulas,i,fmNames)) =
      let
        val (name,i) = newName avoid "definition_" i

        val role = DefinitionRole

        val body = FofFormulaBody def

        val source = NoFormulaSource

        val formula =
            Formula
              {name = name,
               role = role,
               body = body,
               source = source}

        val formulas = formula :: formulas

        val fmNames = FormulaMap.insert fmNames (def,name)
      in
        (formulas,i,fmNames)
      end;

  fun addSubgoalFormula avoid subgoalProof (formulas,i) =
      let
        val {subgoal,normalization,sources,proof} = subgoalProof

        val (fm,pars) = subgoal

        val (name,i) = newName avoid "subgoal_" i

        val number = i - 1

        val (subgoal,formulas) =
            if null pars then (NONE,formulas)
            else
              let
                val role = PlainRole

                val body = FofFormulaBody fm

                val source =
                    StripFormulaSource
                      {inference = "strip",
                       parents = pars}

                val formula =
                    Formula
                      {name = name,
                       role = role,
                       body = body,
                       source = source}
              in
                (SOME (name,fm), formula :: formulas)
              end

        val subgoalProof =
            {number = number,
             subgoal = subgoal,
             normalization = normalization,
             sources = sources,
             proof = proof}
      in
        (subgoalProof,(formulas,i))
      end;

  fun mkNormalizeFormulaSource fmNames inference fms =
      let
        val fms =
            case inference of
              Normalize.Axiom fm => fm :: fms
            | Normalize.Definition (_,fm) => fm :: fms
            | _ => fms

        val parents = map (lookupFormulaName fmNames) fms
      in
        NormalizeFormulaSource
          {inference = inference,
           parents = parents}
      end;

  fun mkProofFormulaSource sources fmNames clNames inference =
      let
        val parents =
            case inference of
              Proof.Axiom cl => [lookupClauseSourceName sources fmNames cl]
            | _ =>
              let
                val cls = map Thm.clause (Proof.parents inference)
              in
                map (lookupClauseName clNames) cls
              end
      in
          ProofFormulaSource
            {inference = inference,
             parents = parents}
        end;

  fun addNormalizeFormula avoid prefix ((fm,inf,fms),acc) =
      let
        val (formulas,i,fmNames) = acc

        val (name,i) = newName avoid prefix i

        val role = PlainRole

        val body = FofFormulaBody fm

        val source = mkNormalizeFormulaSource fmNames inf fms

        val formula =
            Formula
              {name = name,
               role = role,
               body = body,
               source = source}

        val formulas = formula :: formulas

        val fmNames = FormulaMap.insert fmNames (fm,name)
      in
        (formulas,i,fmNames)
      end;

  fun isSameClause sources inf =
      case inf of
        Proof.Axiom cl =>
          (case lookupClauseSource sources cl of
             CnfClauseSource (name,lits) =>
             if List.exists isBooleanLiteral lits then NONE
             else SOME name
           | _ => NONE)
      | _ => NONE;

  fun addProofFormula avoid sources fmNames prefix ((th,inf),acc) =
      let
        val (formulas,i,clNames) = acc

        val cl = Thm.clause th
      in
        case isSameClause sources inf of
          SOME name =>
          let
            val clNames = LiteralSetMap.insert clNames (cl,name)
          in
            (formulas,i,clNames)
          end
        | NONE =>
          let
        val (name,i) = newName avoid prefix i

        val role = PlainRole

        val body = CnfFormulaBody (clauseFromLiteralSet cl)

        val source = mkProofFormulaSource sources fmNames clNames inf

        val formula =
            Formula
              {name = name,
               role = role,
               body = body,
               source = source}

        val formulas = formula :: formulas

        val clNames = LiteralSetMap.insert clNames (cl,name)
      in
        (formulas,i,clNames)
          end
      end;

  fun addSubgoalProofFormulas avoid fmNames (subgoalProof,formulas) =
      let
        val {number,subgoal,normalization,sources,proof} = subgoalProof

        val (formulas,fmNames) =
            case subgoal of
              NONE => (formulas,fmNames)
            | SOME (name,fm) =>
              let
                val source =
                    StripFormulaSource
                      {inference = "negate",
                       parents = [name]}

                val prefix = "negate_" ^ Int.toString number ^ "_"

                val (name,_) = newName avoid prefix 0

                val role = PlainRole

                val fm = Formula.Not fm

                val body = FofFormulaBody fm

                val formula =
                    Formula
                      {name = name,
                       role = role,
                       body = body,
                       source = source}

                val formulas = formula :: formulas

                val fmNames = FormulaMap.insert fmNames (fm,name)
              in
                (formulas,fmNames)
              end

        val prefix = "normalize_" ^ Int.toString number ^ "_"
        val (formulas,_,fmNames) =
            List.foldl (addNormalizeFormula avoid prefix)
              (formulas,0,fmNames) normalization

        val prefix = "refute_" ^ Int.toString number ^ "_"
        val clNames : formulaName LiteralSetMap.map = LiteralSetMap.new ()
        val (formulas,_,_) =
            List.foldl (addProofFormula avoid sources fmNames prefix)
              (formulas,0,clNames) proof
      in
        formulas
      end;
in
  fun fromProof {problem,proofs} =
      let
        val names = emptyFormulaNameSet
        and fofs = FormulaSet.empty
        and defs : Formula.formula StringMap.map = StringMap.new ()

        val (proofs,(names,fofs,defs)) =
            maps collectSubgoalProofDeps proofs (names,fofs,defs)

        val Problem {formulas,...} = problem

        val fmNames : formulaName FormulaMap.map = FormulaMap.new ()
        val (avoid,formulas,fmNames) =
            List.foldl (addProblemFormula names fofs)
              (emptyFormulaNameSet,[],fmNames) formulas

        val (formulas,_,fmNames) =
            StringMap.foldl (addDefinitionFormula avoid)
              (formulas,0,fmNames) defs

        val (proofs,(formulas,_)) =
            maps (addSubgoalFormula avoid) proofs (formulas,0)

        val formulas =
            List.foldl (addSubgoalProofFormulas avoid fmNames) formulas proofs
      in
        rev formulas
      end
(*MetisDebug
      handle Error err => raise Bug ("Tptp.fromProof: shouldn't fail:\n" ^ err);
*)
end;

end
