(* ========================================================================= *)
(* FIRST ORDER LOGIC TERMS                                                   *)
(* Copyright (c) 2001 Joe Hurd, distributed under the MIT license            *)

(* ========================================================================= *)

structure Term :> Term =
struct

open Useful;

(* ------------------------------------------------------------------------- *)
(* A type of first order logic terms.                                        *)
(* ------------------------------------------------------------------------- *)

type var = Name.name;

type functionName = Name.name;

type function = functionName * int;

type const = functionName;

datatype term =
    Var of Name.name
  | Rat of Rat.rat  (*LCP Rational numbers are primitive*)
  | Fn of Name.name * term list;

(* ------------------------------------------------------------------------- *)
(* Constructors and destructors.                                             *)
(* ------------------------------------------------------------------------- *)

fun isGround (Fn (_,args)) = List.all isGround args
  | isGround (Rat _) = true
  | isGround (Var _) = false;

(* Additional "ground" testing function which considers only terms containing *)
(* Skolem functions of at least one argument to be NOT ground.                *)
fun containsSkolemFunction (Fn (_,[])) = false
 |  containsSkolemFunction (Rat _) = false
 |  containsSkolemFunction (Var _) = false
 |  containsSkolemFunction (Fn (name,args))=
    if(String.isPrefix "sko" name) then true else
    List.exists containsSkolemFunction args;


(* Variables *)

fun destVar (Var v) = v
  | destVar _ = raise Error "destVar";

fun isVar (Var v) = true
  | isVar _ = false;

fun destRat (Rat r) = r
  | destRat _ = raise Error "destRat";

fun isRat (Rat _) = true
  | isRat _ = false;

fun equalVar v (Var v') = Name.equal v v'
  | equalVar _ _ = false;

(* Functions *)

fun destFn (Fn f) = f
  | destFn _ = raise Error "destFn";

val isFn = can destFn;

fun fnName tm = fst (destFn tm);

fun fnArguments tm = snd (destFn tm);

fun fnArity tm = length (fnArguments tm);

fun fnFunction tm = (fnName tm, fnArity tm);

local
  fun func fs [] = fs
    | func fs (Fn (n,l) :: tms) = func (NameAritySet.add fs (n, length l)) (l @ tms)
    | func fs (_ :: tms) = func fs tms
in
  fun functions tm = func NameAritySet.empty [tm];
end;

local
  fun func fs [] = fs
    | func fs (Fn (n,l) :: tms) = func (NameSet.add fs n) (l @ tms)
    | func fs (_ :: tms) = func fs tms
in
  fun functionNames tm = func NameSet.empty [tm];
end;

(* Constants *)

fun mkConst c = (Fn (c, []));

fun destConst (Fn (c, [])) = c
  | destConst _ = raise Error "destConst";

val isConst = can destConst;

(* Binary functions *)

fun mkBinop f (a,b) = Fn (f,[a,b]);

fun destBinop f (Fn (x,[a,b])) =
    if Name.equal x f then (a,b) else raise Error "Term.destBinop: wrong binop"
  | destBinop _ _ = raise Error "Term.destBinop: not a binop";

fun isBinop f = can (destBinop f);

(* ------------------------------------------------------------------------- *)
(* The size of a term in symbols.                                            *)
(* ------------------------------------------------------------------------- *)

val VAR_SYMBOLS = 1;
val RAT_SYMBOLS = 5;
val FN_SYMBOLS = 1;

local
  fun sz n [] = n
    | sz n (Var _ :: tms) = sz (n + VAR_SYMBOLS) tms
    | sz n (Rat _ :: tms) = sz (n + RAT_SYMBOLS) tms
    | sz n (Fn (func,args) :: tms) = sz (n + FN_SYMBOLS) (args @ tms);
in
  fun symbols tm = sz 0 [tm];
end;

(* ------------------------------------------------------------------------- *)
(* A total comparison function for terms.                                    *)
(* ------------------------------------------------------------------------- *)

local
  fun cmp [] [] = EQUAL
    | cmp (tm1 :: tms1) (tm2 :: tms2) =
      let
        val tm1_tm2 = (tm1,tm2)
      in
        if Portable.pointerEqual tm1_tm2 then cmp tms1 tms2
        else
          case tm1_tm2 of
            (Var v1, Var v2) =>
            (case Name.compare (v1,v2) of
               LESS => LESS
             | EQUAL => cmp tms1 tms2
             | GREATER => GREATER)
          | (Var _, _) => LESS
          | (_, Var _) => GREATER
          | (Rat r1, Rat r2) =>
            (case Rat.compare (r1,r2) of
               LESS => LESS
             | EQUAL => cmp tms1 tms2
             | GREATER => GREATER)
          | (Rat _, _) => LESS
          | (_, Rat _) => GREATER
          | (Fn (f1,a1), Fn (f2,a2)) =>
            (case Name.compare (f1,f2) of
               LESS => LESS
             | EQUAL =>
               (case Int.compare (length a1, length a2) of
                  LESS => LESS
                | EQUAL => cmp (a1 @ tms1) (a2 @ tms2)
                | GREATER => GREATER)
             | GREATER => GREATER)
      end
    | cmp _ _ = raise Bug "Term.compare";
in
  fun compare (tm1,tm2) = cmp [tm1] [tm2];
end;

fun equal tm1 tm2 = compare (tm1,tm2) = EQUAL;

(* ------------------------------------------------------------------------- *)
(* Subterms.                                                                 *)
(* ------------------------------------------------------------------------- *)

type path = int list;

fun subterm tm [] = tm
  | subterm (Var _) (_ :: _) = raise Error "Term.subterm: Var"
  | subterm (Rat _) (_ :: _) = raise Error "Term.subterm: Rat"
  | subterm (Fn (_,tms)) (h :: t) =
    if h >= length tms then raise Error "Term.replace: Fn"
    else subterm (List.nth (tms,h)) t;

local
  fun subtms [] acc = acc
    | subtms ((path,tm) :: rest) acc =
      let
        fun f (n,arg) = (n :: path, arg)

        val acc = (rev path, tm) :: acc
      in
        case tm of
          Fn (_,args) => subtms (map f (enumerate args) @ rest) acc
        | _ => subtms rest acc
      end;
in
  fun subterms tm = subtms [([],tm)] [];
end;

fun replace tm ([],res) = if equal res tm then tm else res
  | replace tm (h :: t, res) =
    case tm of
      Var _ => raise Error "Term.replace: Var"
    | Rat _ => raise Error "Term.replace: Rat"
    | Fn (func,tms) =>
      if h >= length tms then raise Error "Term.replace: Fn"
      else
        let
          val arg = List.nth (tms,h)
          val arg' = replace arg (t,res)
        in
          if Portable.pointerEqual (arg',arg) then tm
          else Fn (func, updateNth (h,arg') tms)
        end;

fun find pred =
    let
      fun search [] = NONE
        | search ((path,tm) :: rest) =
          if pred tm then SOME (rev path)
          else
            case tm of
              Fn (_,a) =>
              let
                val subtms = map (fn (i,t) => (i :: path, t)) (enumerate a)
              in
                search (subtms @ rest)
              end
            | _ => search rest
    in
      fn tm => search [([],tm)]
    end;

val ppPath = Print.ppList Print.ppInt;

val pathToString = Print.toString ppPath;

(* ------------------------------------------------------------------------- *)
(* Free variables.                                                           *)
(* ------------------------------------------------------------------------- *)

local
  fun free _ [] = false
    | free v (Var w :: tms) = Name.equal v w orelse free v tms
    | free v (Rat _ :: tms) = free v tms
    | free v (Fn (_,args) :: tms) = free v (args @ tms);
in
  fun freeIn v tm = free v [tm];
end;

local
  fun free vs [] = vs
    | free vs (Var v :: tms) = free (NameSet.add vs v) tms
    | free vs (Rat _ :: tms) = free vs tms
    | free vs (Fn (_,args) :: tms) = free vs (args @ tms);
in
  val freeVarsList = free NameSet.empty;

  fun freeVars tm = freeVarsList [tm];
end;

local
  fun free vs [] = vs
    | free vs (Var _ :: tms) = free vs tms
    | free vs (Rat _ :: tms) = free vs tms
    | free vs (Fn (v,[]) :: tms) = free (NameSet.add vs v) tms
    | free vs (Fn (_,args) :: tms) = free vs (args @ tms);
in
  val freeSkosList = free NameSet.empty;

  fun freeSkos tm = freeSkosList [tm];
end;

(* ------------------------------------------------------------------------- *)
(* Fresh variables.                                                          *)
(* ------------------------------------------------------------------------- *)

fun newVar () = Var (Name.newName ());

fun newVars n = map Var (Name.newNames n);

local
  fun avoidAcceptable avoid n = not (NameSet.member n avoid);
in
  fun variantPrime avoid = Name.variantPrime (avoidAcceptable avoid);

  fun variantNum avoid = Name.variantNum (avoidAcceptable avoid);
end;

(* ------------------------------------------------------------------------- *)
(* Special support for terms with type annotations.                          *)
(* ------------------------------------------------------------------------- *)

val hasTypeFunctionName = Name.fromString ":";

val hasTypeFunction = (hasTypeFunctionName,2);

fun destFnHasType ((f,a) : functionName * term list) =
    if not (Name.equal f hasTypeFunctionName) then
      raise Error "Term.destFnHasType"
    else
      case a of
        [tm,ty] => (tm,ty)
      | _ => raise Error "Term.destFnHasType";

val isFnHasType = can destFnHasType;

fun isTypedVar tm =
    case tm of
      Var _ => true
    | Rat _ => false
    | Fn func =>
      case total destFnHasType func of
        SOME (Var _, _) => true
      | _ => false;

(*LCP: We ignore algebraic operators and constants when computing weights;
  the number of distinct variables is more important than repetitions of variables.
  Much is arbitrary in the settings of these parameters. They have been determined empirically,
  but their effects on different problems vary widely.*)
(*
local
  fun sz n vs [] = n
    | sz n vs (Var v :: tms) =
        if List.exists (Name.equal v) vs then sz (n+10) vs tms
        else sz (n+450) (v::vs) tms
    | sz n vs (Rat _ :: tms) = sz (n+1) vs tms
    | sz n vs (Fn (_,[]) :: tms) = sz n vs tms
    | sz n vs (Fn (f,args) :: tms) =
        case f of
            "+"        => sz (n+7) vs (args @ tms)
          | "-"        => sz (n+7) vs (args @ tms)
          | "*"        => sz (n+12) vs (args @ tms)
          | "^"        => sz (n+7) vs (args @ tms)
          | "/"        => sz (n+25) vs (args @ tms)
          | "abs"      => sz (n+450) vs (args @ tms)
          | _          => sz (n+100) vs (args @ tms)
          in
  fun typedSymbols tm = sz 0 [] [tm];
          end;
*)
(* Depth aware version - JPB 25.5.11 *)
(* Modified 31.5.11 to restrict increase in weighting to only the arguments of "*" that are also special functions *)
val DEPTH_TOP_LEVEL = 1;
val DEPTH_FACTOR = 1; (* 0 means no extra depth weight *)
val DEPTH_DIVISOR = 1;
local
  fun sz depth nTotal n vs [] [] = nTotal + n
    | sz depth nTotal n vs [] lower_level = sz (depth+DEPTH_FACTOR) (nTotal+n) 0 vs lower_level []
    | sz depth nTotal n vs (Var v :: tms) lower_level =
        if List.exists (Name.equal v) vs then sz depth nTotal (n+10) vs tms lower_level
        else sz depth nTotal (n+450) (v::vs) tms lower_level
    | sz depth nTotal n vs (Rat _ :: tms) lower_level = sz depth nTotal (n+1) vs tms lower_level
    | sz depth nTotal n vs (Fn (_,[]) :: tms) lower_level = sz depth nTotal n vs tms lower_level
    | sz depth nTotal n vs (Fn (f,args) :: tms) lower_level=
        case f of
            "+"        => sz depth nTotal (n+7) vs (args @ tms) (lower_level)
          | "-"        => sz depth nTotal (n+7) vs (args @ tms) (lower_level)
          | "*"        => sz depth nTotal (n+12) vs  tms (args @ lower_level)
          | "^"        => sz depth nTotal (n+7) vs ((tl args) @ tms) ((hd args) :: lower_level)
          | "/"        => sz depth nTotal (n+25) vs (args @ tms) (lower_level)
          | "floor"      => sz depth nTotal (n+250) vs (args @ tms) (lower_level)  (*A guess, needs to be determined by testing*)
          | "abs"      => sz depth nTotal (n+450) vs (args @ tms) (lower_level)
          | _          => sz depth nTotal (n+100*depth) vs (args @ tms) (lower_level)
in
  fun typedSymbols tm = (sz DEPTH_TOP_LEVEL 0 0 [] [tm] []) div DEPTH_DIVISOR;
end;

local
  fun subtms [] acc = acc
    | subtms ((_, Var _) :: rest) acc = subtms rest acc
    | subtms ((_, Rat _) :: rest) acc = subtms rest acc
    | subtms ((_, Fn (":", [Var _, _])) :: rest) acc = subtms rest acc
    | subtms ((path, tm as Fn func) :: rest) acc =
             let
            fun f (n,arg) = (n :: path, arg)

            val (_,args) = func

            val acc = (rev path, tm) :: acc

            val rest = map f (enumerate args) @ rest
          in
            subtms rest acc
          end;
in
  fun nonVarTypedSubterms tm = subtms [([],tm)] [];
end;

(* ------------------------------------------------------------------------- *)
(* Special support for terms with an explicit function application operator. *)
(* ------------------------------------------------------------------------- *)

val appName = Name.fromString ".";

fun mkFnApp (fTm,aTm) = (appName, [fTm,aTm]);

fun mkApp f_a = Fn (mkFnApp f_a);

fun destFnApp ((f,a) : Name.name * term list) =
    if not (Name.equal f appName) then raise Error "Term.destFnApp"
    else
      case a of
        [fTm,aTm] => (fTm,aTm)
      | _ => raise Error "Term.destFnApp";

val isFnApp = can destFnApp;

fun destApp tm =
    case tm of Fn func => destFnApp func
      | _ => raise Error "Term.destApp";

val isApp = can destApp;

fun listMkApp (f,l) = foldl mkApp f l;

local
  fun strip tms tm =
      case total destApp tm of
        SOME (f,a) => strip (a :: tms) f
      | NONE => (tm,tms);
in
  fun stripApp tm = strip [] tm;
end;

(* ------------------------------------------------------------------------- *)
(* Parsing and pretty printing.                                              *)
(* ------------------------------------------------------------------------- *)

(* Operators parsed and printed infix *)

(*This table is used in the printing of terms and formulas.*)
val infixes = Print.Infixes
  [{token = " ^ ", precedence = 8, leftAssoc = false},
   {token = " / ", precedence = 7, leftAssoc = true},
   {token = " * ", precedence = 7, leftAssoc = true},
   {token = " + ", precedence = 6, leftAssoc = true},
   {token = " - ", precedence = 6, leftAssoc = true},
   {token = " = ", precedence = 4, leftAssoc = true},
   {token = " <= ", precedence = 4, leftAssoc = true},
   {token = " | ", precedence = ~2, leftAssoc = false}];

(* The negation symbol *)

val negation : string ref = ref "~";

(* Binder symbols *)

val binders : string list ref = ref ["\\","!","?","?!"];

(* Bracket symbols *)

val brackets : (string * string) list ref = ref [("[","]"),("{","}")];

(* Pretty printing *)

fun pp inputTerm =
    let
      val quants = !binders
        and iOps = infixes
      and neg = !negation

      val iTokens = Print.tokensInfixes iOps

      fun destI tm =
          case tm of
            Fn (f,[a,b]) =>
              if StringSet.member f iTokens then SOME (f,a,b) else NONE
          | _ => NONE

      val iPrinter = Print.ppInfixes iOps destI

      val specialTokens =
          StringSet.addList iTokens (neg :: quants @ ["$","(",")"])

      fun isI tm = Option.isSome (destI tm)

      fun stripNeg tm =
          case tm of
            Fn (f,[a]) =>
            if Name.toString f <> neg then (0,tm)
            else let val (n,tm) = stripNeg a in (n + 1, tm) end
          | _ => (0,tm)

      val destQuant =
          let
            fun dest q (Fn (q', [Var v, body])) =
                if Name.toString q' <> q then NONE
                else
                  (case dest q body of
                     NONE => SOME (q,v,[],body)
                   | SOME (_,v',vs,body) => SOME (q, v, v' :: vs, body))
              | dest _ _ = NONE
          in
            fn tm => Useful.first (fn q => dest q tm) quants
          end

      fun isQuant tm = Option.isSome (destQuant tm)

      and basic bv (Var v) = Print.ppString v
        | basic bv (Rat r) = Print.ppString (Rat.toString r)
        | basic bv (Fn (f,[])) = Print.ppString f
        | basic bv (Fn (f,args)) =
          Print.blockProgram Print.Inconsistent 2
            [Print.ppString f, Print.ppBracket "(" ")" (Print.ppOpList "," (term bv)) args]

      and innerQuant bv tm =
          case destQuant tm of
            NONE => term bv tm
          | SOME (q,v,vs,tm) =>
            let
              val bv = StringSet.addList bv (map Name.toString (v :: vs))
            in
              Print.program
                [Print.addString q,
                 Print.addString v,
                 Print.program
                   (map (Print.sequence (Print.addBreak 1) o Print.addString) vs),
                 Print.addString ".",
                 Print.addBreak 1,
                 innerQuant bv tm]
            end

      and quantifier bv tm =
          if not (isQuant tm) then basic bv tm
          else Print.block Print.Inconsistent 2 (innerQuant bv tm)

      and molecule bv (tm,r) =
          let
            val (n,tm) = stripNeg tm
          in
            Print.blockProgram Print.Inconsistent n
              [Print.duplicate n (Print.addString neg),
               if isI tm orelse (r andalso isQuant tm) then bracket bv tm
               else quantifier bv tm]
          end

      and term bv tm = iPrinter (molecule bv) (tm,false)

      and bracket bv tm = Print.ppBracket "(" ")" (term bv) tm
    in
      term StringSet.empty
    end inputTerm;

val toString = Print.toString pp;

(* ------------------------------------------------------------------------- *)
(* Hashing.                                                                  *)
(* ------------------------------------------------------------------------- *)

fun hashw (Var v, w) = Polyhash.hashw_string (v,w)
  | hashw (Rat r, w) = Rat.hashw (r,w)
  | hashw (Fn (f,args), w) = Polyhash.hashw_string (f, (hashwList (args, w)))
and hashwList ([], w) = w
  | hashwList (t::ts, w) = hashw (t, (hashwList (ts, w)));

(* ------------------------------------------------------------------------- *)
(* Numeric evaluation, also known as constant folding.                       *)
(* ------------------------------------------------------------------------- *)

fun metisRat1 f (Rat r) = Rat (f r)
  | metisRat1 _ _ = raise Option

fun metisRat2 f (Rat r1) (Rat r2) = Rat (f (r1,r2))
  | metisRat2 _ _ _ = raise Option

fun numeric_eval_apply "*" [x,y] = metisRat2 Rat.mult x y
  | numeric_eval_apply "/" [x,y] = metisRat2 Rat.mult x (metisRat1 Rat.inv y)
  | numeric_eval_apply "+" [x,y] = metisRat2 Rat.add x y
  | numeric_eval_apply "-" [x,y] = metisRat2 Rat.add x (metisRat1 Rat.neg y)
  | numeric_eval_apply "^" [x,y] = metisRat2 Rat.exp x y
  | numeric_eval_apply "-" [x] = metisRat1 Rat.neg x
  | numeric_eval_apply _ _ = raise Option;

fun eval_Fn (fname, args) =
  numeric_eval_apply fname args
  handle Option      => Fn (fname, args);

(* Parsing *)

(*This special-purpose parser is necessary because the standard handling of infixes doesn't
  let us assign the correct precedence unary minus. We get either -x^2 = (-x)^2 or
  -a-b = -(a-b)! *)
local
  open Parse;

  infixr 9 >>++
  infixr 8 ++
  infixr 7 >>
  infixr 6 ||
in
  fun iparser toStr basic =
    let fun sym ss = some (fn tok => mem (toStr tok) ss)
        fun leftify (u,[]) = u
          | leftify (u, (a,t)::ts) = leftify(eval_Fn(toStr a, [u,t]), ts)
        fun factor input =
             (sym["-"] ++ factor >> (fn (_,t) => Fn("-",[t])) ||
              basic ++ optional (sym["^"] ++ factor)
              >> (fn (t1, SOME(_,t2)) => Fn("^",[t1,t2]) | (t1, NONE) => t1)
             ) input
        and trm input =
             (factor ++ many (sym["*","/"] ++ factor) >> leftify
             ) input
        and exp input =
             (trm ++ many (sym["+","-"] ++ trm) >> leftify
             ) input
    in  exp  end;
end

local
  open Parse;

  infixr 9 >>++
  infixr 8 ++
  infixr 7 >>
  infixr 6 ||

  val isAlphaNum =
      let
        val alphaNumChars = explode "_'"
      in
        fn c => mem c alphaNumChars orelse Char.isAlphaNum c
      end;

  local
    val alphaNumToken = atLeastOne (some isAlphaNum) >> implode;

    val symbolToken =
        let
          val symbolChars = explode "<>=-*+/\\?@|!$%&#^:;~"

          fun isSymbol c = mem c symbolChars
        in
          some isSymbol >> str
        end;

    val punctToken =
        let
          val punctChars = explode "()[]{}.,"

          fun isPunct c = mem c punctChars
        in
          some isPunct >> str
        end;

    val lexToken = alphaNumToken || symbolToken || punctToken;

    val space = many (some Char.isSpace);
  in
    val lexer = (space ++ lexToken ++ space) >> (fn (_,(tok,_)) => tok);
  end;

  fun termParser inputStream =
      let
        val quants = !binders
        and iOps = infixes
        and neg = "-"  (*LCP*)
        and bracks = ("(",")") :: !brackets

        val bracks = map (fn (b1,b2) => (b1 ^ b2, b1, b2)) bracks

        val bTokens = map #2 bracks @ map #3 bracks

        fun possibleVarName "" = false
          | possibleVarName s = isAlphaNum (String.sub (s,0))

        fun vName bv s = StringSet.member s bv

        val iTokens = Print.tokensInfixes iOps

        val specialTokens =
            StringSet.addList iTokens (neg :: quants @ ["$"] @ bTokens)

        fun varName bv =
            some (vName bv) ||
            (some (Useful.equal "$") ++ some possibleVarName) >> snd

        fun fName bv s =
            not (StringSet.member s specialTokens) andalso not (vName bv s)

        fun functionName bv =
            some (fName bv) ||
            (some (Useful.equal "(") ++ any ++ some (Useful.equal ")")) >>
            (fn (_,(s,_)) => s)

        fun basic bv tokens =
            let
              val var = varName bv >> (Var o Name.fromString)

              val const = (*parse a rational or a constant*)
                  functionName bv >>
                   (fn f => Rat (Rat.rat_of_intinf (Option.valOf (IntInf.fromString f)))
                        handle Option => Fn (Name.fromString f, []))

              val unary_minus =
                  (some (Useful.equal "-") ++ basic bv) >> (fn (_,s) => Fn ("-", [s]))

              fun bracket (ab,a,b) =
                  (some (Useful.equal a) ++ term bv ++ some (Useful.equal b)) >>
                  (fn (_,(tm,_)) =>
                      if ab = "()" then tm else Fn (Name.fromString ab, [tm]))

              fun quantifier q =
                  let
                    fun bind (v,t) =
                        Fn (Name.fromString q, [Var (Name.fromString v), t])
                  in
                    (some (Useful.equal q) ++
                     atLeastOne (some possibleVarName) ++
                     some (Useful.equal ".")) >>++
                    (fn (_,(vs,_)) =>
                        term (StringSet.addList bv vs) >>
                        (fn body => foldr bind body vs))
                  end
            in
              var ||
              const ||
              unary_minus ||
              first (map bracket bracks) ||
              first (map quantifier quants)
            end tokens

        and term bv tokens = iparser (fn s=>s) (basic bv) tokens
      in
        term StringSet.empty
      end inputStream;
in
  fun fromString input =
      let
        val chars = Stream.fromList (explode input)

        val tokens = everything (lexer >> singleton) chars

        val terms = everything (termParser >> singleton) tokens
      in
        case Stream.toList terms of
          [tm] => tm
        | _ => raise Error "Term.fromString"
      end;
end;

local
  val antiquotedTermToString = Print.toString (Print.ppBracket "(" ")" pp);
in
  val parse = Parse.parseQuotation antiquotedTermToString fromString;
end;

end

structure TermOrdered =
struct type t = Term.term val compare = Term.compare end

structure TermMap = KeyMap (TermOrdered);

structure TermSet = ElementSet (TermMap);
