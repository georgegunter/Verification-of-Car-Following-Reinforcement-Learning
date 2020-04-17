(* ------------------------------------------------------- *)
(* SMTLIB.sml routines to read a subset of SMT-LIB v2      *)
(* suitable for MetiTarski Problems - JPB 9th October 2012 *)
(* ------------------------------------------------------- *)

(* NB Quoted symbols and Strings can both contain new line *)
(* characters which means that these tokens may be split   *)
(* across lines. This is a pain as files can't be dealt    *)
(* with on a line by line basis. But as problem files are  *)
(* small the easiest solution is to read the entire file   *)
(* into a char list.                                       *)


structure SMTLIB :> SMTLIB =

struct

exception Error of string (* normally contained in Useful but not using Useful *)


(* Tokens - numerical values are stored as ints or ratio of ints - these are *)
(* different from rats as they are not normalised which makes comparing with *)
(* the original string easier but can easily be converted to rats.           *)
datatype Token =
   Left_bracket
 | Right_bracket
 | Numeral           of IntInf.int
 | Decimal           of IntInf.int * IntInf.int
 | Binary            of IntInf.int
 | Hex               of IntInf.int
 | String_token      of string
 | Simple_symbol     of string
 | Quoted_symbol     of string
 | Keyword           of string
 | Command           of string (* Reserverd words (recognized commands) *)
 | Quantifier        of string (* Reserved word forall or exists *)
 | Unsupported       of string; (* Reserved Words not (yet?) supported *)

(* --------------------------------------------------- *)
(* function to express a rat as a decimal if possible  *)
(* this is useful for reconstructing numbers that were *)
(* decimals to begin with.                             *)
(* --------------------------------------------------- *)
fun dec_to_string (p,q) =
   if (p mod q) = 0 then (IntInf.toString (p div q)) else
   let
      fun next_pow_10 q e =
          if e >= q then e
          else next_pow_10 q (10*e)
      val e = next_pow_10 q 1
   in
      if (e mod q) = 0 then
        let
           val p = p*(e div q)
           val ipart = p div e
           val fpart = p mod e
           fun leading_zeros f e n =
               if f >= e then n else
                  leading_zeros (10*f) e (n+1)
           val n = leading_zeros (fpart*10) e 0
           (*
           val _ = print("p : "^(IntInf.toString p)^" q : "^(IntInf.toString q)
                        ^"\n ipart : "^(IntInf.toString ipart)^" fpart : "^(IntInf.toString fpart)
                        ^"\n e : "^(IntInf.toString e)^" n : "^(IntInf.toString n)^"\n")
           *)
           fun gen_zero_str n s = if n <= 0 then s
               else gen_zero_str (n-1) "0"^s
           val zero_string = gen_zero_str n ""
        in
           (IntInf.toString ipart)^"."^zero_string^(IntInf.toString fpart)
        end
      else
        ("(/ "^(IntInf.toString p)^" "^(IntInf.toString q)^")")
   end;


fun tokenToString token =
   case token of
     Left_bracket => "Left_bracket : ("
   | Right_bracket => "Right_bracket : )"
   | Numeral (i) => "Numeral : " ^ (IntInf.toString i)
   | Decimal (p,q) => "Decimal : " ^ (dec_to_string (p,q))
   | Binary (ib) =>  "Binary : " ^ (IntInf.fmt StringCvt.BIN ib)
   | Hex (ih) => "Hex : " ^ (IntInf.fmt StringCvt.HEX ih)
   | String_token (s) => "String_token : " ^ s
   | Simple_symbol (s) => "Simple_symbol : " ^ s
   | Quoted_symbol (s) => "Quoted_symbol : " ^ s
   | Keyword (s) => "Keyword : " ^ s
   | Command (s) => "Command : " ^ s
   | Quantifier (s) => "Quantifier : " ^ s
   | Unsupported (s) => "Unsupported (reserved word) : " ^ s;

fun stringPartOfToken token =
   case token of
     Left_bracket  =>  "("
   | Right_bracket => ")"
   | Numeral (i) => (IntInf.toString i)
   | Decimal (p,q) =>(dec_to_string (p,q))
   | Binary (ib) =>  (IntInf.fmt StringCvt.BIN ib)
   | Hex (ih) => (IntInf.fmt StringCvt.HEX ih)
   | String_token (s) => s
   | Simple_symbol (s) => s
   | Quoted_symbol (s) => s
   | Keyword (s) => s
   | Command (s) => s
   | Quantifier (s) => s
   | Unsupported (s) => s;

(* NB S-expressions are token lists *)
fun tokenListToString token_list =
   let
     fun tsToStr [] s = s
      |  tsToStr (t::ts) s = tsToStr ts (s^" "^(stringPartOfToken t));
   in
     tsToStr token_list ""
   end;

fun seListToString se_list =
   let
      fun seToStr []  s = s^"\n;End of S-Expressions\n"
       |  seToStr (se::ses) s = seToStr ses (s^";\n------------------------------\n"^(tokenListToString se))
   in
      seToStr se_list "\n;List of S-Expressions\n"
   end;

fun functionsToString functions =
   let
      val fList = NameAritySet.toList functions
      fun f_to_str [] s = s^"\n------ End of Functions -----\n"
       |  f_to_str ((f,a)::rest) s = f_to_str rest (s ^ ("\n"^f^" of arity "^(Int.toString a)))
      val fstr = f_to_str fList "---- Declared functions with arities ----\n"
   in
      fstr
   end;


(* ----------------------------------------------------- *)
(* NB set-option is used for the includes of axiom files *)
(* i.e. (set-option includes (fname1 fname2 ....))       *)
(* ----------------------------------------------------- *)
val commands = 
["assert","declare-fun","set-option","exit","check-sat"]; (* NB these last two are supported by being ignored! *)

val quantifiers =
["forall","exists"];

val unsupported_Reserved_words =
["declare-sort","define-sort",
"define-fun","get-assertions",
"get-assignment","get-info","get-option",
"get-proof","get-unsat-core","get-value",
"pop","push","set-logic","set-info"];
 

fun inWordList _ [] = false
 |  inWordList wx (w::ws) = if (wx = w) then true
            else inWordList wx ws;

fun isCommand w = inWordList w commands;
fun isQuantifier w = inWordList w quantifiers;
fun isUnsupportedWord w = inWordList w unsupported_Reserved_words;

(* local function to convert a decimal list of characters to an unnormalised ratio of ints *)
(* as this is only called when a decimal has successfully been read, no error checking is  *)
(* carried out.                                                                            *)
fun strToRat dec =
  let
     fun split ((#".")::dec_part) int_part = (rev int_part,dec_part)
      |  split [] int_part = (rev int_part,[]) (* should work with ints as well as decimals *)
      |  split (d::ds) int_part = split ds (d::int_part)
     fun get_q 0 q = rev q
      |  get_q n q = get_q (n-1) (#"0"::q)
     val (ps,qs) = split dec []
     val q = get_q (List.length qs) [#"1"]
     val p = ps@qs
     val p = case IntInf.fromString (implode p) of SOME p => p | NONE => 0
     val q = case IntInf.fromString (implode q) of SOME q => q | NONE => 1
  in
     (p,q)
  end;
(* functions for hex and bin - probably can use library routines but quicker to rewrite *)
fun hexStrToInt hex =
let
  fun hexToInt [] i = i
   |  hexToInt (h::hs) i =
      let
         val d = case h of (#"0")=>0|(#"1")=>1|(#"2")=>2|(#"3")=>3|(#"4")=>4
                        |(#"5")=>5|(#"6")=>6|(#"7")=>7|(#"8")=>8|(#"9")=>9
                        |(#"A")=>10|(#"B")=>11|(#"C")=>12|(#"D")=>13|(#"E")=>14|(#"F")=>15
                        |(#"a")=>10|(#"b")=>11|(#"c")=>12|(#"d")=>13|(#"e")=>14|(#"f")=>15
                        |_=> raise Error " Error converting hex number "
         val i = 16*i + d
      in
         hexToInt hs i
      end
   in
      hexToInt hex (IntInf.fromInt 0)
   end;
fun binStrToInt bin =
let
  fun binToInt [] i = i
   |  binToInt (b::bs) i =
      let
         val d = case b of (#"0")=>0|(#"1")=>1
                    |_=> raise Error " Error converting hex number "
         val i = 2*i + d
      in
         binToInt bs i
      end
   in
      binToInt bin (IntInf.fromInt 0)
   end;

(* <<<<<<<<<<<<<<<<<<<<<<<<< TOKEN READING CODE >>>>>>>>>>>>>>>>>>>>>>>>> *)

(* function to skip over white space including comments *)
(* line should be a list of chars.                      *)
fun skipWhiteSpace line =
  let
     fun skipComment (#"\n"::cs) = cs
      |  skipComment (_::cs) = skipComment cs
      |  skipComment _ = raise Error "new line missing in comment\n"
     fun skipSpaceChars (#" "::cs) = skipSpaceChars cs
      |  skipSpaceChars (#"\t"::cs) = skipSpaceChars cs
      |  skipSpaceChars (#"\n"::cs) = skipSpaceChars cs
      |  skipSpaceChars (#"\r"::cs) = skipSpaceChars cs
      |  skipSpaceChars (#";"::cs) = skipSpaceChars (skipComment cs)
      |  skipSpaceChars cs = cs
   in
      skipSpaceChars line
   end;

(* function to recognize allowed Symbol characters *)
fun isSymbolChar #"~" = true
 |  isSymbolChar #"!" = true
 |  isSymbolChar #"@" = true
 |  isSymbolChar #"$" = true
 |  isSymbolChar #"%" = true
 |  isSymbolChar #"^" = true
 |  isSymbolChar #"&" = true
 |  isSymbolChar #"*" = true
 |  isSymbolChar #"_" = true
 |  isSymbolChar #"+" = true
 |  isSymbolChar #"=" = true
 |  isSymbolChar #"<" = true
 |  isSymbolChar #">" = true
 |  isSymbolChar #"." = true
 |  isSymbolChar #"?" = true
 |  isSymbolChar #"/" = true
 |  isSymbolChar #"-" = true
 |  isSymbolChar c = Char.isAlphaNum c;

(* ------------------------------------------- *)
(* function to read all tokens in line         *)
(* line should be a list of characters         *)
(* NB the tokens are returned in reverse order *)
(* this allows lines to be read sequentially   *)
(* without the need for appending. The whole   *)
(* token list can then be reversed at the end. *)
(* ------------------------------------------- *)
fun readTokensFromCharList [] token_list = token_list
 |  readTokensFromCharList line token_list =
   let
       (* NB in completeString I've not allowed \n and \r as they are
            not in the standard but note that they are in the tutorial?? *)
       fun completeString ((#"\"")::cs) t = (((#"\"")::t),cs)
        |  completeString ((#"\\")::(#"\"")::cs) t = completeString cs ((#"\"")::(#"\\")::t)
        |  completeString ((#"\\")::(#"\\")::cs) t = completeString cs ((#"\\")::(#"\\")::t)
        |  completeString (c::cs) t =
           if (Char.isPrint c orelse c = #"\n" orelse c = #"\r" orelse c = #"\t")
              then completeString cs (c::t)
           else
              raise Error ("badly formed String : " ^ (implode(rev(t))))
        |  completeString _ t = raise Error ("incomplete String : " ^ (implode(rev(t))))
       (* completeNumeral is used both for numerals (ints) and
          the fractional part of decimals *)
       fun completeNumeral [] t = (t,[])
        |  completeNumeral (c::cs) t =
           if (Char.isDigit c) then completeNumeral cs (c::t) else (t,c::cs)
       fun completeBinary (#"0"::cs) t  = completeBinary cs (#"0"::t)
        |  completeBinary (#"1"::cs) t  = completeBinary cs (#"1"::t)
        |  completeBinary cs t = (t,cs)        
       fun completeHex (c::cs) t =
           if (Char.isHexDigit c) then completeHex cs (c::t) else (t,c::cs)
        |  completeHex [] t = (t,[])
       fun completeSymbol (c::cs) t =
           if (isSymbolChar c) then completeSymbol cs (c::t) else (t,c::cs)
        |  completeSymbol [] t = (t,[])
       fun completeQuotedSymbol (#"|"::cs) t = ((#"|"::t),cs)
        |  completeQuotedSymbol (#"\\"::cs) t =
           raise Error ("badly formed Quoted Symbol containing \"\\\" : "
                     ^ (implode(rev(t)))^"**ERROR**"^implode(cs))
        |  completeQuotedSymbol (c::cs) t =
           if (Char.isPrint c orelse c = #"\n" orelse c = #"\r" orelse c = #"\t")
               then completeQuotedSymbol cs (c::t)
           else raise Error ("badly formed Quoted Symbol : "
                             ^ (implode(rev(t))))
        |  completeQuotedSymbol [] t =
                raise Error ("incomplete Quoted Symbol : " ^ (implode(rev(t))))

       fun readToken (#"("::cs) = (SOME (Left_bracket),cs)
        |  readToken (#")"::cs) = (SOME (Right_bracket),cs)
        |  readToken (#"\""::cs) = 
               let
                    val (t,cs) = completeString cs [#"\""]
               in
                    (SOME (String_token(implode(rev t))),cs)
               end
        | readToken (#"#"::(#"x")::cs) =
               let
                    (* val (t,cs) = completeHex cs (#"x"::[(#"#")]) *)
                    val (t,cs) = completeHex cs []
               in
                    (SOME (Hex(hexStrToInt(rev t))),cs)
               end
        | readToken (#"#"::(#"b")::cs) =
               let
                    (*val (t,cs) = completeBinary cs (#"b"::[#"#"])*)
                    val (t,cs) = completeBinary cs []
               in
                    (SOME (Binary(binStrToInt(rev t))),cs)
               end
         | readToken (#":"::cs) =
               let
                    val (t,cs) = completeSymbol cs [#":"]
               in
                    (SOME (Keyword(implode(rev t))),cs)
               end
         | readToken (#"|"::cs) =
               let
                    val (t,cs) = completeQuotedSymbol cs [#"|"]
               in
                    (SOME (Quoted_symbol(implode(rev t))),cs)
               end
          (* with numbers 0 is either the start of a decimal or a
             stand-alone integer, other integers cannot have a leading 0 *)
         | readToken (#"0"::(#".")::cs) =
               let
                   val (t,cs) = completeNumeral cs (#"."::[#"0"])
               in
                   (SOME (Decimal(strToRat(rev t))),cs)
               end
         | readToken (#"0"::cs) = (SOME (Numeral(0)),cs)
         | readToken (c::cs) =
               if (Char.isDigit c) then
                   let
                       val (t,cs) = completeNumeral cs [c]
                       val c = if null cs then #" " else hd cs
                       val (t,cs) = if c = (#".") then
                                    completeNumeral (tl cs) (#"."::t)
                                    else
                                        (t,cs)
                   in
                     if c = (#".") then
                       (SOME (Decimal(strToRat(rev t))),cs)
                     else
                       (SOME (Numeral(Option.valOf (IntInf.fromString(implode(rev t))))),cs)
                   end
               else if (isSymbolChar c) then (* c is not a Num therefore this should be a symbol *)
                   let
                      val (t,cs) = completeSymbol cs [c]
                      val tok = implode(rev t)
                   in
                      if isCommand tok then
                         (SOME (Command(tok)),cs)
                      else if isQuantifier tok then
                         (SOME (Quantifier(tok)),cs)
                      else if isUnsupportedWord tok then
                         (SOME (Unsupported(tok)),cs)
                      else
                         (SOME (Simple_symbol(tok)),cs)
                   end
               else
                   raise Error ("Unrecognized Token type : "^(implode(c::cs)))
         | readToken [] = (NONE,[])
       val cs = skipWhiteSpace line
       val (tok_option,cs) = readToken cs
       val cs = skipWhiteSpace cs
   in
       case tok_option of NONE =>
           readTokensFromCharList cs (token_list)
         | SOME tok =>
           readTokensFromCharList cs (tok::token_list)
   end;

   (* Function to read all chars in a file *)
   fun readAllChars file_stream char_stack =
      let
          fun add_chars_to_stack [] stack = stack
           |  add_chars_to_stack (c::cs) stack =
                  add_chars_to_stack cs (c::stack)
      in         
         case (TextIO.inputLine file_stream) of
            NONE => rev char_stack
          | SOME line =>
               readAllChars file_stream (add_chars_to_stack (explode line) char_stack)
      end;

   (* Function to read all tokens in a file *)
   fun readTokens file_name =
      let
         val fin =  TextIO.openIn file_name
         val charList = readAllChars fin []
         val _ = TextIO.closeIn fin
         val token_stack = readTokensFromCharList charList []
      in
         rev token_stack
      end;

   (* Debug function to write out tokens to a file *)
   fun writeTokens file_name token_list = 
      let
         val fout = TextIO.openOut file_name
         fun outputTokens file_stream [] =
                  TextIO.output (file_stream,"----------- End Of Tokens -----------\n")
          |  outputTokens file_stream (token::tokens) =
                let
                  val _ = TextIO.output (file_stream,((tokenToString token) ^ "\n"))
                in
                  outputTokens file_stream tokens
                end
         val _ = outputTokens fout token_list
     in
       TextIO.closeOut fout
     end;

     fun testTokenReading fin fout =
       let
          val token_list = readTokens fin
       in
          writeTokens fout token_list
       end;
         
(* <<<<<<<<<<<<<<<<<<<<<<<<< END OF TOKEN READING CODE >>>>>>>>>>>>>>>>>>>>>>>>> *)

(* <<<<<<<<<<<<<<<<<<<<<<<<< S-EXPRESSION CODE >>>>>>>>>>>>>>>>>>>>>>>> *)

(* ---------------------------------------------------------------------------------- *)
(* Function to get the next S-expression, this may itself contain other S-expressions *)
(* simple bracket matching is used so if a bracket is missing an error will be raised *)
(* S-expressions are lists of tokens including the outer parenthasis.                 *)
(* ---------------------------------------------------------------------------------- *)


  fun getSExpression ((t as Left_bracket)::ts) =
    let
         fun addToken ts s 0 = (SOME (rev s),ts)
          |  addToken [] s _ = raise Error ("right bracket missing in \n"
                                           ^ (tokenListToString (rev s)))
          |  addToken ((t as Left_bracket)::ts) s bc = addToken ts (t::s) (bc+1)
          |  addToken ((t as Right_bracket)::ts) s bc = addToken ts (t::s) (bc-1)
          |  addToken (t::ts) s bc = addToken ts (t::s) bc
       in
          addToken ts [t] 1
       end
   |  getSExpression (t::ts) = (SOME [t],ts)
   |  getSExpression _ = (NONE,[]);

  (* Debug function to write out S-expressions *)
  fun writeSExpressions token_list fout =
    let
        val fs = TextIO.openOut fout
        fun writeSE file_stream [] = TextIO.closeOut file_stream
         |  writeSE file_stream token_list =
               let
                  val (se_o,ts) = getSExpression token_list
                  val _ = case se_o of SOME se =>TextIO.output (file_stream,("S-Expression : \n"
                                                          ^(tokenListToString se)^"\n"))
                           | NONE => raise Error ("Error trying to read S-expression from \n"
                                                        ^(tokenListToString token_list)^"\n")
               in
                  writeSE file_stream ts
               end
    in
        writeSE fs token_list
    end;

    fun testSExpressions fin fout =
        let
           val token_list = readTokens fin
        in
           writeSExpressions token_list fout
        end;

(* -------------------------------------------------------------------------------------------------- *)      
(* functions to deal with the various types of top level S-expressions such as declare-fun and assert *)
(* -------------------------------------------------------------------------------------------------- *)
    (* --------------------------------------------------------- *)
    (* NB removeBrackets removes only the outer pair of brackets *)
    (* originally it recursively removed outer pairs but this    *)
    (* messes up things like variable S-expressions of the form  *)
    (* ((x Real)(y Real)) which becomes x Real)(y Real if 2 outer*)
    (* brackets are removed!                                     *)
    (* --------------------------------------------------------- *)
    fun removeBrackets (Left_bracket::ts) =
             (case (rev ts) of (Right_bracket::s) => (rev s)
                       |  ts => (Left_bracket::(rev ts)))
     |  removeBrackets ts = ts;

    fun isRealSort (Simple_symbol("Real")) = true
     |  isRealSort _ = false;

    fun isIntSort (Simple_symbol("Int")) = true
     |  isIntSort _ = false;

    fun isRatSort (Simple_symbol("Rat")) = true
     |  isRatSort _ = false;

    fun tokenListToSEList ts =
       let
          fun getSE [] se_list = rev se_list
           |  getSE ts se_list =
                 let
                     val (se_o,ts) = getSExpression ts
                 in
                     case se_o of SOME se => getSE ts (se::se_list)
                                | NONE => getSE ts se_list
                 end
       in
          getSE ts []
       end;
           
    (* function to convert a sorted_variable S-Expression into a (Real) variable name *)
    (* extended to also recognize types Int and Rat returning appropriate relations   *)
    fun sorted_variable_SE_to_variable_name ts =
      let
         val error_message = "error converting " ^
                             (tokenListToString ts) ^
                             " to (Real)Sorted Variable\n"
         val reserved_error = " Reserved word used as variable name "
         val sort_error = " Variables must be of sort/type Real, Int or Rat "
         val (var_o,ts) = getSExpression (removeBrackets ts)
         val var = case var_o of SOME v => (removeBrackets v)
                               | NONE => raise Error error_message
         val var = if (List.length var) = 1 then hd var
                   else raise Error error_message
         val var = case var of Simple_symbol(v) => v
                             | Command(_) => raise Error (reserved_error^error_message)
                             | Quantifier(_) => raise Error (reserved_error^error_message)
                             | Unsupported(_) => raise Error (reserved_error^error_message)
                             | _ => raise Error error_message
         val (sort_o,_) = getSExpression (removeBrackets ts)
         val sort = case sort_o of SOME s => (removeBrackets s)
                                 | NONE => raise Error error_message
         val sort = if (List.length sort) = 1 then hd sort
                    else raise Error (sort_error^error_message)
         val sort_option = if isRealSort sort then NONE
                    else if isRatSort sort then SOME (Formula.Atom ("$rat",[Term.Var (var)]))
                    else if isIntSort sort then SOME (Formula.Atom ("$int",[Term.Var (var)]))
                    else raise Error (sort_error^error_message)
      in
         (var,sort_option)
      end;

    (* -------------------------------------------------------------------------------- *)
    (* function to convert an S-Expression to a term (NB both may be tree structures)   *)
    (* NB in SMTLIB all symbols should be pre-declared either as functions (constants   *)
    (*    being zero arity functions) or as variables from forall or exists quantifiers *)
    (*    numerical constants are also permitted. Variables are stored in a NameSet and *)
    (*    functions are stored in a NameAritySet.                                       *)
    (* -------------------------------------------------------------------------------- *)
    fun term_from_SE se functions variables =
       let
          val ts = removeBrackets se
          val error_message = " Error in SE term : "^(tokenListToString ts)
          val unknown_variable = " Unknown variable or function/constant "
          val (se_o,ts) = getSExpression ts
          val se = case se_o of SOME s => (removeBrackets s)
                              | NONE => raise Error error_message
          val t = if(List.length se)=1 then hd se else raise Error error_message
          val term = case t of
                        Numeral(n) => Term.Rat (Rat.rat_of_intinf n)
                       |Decimal(p,q) => Term.Rat (Rat.rat_of_quotient (p,q))
                       |Binary(n) => Term.Rat (Rat.rat_of_intinf n)
                       |Hex(n) => Term.Rat (Rat.rat_of_intinf n)
                       |Simple_symbol(n) =>
                          if(NameSet.member n variables) then Term.Var (n)
                          else 
                            let
                               val ses = tokenListToSEList ts
                               val arity = List.length ses
                            in
                               if (NameAritySet.member (n,arity) functions) then
                                let
                                  (* recursive bit to get subterms from sub SExpressions *)
                                  fun  f s = term_from_SE s functions variables
                                  val term_list = map f ses
                                in
                                  Term.Fn (n,term_list)
                                end
                              else
                                raise Error (unknown_variable ^ error_message)
                           end
                       | _ => raise Error error_message
       in
           term
       end;

   (* function to convert inequalities to be <= *)
   fun normalise_atomic_relations (f as Formula.Atom(relation,term_list)) =
       let
          fun swap_terms ([a,b]) = [b,a]
           |  swap_terms _ = raise Error "error in term_list in SMTLIB.normalise_atomic_relations\n"
          fun negate (Formula.Not (f)) = f
           |  negate f = Formula.Not(f)
       in
          case relation of
                "<" =>
              let
                  val a = Formula.Atom("<=",(swap_terms term_list))
              in
                  negate a
              end
              | ">" =>
              let
                  val a = Formula.Atom("<=",term_list)
              in
                  negate a
              end
              | ">=" => Formula.Atom("<=",(swap_terms term_list))
              | _ => f

        end
      | normalise_atomic_relations f = f;        
   
   (* ------------------------------------------------- *)
   (* function to convert an S-Expression to an Atom    *)
   (* the first symbol of the S-Expression is assumed   *)
   (* to be a relation, the remaining sub-S-Expressions *)
   (* are taken to be terms.                            *)
   (* ------------------------------------------------- *)
   fun atom_from_SE se functions variables =
      let
         val ts = removeBrackets se
         val error_message = " Error in SE atom : "^(tokenListToString ts)
         val name_error = " relation name error, "^error_message
         (* the first sub SE should be a symbol giving the name of the relation *)
         val (se_o,ts) = getSExpression ts
         val se = case se_o of SOME s => (removeBrackets s)
                             | NONE => raise Error error_message
         val relation = if (List.length se) = 1 then
                            let
                               val t = hd se
                            in
                               case t of Simple_symbol(n) => n
                                       | _ => raise Error name_error
                            end
                        else
                            raise Error name_error
         (* the rest of the original SE should be the terms in *)
         (* the relation.                                      *)
         val ses = tokenListToSEList ts
         fun f s = term_from_SE s functions variables
         val term_list = map f ses
      in
         normalise_atomic_relations (Formula.Atom(relation,term_list))
      end;

              
                     
   (* --------------------------------------------------------------- *)
   (* NB in quantified formulas there should be two sub S-Expressions *)
   (* the first is the quantifier with associated variables and the   *)
   (* second is the experssion.                                       *)
   (* --------------------------------------------------------------- *)


   fun formula_from_SE se functions variables =
      let
         val ts = removeBrackets se
         val error_message = " Error in SE formula : "^(tokenListToString ts)
         (* check for true or false as special cases *)
      in
         if(List.length ts)=1 then case (hd ts) of
                                        Simple_symbol("true") => Formula.True
                                     |  Simple_symbol("false") => Formula.False
                                     | _ => raise Error error_message
         else
             let 
                 val ses = tokenListToSEList ts
                 val _ = if null ses then raise Error error_message else ()
                 val sub_se = removeBrackets (hd ses)
                 val args = tl ses
                 val q_or_lc = if null sub_se then raise Error error_message else hd sub_se
             in
                 case q_or_lc of Quantifier(q) =>
                              let
                                 val vars_sorts = map sorted_variable_SE_to_variable_name (tokenListToSEList(removeBrackets (hd args)))
                                 fun split [] vs fs = (rev vs,rev fs)
                                  |  split ((v,s_o)::rest) vs fs =
                                        case s_o of SOME f => split rest (v::vs) (f::fs)
                                                 |  NONE => split rest (v::vs) fs
                                 val (vars,sorts) = split vars_sorts [] []
                                 val variables = NameSet.addList variables vars
                                 val formula = formula_from_SE (hd (tl args)) functions variables
                                 (* need to AND in any sort predicate clauses such as $int(var) *)
                                 fun add_clause [] formula = formula
                                  |  add_clause (f::fs) formula = add_clause fs (Formula.And (f,formula))
                                 val formula = add_clause sorts formula
                                 fun add_forall [] formula = formula
                                  |  add_forall (v::vs) formula = add_forall vs (Formula.Forall(v,formula))
                                 fun add_exists [] formula = formula
                                  |  add_exists (v::vs) formula = add_exists vs (Formula.Exists(v,formula))
                              in
                                 case q of "exists" => add_exists vars formula
                                         | "forall" => add_forall vars formula
                                         (* The following should never occur *)
                                         | _ => raise Error ("Unknown Quantifier Type "^ error_message)
                              end
                         |Simple_symbol("not") =>
                                 if (List.length args) = 1 then
                                     let
                                        val f = formula_from_SE (hd args) functions variables
                                        (* do not simplify double nots because (assert (not is used to
                                           indicate a conjecture...
                                        fun negate (Formula.Not(f)) = f
                                         |  negate f = (Formula.Not(f))
                                        *)
                                        fun negate f = (Formula.Not(f))
                                     in
                                        negate f
                                     end
                                 else
                                     raise Error error_message
                         | Simple_symbol("and") =>
                                 if (List.length args) = 2 then
                                     Formula.And ((formula_from_SE (hd args) functions variables),(formula_from_SE (hd (tl args)) functions variables))
                                 else
                                     raise Error error_message
                         | Simple_symbol("or") =>
                                 if (List.length args) = 2 then
                                     Formula.Or ((formula_from_SE (hd args) functions variables),(formula_from_SE (hd (tl args)) functions variables))
                                 else
                                     raise Error error_message
                         | Simple_symbol("=>") =>
                                 if (List.length args) = 2 then
                                     Formula.Imp ((formula_from_SE (hd args) functions variables),(formula_from_SE (hd (tl args)) functions variables))
                                 else
                                     raise Error error_message
                         | Simple_symbol("<=>") => (* not in the standard or core logic but corresponds to iff *)
                                 if (List.length args) = 2 then
                                     Formula.Iff ((formula_from_SE (hd args) functions variables),(formula_from_SE (hd (tl args)) functions variables))
                                 else
                                     raise Error error_message
                         | Simple_symbol(_) => atom_from_SE se functions variables

                         | _ => raise Error error_message
             end
      end;


   (* ---------------------------------------------------------------- *)
   (* routines to produce  S-Expressions from a formula                *)
   (* NB these are the inner S-Expressions, an external command        *)
   (* (assert (S-Expression)) needs to be added.                       *)
   (* A NameAritySet of functions is also produced so that             *)
   (* suitable define-function SExpressions can be generated.          *)
   (* ---------------------------------------------------------------- *)
   fun term_to_SExpression (Term.Var (name)) functions = ([Simple_symbol(name)],functions)
    |  term_to_SExpression (Term.Rat r) functions =
         let
            val (p,q) = Rat.quotient_of_rat r
         in
           if Rat.ge0 r then ([Decimal (p,q)],functions) else
              ([Left_bracket,Simple_symbol("-"),Decimal(~p,q),Right_bracket],functions)
         end
    |  term_to_SExpression (Term.Fn (name,terms)) functions =
           let
              val functions = NameAritySet.add functions (name,(List.length terms))
              val (se,functions) = terms_to_SExpression terms functions
              val se = if (List.length terms) > 0 then [Left_bracket,Simple_symbol(name)]@se@[Right_bracket]
                       else [Simple_symbol(name)]
           in
              (se,functions)
           end
   and terms_to_SExpression terms functions =
           let
              fun fmap [] done functions = (List.concat (rev done),functions)
               |  fmap (t::ts) done functions =
                     let
                        val (se,functions) = term_to_SExpression t functions
                     in
                        fmap ts (se::done) functions
                     end
           in
             fmap terms [] functions
           end
              
   fun atom_to_SExpression ((name,terms):Atom.atom) functions =
           let
              val (se,functions) = terms_to_SExpression terms functions
           in
              (([Left_bracket,Simple_symbol(name)]@se@[Right_bracket]),functions)
           end; 
       
   fun formula_to_SExpression formula functions =
      case formula of Formula.True => ([Left_bracket,Simple_symbol("true"),Right_bracket],functions)
                   |  Formula.False => ([Left_bracket,Simple_symbol("false"),Right_bracket],functions)
                   |  Formula.Atom (atom) => atom_to_SExpression atom functions
                   |  Formula.Not (f) => 
                          let
                             val (se,functions) = formula_to_SExpression f functions
                             val se = [Left_bracket,Simple_symbol("not")]@se@[Right_bracket]
                          in
                             (se,functions)
                          end
                   |  Formula.And (fa,fb) =>
                          let
                             val (se_a,functions) = formula_to_SExpression fa functions
                             val (se_b,functions) = formula_to_SExpression fb functions
                             val se = [Left_bracket,Simple_symbol("and")]@se_a@se_b@[Right_bracket]
                          in
                             (se,functions)
                          end
                   |  Formula.Or (fa,fb) => 
                          let
                             val (se_a,functions) = formula_to_SExpression fa functions
                             val (se_b,functions) = formula_to_SExpression fb functions
                             val se = [Left_bracket,Simple_symbol("or")]@se_a@se_b@[Right_bracket]
                          in
                             (se,functions)
                          end
                   |  Formula.Imp (fa,fb) =>
                          let
                             val (se_a,functions) = formula_to_SExpression fa functions
                             val (se_b,functions) = formula_to_SExpression fb functions
                             val se = [Left_bracket,Simple_symbol("=>")]@se_a@se_b@[Right_bracket]
                          in
                             (se,functions)
                          end
                   |  Formula.Iff (fa,fb) =>
                          let
                             val (se_a,functions) = formula_to_SExpression fa functions
                             val (se_b,functions) = formula_to_SExpression fb functions
                             val se = [Left_bracket,Simple_symbol("<=>")]@se_a@se_b@[Right_bracket]
                          in
                             (se,functions)
                          end
                   |  Formula.Forall (v,f) => (* need to collate nested foralls into one variable list *)
                         let
                             fun collate (Formula.Forall (v,f)) vs =
                                       collate f ([Left_bracket,Simple_symbol(v),Simple_symbol("Real"),Right_bracket]::vs)
                              |  collate f vs = 
                                       let
                                          val (se,functions) = formula_to_SExpression f functions
                                          val se = [Left_bracket,Quantifier("forall"),Left_bracket]
                                                   @(List.concat (rev vs))@[Right_bracket]
                                                   @se @[Right_bracket]
                                       in
                                          (se,functions)
                                       end
                         in
                             (collate (Formula.Forall(v,f)) [])
                         end
                   |  Formula.Exists (v,f) => (* need to collate nested exists into one variable list *)
                         let
                             fun collate (Formula.Exists (v,f)) vs =
                                       collate f ([Left_bracket,Simple_symbol(v),Simple_symbol("Real"),Right_bracket]::vs)
                              |  collate f vs = 
                                       let
                                          val (se,functions) = formula_to_SExpression f functions
                                          val se = [Left_bracket,Quantifier("exists"),Left_bracket]
                                                   @(List.concat (rev vs))@[Right_bracket]
                                                   @se @[Right_bracket]
                                       in
                                          (se,functions)
                                       end
                         in
                             (collate (Formula.Exists(v,f)) [])
                         end;

   (* --------------------------------------------------- *)
   (* function to add default function declarations for   *)
   (* standard operators such as *,/,+ and -. Note that   *)
   (* the operator - is both unary and binary.            *)
   (* It makes sense to also add cos() sin() etc here.    *)
   (* --------------------------------------------------- *)
   fun define_standard_functions functions =
       let
          val functions = NameAritySet.add functions ("+",2)
          val functions = NameAritySet.add functions ("-",2)
          val functions = NameAritySet.add functions ("-",1)
          val functions = NameAritySet.add functions ("*",2)
          val functions = NameAritySet.add functions ("/",2)
          (* --------------------------------------------- *)
          (* standard MetiTarski functions to save users   *)
          (* having to use declare-fun, they'll still need *)
          (* to use declare-fun in other SMTLIB programs   *)   
          (* though.                                       *)
          (* --------------------------------------------- *)
          val functions = NameAritySet.add functions ("abs",1)
          val functions = NameAritySet.add functions ("arccos",1)
          val functions = NameAritySet.add functions ("arcsin",1)
          val functions = NameAritySet.add functions ("arctan",1)
          val functions = NameAritySet.add functions ("cosh",1)
          val functions = NameAritySet.add functions ("sinh",1)
          val functions = NameAritySet.add functions ("tanh",1)
          val functions = NameAritySet.add functions ("cos",1)
          val functions = NameAritySet.add functions ("sin",1)
          val functions = NameAritySet.add functions ("tan",1)
          val functions = NameAritySet.add functions ("cbrt",1)
          val functions = NameAritySet.add functions ("exp",1)
          val functions = NameAritySet.add functions ("ln",1)
          val functions = NameAritySet.add functions ("log",1)
          val functions = NameAritySet.add functions ("pow",1)
          val functions = NameAritySet.add functions ("sqrt",1)
          val functions = NameAritySet.add functions ("pi",0)
       in
          functions
       end


   (* ------------------------------------------------------------- *)
   (* function to interpret assert and declare-fun commands         *)
   (* functions is a NameArity map of functions including constants *)
   (* forumulas is a list (stack) of formulas.                      *)
   (* ------------------------------------------------------------- *)
   fun interpret_command (se as (Left_bracket::Command("declare-fun")::Simple_symbol(f)::Left_bracket::ts)) formulas functions includes =
       let
          val error_message = "Mulformed declare-fun in "^(tokenListToString se)^"\n"
          val ts = case (rev ts) of (Right_bracket::toks) => (rev toks)
                   | _ => raise Error ("Missing right bracket in "^error_message)
          val (s_o,ts) = getSExpression (Left_bracket::ts)
          val args = case s_o of
                      NONE => raise Error error_message
                    | SOME s => (removeBrackets s)
          val arity = if List.all isRealSort args then List.length args else
                  raise Error ("MetiTarski only deals with Reals! Error in argument list : "
                            ^ error_message)
          val (ftype_o,_) = getSExpression ts
          val ft = case ftype_o of SOME s => removeBrackets s
                                 | NONE => raise Error error_message
          val _ = if null ft then raise Error error_message
                  else if isRealSort (hd ft) then ()
                  else raise Error ("functions/constants must be of type Real in "^error_message)
       in
         (formulas,(NameAritySet.add functions (f,arity)),includes)
       end
    |  interpret_command (se as (Left_bracket::Command("declare-fun")::_)) _ _ _ =
          raise Error ("Mulformed declare-fun in "^(tokenListToString se)^"\n")
    |  interpret_command (se as (Left_bracket::Command("set-option")::Keyword(":includes")::ts)) formulas functions includes =
       let
           val error_message = "Mulformed set-option :includes in"^(tokenListToString se)^"\n"
           val ts = removeBrackets ts
           fun add_include_file [Right_bracket] includes = includes
            |  add_include_file (Simple_symbol(fname)::rest) includes =
                    add_include_file rest (fname::includes)
            |  add_include_file _ _ = raise Error error_message
           val includes = add_include_file ts includes
       in
           (formulas,functions,includes)
       end
    |  interpret_command (se as (Left_bracket::Command("assert")::Left_bracket::ts_plus_rb)) formulas functions includes =
       let
           val error_message = "Mulformed assert in "^(tokenListToString se)^"\n"
           val ts = case (rev ts_plus_rb) of (Right_bracket::toks) => (rev toks)
                   | _ => raise Error ("Missing right bracket in "^error_message)
           val (s_o,ts) = getSExpression (Left_bracket::ts)
           (* ----------------------------------------------------------------------- *)
           (* in the case of quantifiers there may be more than one expression but    *)
           (* these need to be joined into one before being passed to formula_from_SE *)
           (* ----------------------------------------------------------------------- *)
           val (s_o,_) = if null ts then (s_o,ts) else getSExpression (Left_bracket::Left_bracket::ts_plus_rb)
           val expression = case s_o of
                             NONE => raise Error error_message
                           | SOME s => s
           val formula = formula_from_SE expression functions NameSet.empty
       in
           ((formula::formulas),functions,includes)
       end

    |  interpret_command _ formulas functions includes = (formulas,functions,includes);
          

    fun interpret_all_commands token_list =
       let
           val formulas = []
           val functions = NameAritySet.empty
           val functions = define_standard_functions functions
           val includes = []
           fun interpret [] formulas functions includes = (formulas,functions,includes)
            |  interpret ts formulas functions includes =
                  let
                     val (s_o,ts) = getSExpression ts
                     val (formulas,functions,includes) = case s_o of
                         SOME se => ((interpret_command se formulas functions includes) (*handle Error _ => (formulas,functions,includes)*))
                      |  NONE => (formulas,functions,includes)
                  in
                      interpret ts formulas functions includes
                  end
       in
         interpret token_list formulas functions includes
       end;

              
    (* function to test command interpreter *)
    fun testInterpreter fin fout =
        let
            val out_stream = TextIO.openOut fout
            val token_list = readTokens fin
            val (formulas,functions,includes) = interpret_all_commands token_list
            fun incs_to_str [] s = s^"\n------- End of Includes -------\n"
             |  incs_to_str (inc::incs) s = incs_to_str incs (s^inc^"\n")
            val incs = incs_to_str includes "------- Include Files -------\n"
            val _ = TextIO.output (out_stream,incs)
            val fstr = functionsToString functions
            val _ = TextIO.output (out_stream,fstr)
            fun form_to_str [] s = s^"\n---- End of Formulas ----\n"
             |  form_to_str (f::rest) s = form_to_str rest (s^(Formula.toString f))
            val formula_str = form_to_str formulas "---- Asserted formulas ----\n"
            val _ = TextIO.output (out_stream,formula_str)
            val _ = TextIO.closeOut out_stream
        in
        ()
        end;

   (* ---------------------------------------------------------------------------------- *)
   (* main read function, interprets commands and returns in Tptp.Problem format         *)
   (* NB comments are not returned as they are skipped as white space and I don't        *)
   (* think that MetiTarski makes any use of them anyway. Most fields are set to         *)
   (* default values, e.g. name = empty, role = ConjectureRole, source = NoFormulaSource *)
   (* and so on.                                                                         *)
   (* ---------------------------------------------------------------------------------- *)

   (* NB SMT format does not allow for formula names. Formulas therefore need to be given *)
   (* an arbitrary name. Initially this was just the empty string but this then upsets    *)
   (* the code that writes out the proof so instead an incremented value is used.         *)
   val formula_name_count = ref 0;
   fun formula_name () = (formula_name_count := (1 + !formula_name_count);"SMT_formula_"^(Int.toString (!formula_name_count)));


    fun read file_name =
        let
           val token_list = readTokens file_name
           val (formulas,_,includes) = interpret_all_commands token_list
           fun toTPTPformula [] tptpFormulas conjectureFound = 
               if conjectureFound then rev tptpFormulas
               else raise Error ("No conjecture found in file : "^file_name^"\n")
            |  toTPTPformula (f::fs) tptpFormulas conjectureFound =
               let
                  fun checkForConjecture (Formula.Not(f)) = (true,f)
                   |  checkForConjecture f = (false,f)
                  val (isConjecture,f,conjectureFound) = 
                      if conjectureFound then (false,f,conjectureFound)
                      else
                        let
                          val (isConjecture,f) = checkForConjecture (f)
                          val conjectureFound = isConjecture
                        in
                          (isConjecture,f,conjectureFound)
                        end
                  val name = Tptp.FormulaName(formula_name())
                  val role = if(isConjecture) then Tptp.ConjectureRole
                                              else Tptp.AxiomRole
                  val body = Tptp.FofFormulaBody(f)
                  val source = Tptp.NoFormulaSource
                  val tptpF= Tptp.Formula {
                            name = name,
                            role = role,
                            body = body,
                            source = source
                  }
               in
                  toTPTPformula fs (tptpF::tptpFormulas) conjectureFound
               end
           val tptpFormulas = toTPTPformula formulas [] false                         
        in
           Tptp.Problem {comments=[],includes=includes,formulas=tptpFormulas}
        end; 

   (* --------------------------------------------------------------------------------- *)
   (* function to write out a Tptp.Problem in SMTLIB format, comments are written first *)
   (* and could, for example, contain the original tptp file.                           *)
   (* NB comments should NOT contain any \n or \r chars.                                *)
   (* --------------------------------------------------------------------------------- *)
    fun write file_name (Tptp.Problem {includes,formulas,comments}) =
        let
           val error_message = "Error in SMTLIB.write"
           val out_stream = TextIO.openOut file_name
           fun write_comments [] = ()
            |  write_comments (c::cs) =
               let
                   val _ = TextIO.output (out_stream,(";"^c^"\n"))
               in
                   write_comments cs
               end
           val _ = write_comments comments
           val _ = TextIO.output (out_stream,"(set-logic AUFNIRA)\n")
           fun add_includes [] s = s
            |  add_includes (inc::incs) s = add_includes incs (s^" "^inc)
           val include_str = add_includes includes "(set-option :includes ("
           val include_str = include_str^"))\n"
           val _ = TextIO.output (out_stream,include_str)
           fun convert [] forms conjectureFound = forms
            |  convert ((Tptp.Formula {role=Tptp.ConjectureRole,body=Tptp.FofFormulaBody(f),...})::fs) forms false =
                  convert fs ((Formula.Not(f))::forms) true
            |  convert ((Tptp.Formula {role=Tptp.ConjectureRole,...})::_) _ true =
                  raise Error (error_message ^ " more than one conjecture!")
            |  convert ((Tptp.Formula {role=Tptp.AxiomRole,body=Tptp.FofFormulaBody(f),...})::fs) forms conjectureFound =
                  convert fs (f::forms) conjectureFound
            |  convert _ _ _ = raise Error error_message
           val forms = convert formulas [] false
           fun get_ses [] ses functions = ((rev ses),functions)
            |  get_ses (f::fs) ses functions =
                 let
                    val (se,functions) = formula_to_SExpression f functions
                 in
                    get_ses fs (se::ses) functions
                 end
            val (ses,functions) = get_ses forms [] (NameAritySet.empty)
            val functions = NameAritySet.toList functions
            (* function to determine if operators are amongst those predefined in core logic *)
            fun is_defined_in_core ("+",2) = true
             |  is_defined_in_core ("-",1) = true
             |  is_defined_in_core ("-",2) = true
             |  is_defined_in_core ("*",2) = true
             |  is_defined_in_core ("/",2) = true
             |  is_defined_in_core _ = false
            fun fa_to_str n s = if (n <= 0) then s^" ) Real)\n"
                                else fa_to_str (n-1) (s^" Real")
            fun f_to_str (f,a) = if is_defined_in_core (f,a) then "" else fa_to_str a ("(declare-fun "^f^" (") 
            fun fs_to_str [] s = s
             |  fs_to_str ((f,a)::fs) s =
                   fs_to_str fs (s^(f_to_str (f,a)))
            val fun_str = fs_to_str functions ""
            val _ = TextIO.output (out_stream,fun_str)
            fun ses_to_str [] s = s
             |  ses_to_str (se::ses) s =
                   ses_to_str ses ("(assert "^ (tokenListToString se)^")\n" ^ s)
            val ses_str = ses_to_str ses "\n"
            val _ = TextIO.output (out_stream,ses_str)
            val _ = TextIO.output (out_stream,"(check-sat)\n")
            val _ = TextIO.output (out_stream,"(exit)\n")
         in
            TextIO.closeOut out_stream
         end;
            


(* ------------------------------------------------------- *)
(* generic code to remove redundant brackets from a string *)
(* this is not specific to the SMTLIB code so may be moved *)
(* to a separate file/structure.                           *)
(* ------------------------------------------------------- *)
fun remove_redundant_brackets str =
    let
	val chars = explode str
        fun check_matching_numbers_of_brackets char_list =
            let
               fun check count [] = count = 0
                |  check count (#"("::cs) = check (count+1) cs
                |  check count (#")"::cs) = check (count-1) cs
                |  check count (c::cs) = check count cs
             in
                check 0 char_list
             end
        fun remove_leading_blanks (#" "::cs) = remove_leading_blanks cs
         |  remove_leading_blanks (#"\n"::cs) = remove_leading_blanks cs
         |  remove_leading_blanks (#"\t"::cs) = remove_leading_blanks cs
         |  remove_leading_blanks cs = cs
	fun find_closing_bracket open_brackets (c::cs) enclosed =
	    if c = #")" then
		if open_brackets = 1 then  (* return the enclosed string without brackets *)
                     ((remove_leading_blanks (rev (remove_leading_blanks enclosed))),cs)
		else find_closing_bracket (open_brackets-1) cs (c::enclosed)
	    else if c = #"(" then
                find_closing_bracket (open_brackets+1) cs (c::enclosed)
            else
                find_closing_bracket open_brackets cs (c::enclosed)
         | find_closing_bracket open_brackets [] enclosed =
             if open_brackets = 0 then ((rev enclosed),[])
             else raise Error "missing closing bracket"
       fun strip_matching_enclosing_brackets (#"("::cs) =
           let
               val (enclosed,remainder) = find_closing_bracket 1 cs []
           in
               if (null remainder) then (strip_matching_enclosing_brackets enclosed)
               else (#"("::cs)
           end
        |  strip_matching_enclosing_brackets cs = cs
       fun process [] processed = rev processed
        |  process (#"("::cs) processed = 
              let
                 val (enclosed,remainder) = find_closing_bracket 1 cs []
                 val enclosed = strip_matching_enclosing_brackets enclosed
                 val remainder = #")"::remainder
              in
                 process (enclosed @ remainder) (#"("::processed)
              end
        |  process (c::cs) processed = process cs (c::processed)
     in
        if (check_matching_numbers_of_brackets chars) then
             implode (process chars [])
        else
             raise Error ("brackets don't match in string : "^(implode chars))
     end

(* Code to read a tptp file, remove redundant brackets, and comments and rewrite it *)
fun skipTPTPcomments in_stream char_stack =
    let
       fun add_chars_to_stack [] stack = stack
        |  add_chars_to_stack (c::cs) stack =
               add_chars_to_stack cs (c::stack)
       fun remove_leading_spaces (#" "::cs) = remove_leading_spaces cs
        |  remove_leading_spaces cs = cs
       fun add_line_to_stack line stack =
           let
              val (c::cs) = remove_leading_spaces (explode line)
           in
              if c = #"%" then stack
              else add_chars_to_stack (c::cs) stack
           end
    in
       case (TextIO.inputLine in_stream) of
          NONE => rev char_stack
        | SOME line =>
             let
                val char_stack = add_line_to_stack line char_stack
             in
                skipTPTPcomments in_stream char_stack
             end
    end 

open Useful (* only used for chat and chatting below *)

fun filter_tptp_file fname =
let
    (* create a backup of the original file *)
    val new_fname = OS.FileSys.tmpName ()
    val in_stream = TextIO.openIn fname
    val out_stream = TextIO.openOut new_fname
    val charList =  skipTPTPcomments in_stream [];
    val inString = implode charList
    val _ = chatting 3 andalso chat ("filter_tptp_file input :\n"^inString^"\n")
    val outString = remove_redundant_brackets inString
    val _ = chatting 3 andalso chat ("filter_tptp_file output :\n"^outString^"\n")
    val _ = TextIO.output (out_stream,outString)
    val _ = TextIO.closeIn in_stream
    val _ = TextIO.closeOut out_stream
in
    new_fname
end    
    
    
    

              
















end (* of module *)



                   
                                         


       

               
