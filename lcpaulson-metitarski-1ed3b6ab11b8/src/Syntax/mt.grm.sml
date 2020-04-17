functor MTLrValsFun(structure Token : TOKEN)
 : sig structure ParserData : PARSER_DATA
       structure Tokens : MT_TOKENS
   end
 = 
struct
structure ParserData=
struct
structure Header = 
struct
open Useful;


end
structure LrTable = Token.LrTable
structure Token = Token
local open LrTable in 
val table=let val actionRows =
"\
\\001\000\005\000\062\000\006\000\061\000\008\000\060\000\009\000\059\000\
\\010\000\058\000\012\000\119\000\000\000\
\\001\000\005\000\062\000\006\000\061\000\008\000\060\000\009\000\059\000\
\\010\000\058\000\012\000\120\000\000\000\
\\001\000\005\000\062\000\006\000\061\000\008\000\060\000\009\000\059\000\
\\010\000\058\000\016\000\104\000\000\000\
\\001\000\005\000\062\000\006\000\061\000\008\000\060\000\009\000\059\000\
\\010\000\058\000\016\000\104\000\019\000\056\000\020\000\055\000\
\\021\000\054\000\022\000\053\000\023\000\052\000\024\000\051\000\000\000\
\\001\000\005\000\062\000\006\000\061\000\008\000\060\000\009\000\059\000\
\\010\000\058\000\016\000\128\000\000\000\
\\001\000\005\000\062\000\006\000\061\000\008\000\060\000\009\000\059\000\
\\010\000\058\000\016\000\130\000\018\000\129\000\000\000\
\\001\000\005\000\062\000\006\000\061\000\008\000\060\000\009\000\059\000\
\\010\000\058\000\016\000\132\000\018\000\131\000\000\000\
\\001\000\006\000\044\000\015\000\043\000\025\000\042\000\034\000\041\000\
\\035\000\040\000\036\000\039\000\037\000\038\000\038\000\037\000\
\\039\000\036\000\041\000\035\000\042\000\034\000\000\000\
\\001\000\006\000\044\000\015\000\049\000\035\000\048\000\038\000\037\000\
\\039\000\036\000\041\000\035\000\042\000\034\000\000\000\
\\001\000\006\000\044\000\015\000\049\000\038\000\037\000\039\000\036\000\
\\041\000\035\000\042\000\034\000\000\000\
\\001\000\006\000\044\000\015\000\087\000\035\000\048\000\038\000\037\000\
\\039\000\036\000\041\000\035\000\042\000\034\000\000\000\
\\001\000\011\000\122\000\000\000\
\\001\000\012\000\023\000\000\000\
\\001\000\012\000\024\000\000\000\
\\001\000\012\000\028\000\000\000\
\\001\000\012\000\029\000\000\000\
\\001\000\013\000\076\000\000\000\
\\001\000\014\000\115\000\000\000\
\\001\000\015\000\012\000\000\000\
\\001\000\015\000\013\000\000\000\
\\001\000\015\000\014\000\000\000\
\\001\000\015\000\030\000\000\000\
\\001\000\015\000\092\000\017\000\091\000\000\000\
\\001\000\016\000\022\000\000\000\
\\001\000\016\000\071\000\026\000\070\000\027\000\069\000\028\000\068\000\
\\029\000\067\000\030\000\066\000\031\000\065\000\032\000\064\000\000\000\
\\001\000\016\000\085\000\000\000\
\\001\000\016\000\109\000\000\000\
\\001\000\016\000\114\000\000\000\
\\001\000\026\000\070\000\027\000\069\000\028\000\068\000\029\000\067\000\
\\030\000\066\000\031\000\065\000\032\000\064\000\000\000\
\\001\000\033\000\025\000\000\000\
\\001\000\033\000\099\000\000\000\
\\001\000\033\000\117\000\000\000\
\\001\000\039\000\020\000\040\000\019\000\041\000\018\000\042\000\017\000\000\000\
\\001\000\040\000\015\000\000\000\
\\001\000\041\000\103\000\000\000\
\\001\000\042\000\026\000\000\000\
\\001\000\042\000\027\000\000\000\
\\001\000\044\000\000\000\000\000\
\\134\000\000\000\
\\135\000\000\000\
\\136\000\001\000\010\000\002\000\009\000\003\000\008\000\004\000\007\000\000\000\
\\137\000\000\000\
\\138\000\000\000\
\\139\000\000\000\
\\140\000\000\000\
\\141\000\000\000\
\\142\000\000\000\
\\143\000\000\000\
\\144\000\000\000\
\\145\000\000\000\
\\146\000\000\000\
\\147\000\000\000\
\\148\000\000\000\
\\148\000\016\000\105\000\000\000\
\\149\000\000\000\
\\150\000\000\000\
\\151\000\005\000\062\000\006\000\061\000\008\000\060\000\009\000\059\000\
\\010\000\058\000\011\000\057\000\016\000\104\000\019\000\056\000\
\\020\000\055\000\021\000\054\000\022\000\053\000\023\000\052\000\
\\024\000\051\000\000\000\
\\151\000\005\000\062\000\006\000\061\000\008\000\060\000\009\000\059\000\
\\010\000\058\000\011\000\057\000\019\000\056\000\020\000\055\000\
\\021\000\054\000\022\000\053\000\023\000\052\000\024\000\051\000\000\000\
\\152\000\000\000\
\\153\000\005\000\062\000\006\000\061\000\008\000\060\000\009\000\059\000\
\\010\000\058\000\000\000\
\\154\000\000\000\
\\155\000\026\000\070\000\027\000\069\000\000\000\
\\156\000\000\000\
\\157\000\000\000\
\\158\000\000\000\
\\159\000\000\000\
\\160\000\030\000\084\000\000\000\
\\161\000\005\000\062\000\006\000\061\000\008\000\060\000\009\000\059\000\
\\010\000\058\000\011\000\083\000\019\000\056\000\020\000\055\000\
\\021\000\054\000\022\000\053\000\023\000\052\000\024\000\051\000\000\000\
\\162\000\005\000\062\000\006\000\061\000\008\000\060\000\009\000\059\000\
\\010\000\058\000\000\000\
\\163\000\000\000\
\\164\000\000\000\
\\165\000\000\000\
\\166\000\000\000\
\\167\000\000\000\
\\168\000\000\000\
\\169\000\000\000\
\\170\000\000\000\
\\171\000\000\000\
\\172\000\000\000\
\\173\000\000\000\
\\174\000\000\000\
\\175\000\000\000\
\\176\000\000\000\
\\177\000\000\000\
\\178\000\000\000\
\\179\000\000\000\
\\180\000\000\000\
\\181\000\000\000\
\\182\000\000\000\
\\183\000\000\000\
\\184\000\012\000\116\000\000\000\
\\185\000\000\000\
\\186\000\015\000\073\000\000\000\
\\187\000\000\000\
\\188\000\005\000\062\000\006\000\061\000\008\000\060\000\009\000\059\000\
\\010\000\058\000\012\000\113\000\000\000\
\\189\000\000\000\
\\190\000\000\000\
\\191\000\000\000\
\\192\000\000\000\
\\193\000\000\000\
\\194\000\010\000\058\000\000\000\
\\195\000\008\000\060\000\009\000\059\000\010\000\058\000\000\000\
\\196\000\008\000\060\000\009\000\059\000\010\000\058\000\000\000\
\\197\000\010\000\058\000\000\000\
\\198\000\010\000\058\000\000\000\
\\199\000\010\000\058\000\000\000\
\"
val actionRowNumbers =
"\040\000\042\000\041\000\040\000\
\\038\000\018\000\019\000\020\000\
\\043\000\039\000\033\000\032\000\
\\032\000\023\000\012\000\047\000\
\\048\000\050\000\049\000\013\000\
\\029\000\035\000\036\000\046\000\
\\014\000\015\000\021\000\007\000\
\\008\000\057\000\052\000\024\000\
\\092\000\097\000\098\000\099\000\
\\055\000\054\000\007\000\016\000\
\\016\000\007\000\009\000\067\000\
\\066\000\025\000\010\000\009\000\
\\009\000\084\000\082\000\083\000\
\\081\000\080\000\079\000\022\000\
\\009\000\009\000\009\000\009\000\
\\009\000\007\000\076\000\078\000\
\\077\000\075\000\074\000\073\000\
\\072\000\030\000\096\000\009\000\
\\058\000\063\000\034\000\062\000\
\\056\000\053\000\028\000\100\000\
\\009\000\022\000\008\000\026\000\
\\070\000\009\000\002\000\059\000\
\\060\000\009\000\009\000\105\000\
\\104\000\103\000\102\000\101\000\
\\061\000\044\000\094\000\027\000\
\\017\000\090\000\095\000\051\000\
\\068\000\069\000\065\000\031\000\
\\003\000\000\000\001\000\009\000\
\\091\000\011\000\034\000\045\000\
\\009\000\009\000\009\000\093\000\
\\007\000\089\000\004\000\005\000\
\\006\000\064\000\071\000\088\000\
\\086\000\087\000\085\000\037\000"
val gotoT =
"\
\\001\000\131\000\002\000\004\000\003\000\003\000\004\000\002\000\
\\005\000\001\000\000\000\
\\000\000\
\\000\000\
\\002\000\009\000\003\000\003\000\004\000\002\000\005\000\001\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\006\000\014\000\000\000\
\\006\000\019\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\007\000\031\000\008\000\030\000\018\000\029\000\000\000\
\\009\000\045\000\010\000\044\000\018\000\043\000\000\000\
\\012\000\048\000\000\000\
\\000\000\
\\011\000\061\000\000\000\
\\016\000\070\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\007\000\072\000\008\000\030\000\018\000\029\000\000\000\
\\014\000\073\000\000\000\
\\014\000\075\000\000\000\
\\007\000\078\000\008\000\077\000\018\000\076\000\000\000\
\\018\000\079\000\000\000\
\\012\000\080\000\000\000\
\\000\000\
\\000\000\
\\010\000\084\000\018\000\043\000\000\000\
\\018\000\086\000\000\000\
\\018\000\087\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\013\000\088\000\000\000\
\\018\000\091\000\000\000\
\\018\000\092\000\000\000\
\\018\000\093\000\000\000\
\\018\000\094\000\000\000\
\\018\000\095\000\000\000\
\\007\000\096\000\008\000\030\000\018\000\029\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\017\000\099\000\018\000\098\000\000\000\
\\011\000\061\000\000\000\
\\000\000\
\\015\000\100\000\000\000\
\\000\000\
\\012\000\048\000\000\000\
\\000\000\
\\011\000\061\000\000\000\
\\000\000\
\\018\000\104\000\000\000\
\\013\000\105\000\000\000\
\\009\000\106\000\010\000\044\000\018\000\043\000\000\000\
\\000\000\
\\000\000\
\\018\000\108\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\018\000\109\000\000\000\
\\018\000\110\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\011\000\061\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\012\000\116\000\000\000\
\\000\000\
\\000\000\
\\017\000\119\000\018\000\098\000\000\000\
\\000\000\
\\000\000\
\\015\000\121\000\000\000\
\\000\000\
\\018\000\122\000\000\000\
\\018\000\123\000\000\000\
\\018\000\124\000\000\000\
\\000\000\
\\007\000\125\000\008\000\030\000\018\000\029\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\011\000\061\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\"
val numstates = 132
val numrules = 66
val s = ref "" and index = ref 0
val string_to_int = fn () => 
let val i = !index
in index := i+2; Char.ord(String.sub(!s,i)) + Char.ord(String.sub(!s,i+1)) * 256
end
val string_to_list = fn s' =>
    let val len = String.size s'
        fun f () =
           if !index < len then string_to_int() :: f()
           else nil
   in index := 0; s := s'; f ()
   end
val string_to_pairlist = fn (conv_key,conv_entry) =>
     let fun f () =
         case string_to_int()
         of 0 => EMPTY
          | n => PAIR(conv_key (n-1),conv_entry (string_to_int()),f())
     in f
     end
val string_to_pairlist_default = fn (conv_key,conv_entry) =>
    let val conv_row = string_to_pairlist(conv_key,conv_entry)
    in fn () =>
       let val default = conv_entry(string_to_int())
           val row = conv_row()
       in (row,default)
       end
   end
val string_to_table = fn (convert_row,s') =>
    let val len = String.size s'
        fun f ()=
           if !index < len then convert_row() :: f()
           else nil
     in (s := s'; index := 0; f ())
     end
local
  val memo = Array.array(numstates+numrules,ERROR)
  val _ =let fun g i=(Array.update(memo,i,REDUCE(i-numstates)); g(i+1))
       fun f i =
            if i=numstates then g i
            else (Array.update(memo,i,SHIFT (STATE i)); f (i+1))
          in f 0 handle General.Subscript => ()
          end
in
val entry_to_action = fn 0 => ACCEPT | 1 => ERROR | j => Array.sub(memo,(j-2))
end
val gotoT=Array.fromList(string_to_table(string_to_pairlist(NT,STATE),gotoT))
val actionRows=string_to_table(string_to_pairlist_default(T,entry_to_action),actionRows)
val actionRowNumbers = string_to_list actionRowNumbers
val actionT = let val actionRowLookUp=
let val a=Array.fromList(actionRows) in fn i=>Array.sub(a,i) end
in Array.fromList(List.map actionRowLookUp actionRowNumbers)
end
in LrTable.mkLrTable {actions=actionT,gotos=gotoT,numRules=numrules,
numStates=numstates,initialState=STATE 0}
end
end
local open Header in
type pos = int
type arg = string
structure MlyValue = 
struct
datatype svalue = VOID | ntVOID of unit
 | ILLEGAL_CHARACTER of  (string) | LOWER_WORD of  (string)
 | UPPER_WORD of  (string) | SINGLE_QUOTED of  (string)
 | INTEGER of  (string) | REAL of  (string) | COMMENT of  (string)
 | term of  (Term.term) | term_list of  (Term.term list)
 | arguments of  (Term.term list) | vars of  (string list)
 | quantbody of  (string list*Formula.formula)
 | interv of  (int*Term.term*int*Term.term)
 | rel of  (Term.term*Term.term -> Literal.literal)
 | binop of  (Formula.formula*Formula.formula -> Formula.formula)
 | literal of  (Tptp.literal) | disjunction of  (Tptp.literal list)
 | comp_fml of  (Formula.formula) | formula of  (Formula.formula)
 | name of  (string) | include_line of  (string)
 | fml_line of  (Tptp.formula) | tptp_line of  (Tptp.item)
 | tptp_lines of  (Tptp.item list) | mt_file of  (Tptp.item list)
end
type svalue = MlyValue.svalue
type result = Tptp.item list
end
structure EC=
struct
open LrTable
infix 5 $$
fun x $$ y = y::x
val is_keyword =
fn _ => false
val preferred_change : (term list * term list) list = 
(nil
,nil
 $$ (T 15))::
(nil
,nil
 $$ (T 7))::
(nil
,nil
 $$ (T 4))::
(nil
 $$ (T 15),nil
)::
(nil
 $$ (T 42),nil
)::
nil
val noShift = 
fn (T 43) => true | _ => false
val showTerminal =
fn (T 0) => "COMMENT"
  | (T 1) => "FOF"
  | (T 2) => "CNF"
  | (T 3) => "INCLUDE"
  | (T 4) => "PLUS"
  | (T 5) => "MINUS"
  | (T 6) => "UNARYSIGN"
  | (T 7) => "AST"
  | (T 8) => "SLASH"
  | (T 9) => "CARET"
  | (T 10) => "COLON"
  | (T 11) => "COMMA"
  | (T 12) => "LBRKT"
  | (T 13) => "RBRKT"
  | (T 14) => "LPAREN"
  | (T 15) => "RPAREN"
  | (T 16) => "LPARENQ"
  | (T 17) => "RPARENQ"
  | (T 18) => "EQUALS"
  | (T 19) => "NEQUALS"
  | (T 20) => "LE"
  | (T 21) => "LESS"
  | (T 22) => "GE"
  | (T 23) => "GREATER"
  | (T 24) => "EXCLAMATION"
  | (T 25) => "AMPERSAND"
  | (T 26) => "NAMPERSAND"
  | (T 27) => "IFF"
  | (T 28) => "NIFF"
  | (T 29) => "VLINE"
  | (T 30) => "NVLINE"
  | (T 31) => "IMPLIES"
  | (T 32) => "PERIOD"
  | (T 33) => "QUESTION"
  | (T 34) => "TILDE"
  | (T 35) => "TOK_FALSE"
  | (T 36) => "TOK_TRUE"
  | (T 37) => "REAL"
  | (T 38) => "INTEGER"
  | (T 39) => "SINGLE_QUOTED"
  | (T 40) => "UPPER_WORD"
  | (T 41) => "LOWER_WORD"
  | (T 42) => "ILLEGAL_CHARACTER"
  | (T 43) => "EOF"
  | _ => "bogus-term"
local open Header in
val errtermvalue=
fn _ => MlyValue.VOID
end
val terms : term list = nil
 $$ (T 43) $$ (T 36) $$ (T 35) $$ (T 34) $$ (T 33) $$ (T 32) $$ (T 31)
 $$ (T 30) $$ (T 29) $$ (T 28) $$ (T 27) $$ (T 26) $$ (T 25) $$ (T 24)
 $$ (T 23) $$ (T 22) $$ (T 21) $$ (T 20) $$ (T 19) $$ (T 18) $$ (T 17)
 $$ (T 16) $$ (T 15) $$ (T 14) $$ (T 13) $$ (T 12) $$ (T 11) $$ (T 10)
 $$ (T 9) $$ (T 8) $$ (T 7) $$ (T 6) $$ (T 5) $$ (T 4) $$ (T 3) $$ (T 
2) $$ (T 1)end
structure Actions =
struct 
exception mlyAction of int
local open Header in
val actions = 
fn (i392,defaultPos,stack,
    (fileName):arg) =>
case (i392,stack)
of  ( 0, ( ( _, ( MlyValue.tptp_lines tptp_lines, tptp_lines1left, 
tptp_lines1right)) :: rest671)) => let val  result = MlyValue.mt_file
 (tptp_lines)
 in ( LrTable.NT 0, ( result, tptp_lines1left, tptp_lines1right), 
rest671)
end
|  ( 1, ( ( _, ( MlyValue.tptp_lines tptp_lines, _, tptp_lines1right))
 :: ( _, ( MlyValue.tptp_line tptp_line, tptp_line1left, _)) :: 
rest671)) => let val  result = MlyValue.tptp_lines (
tptp_line::tptp_lines)
 in ( LrTable.NT 1, ( result, tptp_line1left, tptp_lines1right), 
rest671)
end
|  ( 2, ( rest671)) => let val  result = MlyValue.tptp_lines ([])
 in ( LrTable.NT 1, ( result, defaultPos, defaultPos), rest671)
end
|  ( 3, ( ( _, ( MlyValue.fml_line fml_line, fml_line1left, 
fml_line1right)) :: rest671)) => let val  result = MlyValue.tptp_line
 (Tptp.Fml fml_line)
 in ( LrTable.NT 2, ( result, fml_line1left, fml_line1right), rest671)

end
|  ( 4, ( ( _, ( MlyValue.include_line include_line, include_line1left
, include_line1right)) :: rest671)) => let val  result = 
MlyValue.tptp_line (Tptp.Include include_line)
 in ( LrTable.NT 2, ( result, include_line1left, include_line1right), 
rest671)
end
|  ( 5, ( ( _, ( MlyValue.COMMENT COMMENT, COMMENT1left, COMMENT1right
)) :: rest671)) => let val  result = MlyValue.tptp_line (
Tptp.Comment COMMENT)
 in ( LrTable.NT 2, ( result, COMMENT1left, COMMENT1right), rest671)

end
|  ( 6, ( ( _, ( _, _, PERIOD1right)) :: _ :: ( _, ( MlyValue.formula 
formula, _, _)) :: _ :: ( _, ( MlyValue.LOWER_WORD LOWER_WORD, _, _))
 :: _ :: ( _, ( MlyValue.name name, _, _)) :: _ :: ( _, ( _, FOF1left,
 _)) :: rest671)) => let val  result = MlyValue.fml_line (
Tptp.Formula{name = Tptp.FormulaName name,
			      role = Tptp.fromStringRole LOWER_WORD,
			      body = Tptp.FofFormulaBody formula,
                              source=Tptp.NoFormulaSource}
)
 in ( LrTable.NT 3, ( result, FOF1left, PERIOD1right), rest671)
end
|  ( 7, ( ( _, ( _, _, PERIOD1right)) :: _ :: _ :: ( _, ( 
MlyValue.disjunction disjunction, _, _)) :: _ :: _ :: ( _, ( 
MlyValue.LOWER_WORD LOWER_WORD, _, _)) :: _ :: ( _, ( MlyValue.name 
name, _, _)) :: _ :: ( _, ( _, CNF1left, _)) :: rest671)) => let val  
result = MlyValue.fml_line (
Tptp.Formula{name = Tptp.FormulaName name,
			      role = Tptp.fromStringRole LOWER_WORD,
			      body = Tptp.CnfFormulaBody disjunction,
                              source=Tptp.NoFormulaSource}
)
 in ( LrTable.NT 3, ( result, CNF1left, PERIOD1right), rest671)
end
|  ( 8, ( ( _, ( _, _, PERIOD1right)) :: _ :: ( _, ( 
MlyValue.SINGLE_QUOTED SINGLE_QUOTED, _, _)) :: _ :: ( _, ( _, 
INCLUDE1left, _)) :: rest671)) => let val  result = 
MlyValue.include_line (SINGLE_QUOTED)
 in ( LrTable.NT 4, ( result, INCLUDE1left, PERIOD1right), rest671)

end
|  ( 9, ( ( _, ( MlyValue.LOWER_WORD LOWER_WORD, LOWER_WORD1left, 
LOWER_WORD1right)) :: rest671)) => let val  result = MlyValue.name (
LOWER_WORD)
 in ( LrTable.NT 5, ( result, LOWER_WORD1left, LOWER_WORD1right), 
rest671)
end
|  ( 10, ( ( _, ( MlyValue.UPPER_WORD UPPER_WORD, UPPER_WORD1left, 
UPPER_WORD1right)) :: rest671)) => let val  result = MlyValue.name (
UPPER_WORD)
 in ( LrTable.NT 5, ( result, UPPER_WORD1left, UPPER_WORD1right), 
rest671)
end
|  ( 11, ( ( _, ( MlyValue.INTEGER INTEGER, INTEGER1left, 
INTEGER1right)) :: rest671)) => let val  result = MlyValue.name (
INTEGER)
 in ( LrTable.NT 5, ( result, INTEGER1left, INTEGER1right), rest671)

end
|  ( 12, ( ( _, ( MlyValue.SINGLE_QUOTED SINGLE_QUOTED, 
SINGLE_QUOTED1left, SINGLE_QUOTED1right)) :: rest671)) => let val  
result = MlyValue.name (SINGLE_QUOTED)
 in ( LrTable.NT 5, ( result, SINGLE_QUOTED1left, SINGLE_QUOTED1right)
, rest671)
end
|  ( 13, ( ( _, ( _, _, RPAREN1right)) :: ( _, ( MlyValue.comp_fml 
comp_fml, _, _)) :: ( _, ( _, LPAREN1left, _)) :: rest671)) => let
 val  result = MlyValue.formula (comp_fml)
 in ( LrTable.NT 6, ( result, LPAREN1left, RPAREN1right), rest671)
end
|  ( 14, ( ( _, ( MlyValue.comp_fml comp_fml, comp_fml1left, 
comp_fml1right)) :: rest671)) => let val  result = MlyValue.formula (
comp_fml)
 in ( LrTable.NT 6, ( result, comp_fml1left, comp_fml1right), rest671)

end
|  ( 15, ( ( _, ( _, TOK_FALSE1left, TOK_FALSE1right)) :: rest671)) =>
 let val  result = MlyValue.formula (Formula.False)
 in ( LrTable.NT 6, ( result, TOK_FALSE1left, TOK_FALSE1right), 
rest671)
end
|  ( 16, ( ( _, ( _, TOK_TRUE1left, TOK_TRUE1right)) :: rest671)) =>
 let val  result = MlyValue.formula (Formula.True)
 in ( LrTable.NT 6, ( result, TOK_TRUE1left, TOK_TRUE1right), rest671)

end
|  ( 17, ( ( _, ( MlyValue.term term, term1left, term1right)) :: 
rest671)) => let val  result = MlyValue.formula (fmOfAtom term)
 in ( LrTable.NT 6, ( result, term1left, term1right), rest671)
end
|  ( 18, ( ( _, ( MlyValue.formula formula, _, formula1right)) :: ( _,
 ( _, TILDE1left, _)) :: rest671)) => let val  result = 
MlyValue.comp_fml (Formula.Not formula)
 in ( LrTable.NT 7, ( result, TILDE1left, formula1right), rest671)
end
|  ( 19, ( ( _, ( MlyValue.term term2, _, term2right)) :: ( _, ( 
MlyValue.rel rel, _, _)) :: ( _, ( MlyValue.term term1, term1left, _))
 :: rest671)) => let val  result = MlyValue.comp_fml (
Literal.toFormula (rel (term1,term2)))
 in ( LrTable.NT 7, ( result, term1left, term2right), rest671)
end
|  ( 20, ( ( _, ( MlyValue.interv interv, _, interv1right)) :: _ :: (
 _, ( MlyValue.term term, term1left, _)) :: rest671)) => let val  
result = MlyValue.comp_fml (
Literal.toFormula (litOfInterval (term,interv)))
 in ( LrTable.NT 7, ( result, term1left, interv1right), rest671)
end
|  ( 21, ( ( _, ( MlyValue.formula formula2, _, formula2right)) :: ( _
, ( MlyValue.binop binop, _, _)) :: ( _, ( MlyValue.formula formula1, 
formula1left, _)) :: rest671)) => let val  result = MlyValue.comp_fml
 (binop (formula1,formula2))
 in ( LrTable.NT 7, ( result, formula1left, formula2right), rest671)

end
|  ( 22, ( ( _, ( MlyValue.quantbody quantbody, _, quantbody1right))
 :: ( _, ( _, EXCLAMATION1left, _)) :: rest671)) => let val  result = 
MlyValue.comp_fml (Formula.listMkForall quantbody)
 in ( LrTable.NT 7, ( result, EXCLAMATION1left, quantbody1right), 
rest671)
end
|  ( 23, ( ( _, ( MlyValue.quantbody quantbody, _, quantbody1right))
 :: ( _, ( _, QUESTION1left, _)) :: rest671)) => let val  result = 
MlyValue.comp_fml (Formula.listMkExists quantbody)
 in ( LrTable.NT 7, ( result, QUESTION1left, quantbody1right), rest671
)
end
|  ( 24, ( ( _, ( MlyValue.formula formula, _, formula1right)) :: _ ::
 _ :: ( _, ( MlyValue.vars vars, _, _)) :: ( _, ( _, LBRKT1left, _))
 :: rest671)) => let val  result = MlyValue.quantbody (vars,formula)
 in ( LrTable.NT 13, ( result, LBRKT1left, formula1right), rest671)

end
|  ( 25, ( ( _, ( MlyValue.disjunction disjunction, _, 
disjunction1right)) :: _ :: ( _, ( MlyValue.literal literal, 
literal1left, _)) :: rest671)) => let val  result = 
MlyValue.disjunction (literal::disjunction)
 in ( LrTable.NT 8, ( result, literal1left, disjunction1right), 
rest671)
end
|  ( 26, ( ( _, ( MlyValue.literal literal, literal1left, 
literal1right)) :: rest671)) => let val  result = MlyValue.disjunction
 ([literal])
 in ( LrTable.NT 8, ( result, literal1left, literal1right), rest671)

end
|  ( 27, ( ( _, ( MlyValue.term term, term1left, term1right)) :: 
rest671)) => let val  result = MlyValue.literal (
Tptp.Literal (Literal.fromFormula (fmOfAtom term)))
 in ( LrTable.NT 9, ( result, term1left, term1right), rest671)
end
|  ( 28, ( ( _, ( MlyValue.term term2, _, term2right)) :: ( _, ( 
MlyValue.rel rel, _, _)) :: ( _, ( MlyValue.term term1, term1left, _))
 :: rest671)) => let val  result = MlyValue.literal (
Tptp.Literal (rel (term1,term2)))
 in ( LrTable.NT 9, ( result, term1left, term2right), rest671)
end
|  ( 29, ( ( _, ( MlyValue.interv interv, _, interv1right)) :: _ :: (
 _, ( MlyValue.term term, term1left, _)) :: rest671)) => let val  
result = MlyValue.literal (Tptp.Literal (litOfInterval (term,interv)))
 in ( LrTable.NT 9, ( result, term1left, interv1right), rest671)
end
|  ( 30, ( ( _, ( MlyValue.literal literal, _, literal1right)) :: ( _,
 ( _, TILDE1left, _)) :: rest671)) => let val  result = 
MlyValue.literal (Tptp.negateLiteral literal)
 in ( LrTable.NT 9, ( result, TILDE1left, literal1right), rest671)
end
|  ( 31, ( ( _, ( _, _, RPAREN1right)) :: ( _, ( MlyValue.term term2,
 _, _)) :: ( _, ( MlyValue.rel rel, _, _)) :: ( _, ( MlyValue.term 
term1, _, _)) :: _ :: ( _, ( _, TILDE1left, _)) :: rest671)) => let
 val  result = MlyValue.literal (
Tptp.negateLiteral (Tptp.Literal (rel (term1,term2))))
 in ( LrTable.NT 9, ( result, TILDE1left, RPAREN1right), rest671)
end
|  ( 32, ( ( _, ( _, AMPERSAND1left, AMPERSAND1right)) :: rest671)) =>
 let val  result = MlyValue.binop (Formula.And)
 in ( LrTable.NT 10, ( result, AMPERSAND1left, AMPERSAND1right), 
rest671)
end
|  ( 33, ( ( _, ( _, NAMPERSAND1left, NAMPERSAND1right)) :: rest671))
 => let val  result = MlyValue.binop (Formula.Not o Formula.And)
 in ( LrTable.NT 10, ( result, NAMPERSAND1left, NAMPERSAND1right), 
rest671)
end
|  ( 34, ( ( _, ( _, IFF1left, IFF1right)) :: rest671)) => let val  
result = MlyValue.binop (Formula.Iff)
 in ( LrTable.NT 10, ( result, IFF1left, IFF1right), rest671)
end
|  ( 35, ( ( _, ( _, NIFF1left, NIFF1right)) :: rest671)) => let val  
result = MlyValue.binop (Formula.Not o Formula.Iff)
 in ( LrTable.NT 10, ( result, NIFF1left, NIFF1right), rest671)
end
|  ( 36, ( ( _, ( _, IMPLIES1left, IMPLIES1right)) :: rest671)) => let
 val  result = MlyValue.binop (Formula.Imp)
 in ( LrTable.NT 10, ( result, IMPLIES1left, IMPLIES1right), rest671)

end
|  ( 37, ( ( _, ( _, VLINE1left, VLINE1right)) :: rest671)) => let
 val  result = MlyValue.binop (Formula.Or)
 in ( LrTable.NT 10, ( result, VLINE1left, VLINE1right), rest671)
end
|  ( 38, ( ( _, ( _, NVLINE1left, NVLINE1right)) :: rest671)) => let
 val  result = MlyValue.binop (Formula.Not o Formula.Or)
 in ( LrTable.NT 10, ( result, NVLINE1left, NVLINE1right), rest671)

end
|  ( 39, ( ( _, ( _, EQUALS1left, EQUALS1right)) :: rest671)) => let
 val  result = MlyValue.rel (Literal.mkEq)
 in ( LrTable.NT 11, ( result, EQUALS1left, EQUALS1right), rest671)

end
|  ( 40, ( ( _, ( _, NEQUALS1left, NEQUALS1right)) :: rest671)) => let
 val  result = MlyValue.rel (Literal.mkNeq)
 in ( LrTable.NT 11, ( result, NEQUALS1left, NEQUALS1right), rest671)

end
|  ( 41, ( ( _, ( _, LE1left, LE1right)) :: rest671)) => let val  
result = MlyValue.rel (Literal.mkBinop (true,"<="))
 in ( LrTable.NT 11, ( result, LE1left, LE1right), rest671)
end
|  ( 42, ( ( _, ( _, GE1left, GE1right)) :: rest671)) => let val  
result = MlyValue.rel (Literal.mkBinop (true,"<=") o swap)
 in ( LrTable.NT 11, ( result, GE1left, GE1right), rest671)
end
|  ( 43, ( ( _, ( _, LESS1left, LESS1right)) :: rest671)) => let val  
result = MlyValue.rel (Literal.mkBinop (false,"<=") o swap)
 in ( LrTable.NT 11, ( result, LESS1left, LESS1right), rest671)
end
|  ( 44, ( ( _, ( _, GREATER1left, GREATER1right)) :: rest671)) => let
 val  result = MlyValue.rel (Literal.mkBinop (false,"<="))
 in ( LrTable.NT 11, ( result, GREATER1left, GREATER1right), rest671)

end
|  ( 45, ( ( _, ( _, _, RPAREN1right)) :: ( _, ( MlyValue.term term2,
 _, _)) :: _ :: ( _, ( MlyValue.term term1, _, _)) :: ( _, ( _, 
LPAREN1left, _)) :: rest671)) => let val  result = MlyValue.interv (
(1,term1,1,term2))
 in ( LrTable.NT 12, ( result, LPAREN1left, RPAREN1right), rest671)

end
|  ( 46, ( ( _, ( _, _, RPAREN1right)) :: ( _, ( MlyValue.term term2,
 _, _)) :: _ :: ( _, ( MlyValue.term term1, _, _)) :: ( _, ( _, 
LPARENQ1left, _)) :: rest671)) => let val  result = MlyValue.interv (
(0,term1,1,term2))
 in ( LrTable.NT 12, ( result, LPARENQ1left, RPAREN1right), rest671)

end
|  ( 47, ( ( _, ( _, _, RPARENQ1right)) :: ( _, ( MlyValue.term term2,
 _, _)) :: _ :: ( _, ( MlyValue.term term1, _, _)) :: ( _, ( _, 
LPAREN1left, _)) :: rest671)) => let val  result = MlyValue.interv (
(1,term1,0,term2))
 in ( LrTable.NT 12, ( result, LPAREN1left, RPARENQ1right), rest671)

end
|  ( 48, ( ( _, ( _, _, RPARENQ1right)) :: ( _, ( MlyValue.term term2,
 _, _)) :: _ :: ( _, ( MlyValue.term term1, _, _)) :: ( _, ( _, 
LPARENQ1left, _)) :: rest671)) => let val  result = MlyValue.interv (
(0,term1,0,term2))
 in ( LrTable.NT 12, ( result, LPARENQ1left, RPARENQ1right), rest671)

end
|  ( 49, ( ( _, ( MlyValue.vars vars, _, vars1right)) :: _ :: ( _, ( 
MlyValue.UPPER_WORD UPPER_WORD, UPPER_WORD1left, _)) :: rest671)) =>
 let val  result = MlyValue.vars (UPPER_WORD::vars)
 in ( LrTable.NT 14, ( result, UPPER_WORD1left, vars1right), rest671)

end
|  ( 50, ( ( _, ( MlyValue.UPPER_WORD UPPER_WORD, UPPER_WORD1left, 
UPPER_WORD1right)) :: rest671)) => let val  result = MlyValue.vars (
[UPPER_WORD])
 in ( LrTable.NT 14, ( result, UPPER_WORD1left, UPPER_WORD1right), 
rest671)
end
|  ( 51, ( ( _, ( _, _, RPAREN1right)) :: ( _, ( MlyValue.term_list 
term_list, _, _)) :: ( _, ( _, LPAREN1left, _)) :: rest671)) => let
 val  result = MlyValue.arguments (term_list)
 in ( LrTable.NT 15, ( result, LPAREN1left, RPAREN1right), rest671)

end
|  ( 52, ( rest671)) => let val  result = MlyValue.arguments ([])
 in ( LrTable.NT 15, ( result, defaultPos, defaultPos), rest671)
end
|  ( 53, ( ( _, ( MlyValue.term_list term_list, _, term_list1right))
 :: _ :: ( _, ( MlyValue.term term, term1left, _)) :: rest671)) => let
 val  result = MlyValue.term_list (term::term_list)
 in ( LrTable.NT 16, ( result, term1left, term_list1right), rest671)

end
|  ( 54, ( ( _, ( MlyValue.term term, term1left, term1right)) :: 
rest671)) => let val  result = MlyValue.term_list ([term])
 in ( LrTable.NT 16, ( result, term1left, term1right), rest671)
end
|  ( 55, ( ( _, ( _, _, RPAREN1right)) :: ( _, ( MlyValue.term term, _
, _)) :: ( _, ( _, LPAREN1left, _)) :: rest671)) => let val  result = 
MlyValue.term (term)
 in ( LrTable.NT 17, ( result, LPAREN1left, RPAREN1right), rest671)

end
|  ( 56, ( ( _, ( MlyValue.arguments arguments, _, arguments1right))
 :: ( _, ( MlyValue.LOWER_WORD LOWER_WORD, LOWER_WORD1left, _)) :: 
rest671)) => let val  result = MlyValue.term (
Term.eval_Fn (LOWER_WORD,arguments))
 in ( LrTable.NT 17, ( result, LOWER_WORD1left, arguments1right), 
rest671)
end
|  ( 57, ( ( _, ( MlyValue.UPPER_WORD UPPER_WORD, UPPER_WORD1left, 
UPPER_WORD1right)) :: rest671)) => let val  result = MlyValue.term (
Term.Var UPPER_WORD)
 in ( LrTable.NT 17, ( result, UPPER_WORD1left, UPPER_WORD1right), 
rest671)
end
|  ( 58, ( ( _, ( MlyValue.INTEGER INTEGER, INTEGER1left, 
INTEGER1right)) :: rest671)) => let val  result = MlyValue.term (
termOfDecimal INTEGER)
 in ( LrTable.NT 17, ( result, INTEGER1left, INTEGER1right), rest671)

end
|  ( 59, ( ( _, ( MlyValue.REAL REAL, REAL1left, REAL1right)) :: 
rest671)) => let val  result = MlyValue.term (termOfDecimal REAL)
 in ( LrTable.NT 17, ( result, REAL1left, REAL1right), rest671)
end
|  ( 60, ( ( _, ( MlyValue.term term, _, term1right)) :: ( _, ( _, 
MINUS1left, _)) :: rest671)) => let val  result = MlyValue.term (
Term.eval_Fn("-",[term]))
 in ( LrTable.NT 17, ( result, MINUS1left, term1right), rest671)
end
|  ( 61, ( ( _, ( MlyValue.term term2, _, term2right)) :: _ :: ( _, ( 
MlyValue.term term1, term1left, _)) :: rest671)) => let val  result = 
MlyValue.term (Term.eval_Fn("+",[term1,term2]))
 in ( LrTable.NT 17, ( result, term1left, term2right), rest671)
end
|  ( 62, ( ( _, ( MlyValue.term term2, _, term2right)) :: _ :: ( _, ( 
MlyValue.term term1, term1left, _)) :: rest671)) => let val  result = 
MlyValue.term (Term.eval_Fn("-",[term1,term2]))
 in ( LrTable.NT 17, ( result, term1left, term2right), rest671)
end
|  ( 63, ( ( _, ( MlyValue.term term2, _, term2right)) :: _ :: ( _, ( 
MlyValue.term term1, term1left, _)) :: rest671)) => let val  result = 
MlyValue.term (Term.eval_Fn("*",[term1,term2]))
 in ( LrTable.NT 17, ( result, term1left, term2right), rest671)
end
|  ( 64, ( ( _, ( MlyValue.term term2, _, term2right)) :: _ :: ( _, ( 
MlyValue.term term1, term1left, _)) :: rest671)) => let val  result = 
MlyValue.term (Term.eval_Fn("/",[term1,term2]))
 in ( LrTable.NT 17, ( result, term1left, term2right), rest671)
end
|  ( 65, ( ( _, ( MlyValue.term term2, _, term2right)) :: _ :: ( _, ( 
MlyValue.term term1, term1left, _)) :: rest671)) => let val  result = 
MlyValue.term (Term.Fn("^",[term1,term2]))
 in ( LrTable.NT 17, ( result, term1left, term2right), rest671)
end
| _ => raise (mlyAction i392)
end
val void = MlyValue.VOID
val extract = fn a => (fn MlyValue.mt_file x => x
| _ => let exception ParseInternal
	in raise ParseInternal end) a 
end
end
structure Tokens : MT_TOKENS =
struct
type svalue = ParserData.svalue
type ('a,'b) token = ('a,'b) Token.token
fun COMMENT (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 0,(
ParserData.MlyValue.COMMENT i,p1,p2))
fun FOF (p1,p2) = Token.TOKEN (ParserData.LrTable.T 1,(
ParserData.MlyValue.VOID,p1,p2))
fun CNF (p1,p2) = Token.TOKEN (ParserData.LrTable.T 2,(
ParserData.MlyValue.VOID,p1,p2))
fun INCLUDE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 3,(
ParserData.MlyValue.VOID,p1,p2))
fun PLUS (p1,p2) = Token.TOKEN (ParserData.LrTable.T 4,(
ParserData.MlyValue.VOID,p1,p2))
fun MINUS (p1,p2) = Token.TOKEN (ParserData.LrTable.T 5,(
ParserData.MlyValue.VOID,p1,p2))
fun UNARYSIGN (p1,p2) = Token.TOKEN (ParserData.LrTable.T 6,(
ParserData.MlyValue.VOID,p1,p2))
fun AST (p1,p2) = Token.TOKEN (ParserData.LrTable.T 7,(
ParserData.MlyValue.VOID,p1,p2))
fun SLASH (p1,p2) = Token.TOKEN (ParserData.LrTable.T 8,(
ParserData.MlyValue.VOID,p1,p2))
fun CARET (p1,p2) = Token.TOKEN (ParserData.LrTable.T 9,(
ParserData.MlyValue.VOID,p1,p2))
fun COLON (p1,p2) = Token.TOKEN (ParserData.LrTable.T 10,(
ParserData.MlyValue.VOID,p1,p2))
fun COMMA (p1,p2) = Token.TOKEN (ParserData.LrTable.T 11,(
ParserData.MlyValue.VOID,p1,p2))
fun LBRKT (p1,p2) = Token.TOKEN (ParserData.LrTable.T 12,(
ParserData.MlyValue.VOID,p1,p2))
fun RBRKT (p1,p2) = Token.TOKEN (ParserData.LrTable.T 13,(
ParserData.MlyValue.VOID,p1,p2))
fun LPAREN (p1,p2) = Token.TOKEN (ParserData.LrTable.T 14,(
ParserData.MlyValue.VOID,p1,p2))
fun RPAREN (p1,p2) = Token.TOKEN (ParserData.LrTable.T 15,(
ParserData.MlyValue.VOID,p1,p2))
fun LPARENQ (p1,p2) = Token.TOKEN (ParserData.LrTable.T 16,(
ParserData.MlyValue.VOID,p1,p2))
fun RPARENQ (p1,p2) = Token.TOKEN (ParserData.LrTable.T 17,(
ParserData.MlyValue.VOID,p1,p2))
fun EQUALS (p1,p2) = Token.TOKEN (ParserData.LrTable.T 18,(
ParserData.MlyValue.VOID,p1,p2))
fun NEQUALS (p1,p2) = Token.TOKEN (ParserData.LrTable.T 19,(
ParserData.MlyValue.VOID,p1,p2))
fun LE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 20,(
ParserData.MlyValue.VOID,p1,p2))
fun LESS (p1,p2) = Token.TOKEN (ParserData.LrTable.T 21,(
ParserData.MlyValue.VOID,p1,p2))
fun GE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 22,(
ParserData.MlyValue.VOID,p1,p2))
fun GREATER (p1,p2) = Token.TOKEN (ParserData.LrTable.T 23,(
ParserData.MlyValue.VOID,p1,p2))
fun EXCLAMATION (p1,p2) = Token.TOKEN (ParserData.LrTable.T 24,(
ParserData.MlyValue.VOID,p1,p2))
fun AMPERSAND (p1,p2) = Token.TOKEN (ParserData.LrTable.T 25,(
ParserData.MlyValue.VOID,p1,p2))
fun NAMPERSAND (p1,p2) = Token.TOKEN (ParserData.LrTable.T 26,(
ParserData.MlyValue.VOID,p1,p2))
fun IFF (p1,p2) = Token.TOKEN (ParserData.LrTable.T 27,(
ParserData.MlyValue.VOID,p1,p2))
fun NIFF (p1,p2) = Token.TOKEN (ParserData.LrTable.T 28,(
ParserData.MlyValue.VOID,p1,p2))
fun VLINE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 29,(
ParserData.MlyValue.VOID,p1,p2))
fun NVLINE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 30,(
ParserData.MlyValue.VOID,p1,p2))
fun IMPLIES (p1,p2) = Token.TOKEN (ParserData.LrTable.T 31,(
ParserData.MlyValue.VOID,p1,p2))
fun PERIOD (p1,p2) = Token.TOKEN (ParserData.LrTable.T 32,(
ParserData.MlyValue.VOID,p1,p2))
fun QUESTION (p1,p2) = Token.TOKEN (ParserData.LrTable.T 33,(
ParserData.MlyValue.VOID,p1,p2))
fun TILDE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 34,(
ParserData.MlyValue.VOID,p1,p2))
fun TOK_FALSE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 35,(
ParserData.MlyValue.VOID,p1,p2))
fun TOK_TRUE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 36,(
ParserData.MlyValue.VOID,p1,p2))
fun REAL (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 37,(
ParserData.MlyValue.REAL i,p1,p2))
fun INTEGER (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 38,(
ParserData.MlyValue.INTEGER i,p1,p2))
fun SINGLE_QUOTED (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 39,(
ParserData.MlyValue.SINGLE_QUOTED i,p1,p2))
fun UPPER_WORD (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 40,(
ParserData.MlyValue.UPPER_WORD i,p1,p2))
fun LOWER_WORD (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 41,(
ParserData.MlyValue.LOWER_WORD i,p1,p2))
fun ILLEGAL_CHARACTER (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 42
,(ParserData.MlyValue.ILLEGAL_CHARACTER i,p1,p2))
fun EOF (p1,p2) = Token.TOKEN (ParserData.LrTable.T 43,(
ParserData.MlyValue.VOID,p1,p2))
end
end
