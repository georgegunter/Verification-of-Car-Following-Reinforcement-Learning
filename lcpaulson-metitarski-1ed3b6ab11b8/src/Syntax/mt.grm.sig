signature MT_TOKENS =
sig
type ('a,'b) token
type svalue
val EOF:  'a * 'a -> (svalue,'a) token
val ILLEGAL_CHARACTER: (string) *  'a * 'a -> (svalue,'a) token
val LOWER_WORD: (string) *  'a * 'a -> (svalue,'a) token
val UPPER_WORD: (string) *  'a * 'a -> (svalue,'a) token
val SINGLE_QUOTED: (string) *  'a * 'a -> (svalue,'a) token
val INTEGER: (string) *  'a * 'a -> (svalue,'a) token
val REAL: (string) *  'a * 'a -> (svalue,'a) token
val TOK_TRUE:  'a * 'a -> (svalue,'a) token
val TOK_FALSE:  'a * 'a -> (svalue,'a) token
val TILDE:  'a * 'a -> (svalue,'a) token
val QUESTION:  'a * 'a -> (svalue,'a) token
val PERIOD:  'a * 'a -> (svalue,'a) token
val IMPLIES:  'a * 'a -> (svalue,'a) token
val NVLINE:  'a * 'a -> (svalue,'a) token
val VLINE:  'a * 'a -> (svalue,'a) token
val NIFF:  'a * 'a -> (svalue,'a) token
val IFF:  'a * 'a -> (svalue,'a) token
val NAMPERSAND:  'a * 'a -> (svalue,'a) token
val AMPERSAND:  'a * 'a -> (svalue,'a) token
val EXCLAMATION:  'a * 'a -> (svalue,'a) token
val GREATER:  'a * 'a -> (svalue,'a) token
val GE:  'a * 'a -> (svalue,'a) token
val LESS:  'a * 'a -> (svalue,'a) token
val LE:  'a * 'a -> (svalue,'a) token
val NEQUALS:  'a * 'a -> (svalue,'a) token
val EQUALS:  'a * 'a -> (svalue,'a) token
val RPARENQ:  'a * 'a -> (svalue,'a) token
val LPARENQ:  'a * 'a -> (svalue,'a) token
val RPAREN:  'a * 'a -> (svalue,'a) token
val LPAREN:  'a * 'a -> (svalue,'a) token
val RBRKT:  'a * 'a -> (svalue,'a) token
val LBRKT:  'a * 'a -> (svalue,'a) token
val COMMA:  'a * 'a -> (svalue,'a) token
val COLON:  'a * 'a -> (svalue,'a) token
val CARET:  'a * 'a -> (svalue,'a) token
val SLASH:  'a * 'a -> (svalue,'a) token
val AST:  'a * 'a -> (svalue,'a) token
val UNARYSIGN:  'a * 'a -> (svalue,'a) token
val MINUS:  'a * 'a -> (svalue,'a) token
val PLUS:  'a * 'a -> (svalue,'a) token
val INCLUDE:  'a * 'a -> (svalue,'a) token
val CNF:  'a * 'a -> (svalue,'a) token
val FOF:  'a * 'a -> (svalue,'a) token
val COMMENT: (string) *  'a * 'a -> (svalue,'a) token
end
signature MT_LRVALS=
sig
structure Tokens : MT_TOKENS
structure ParserData:PARSER_DATA
sharing type ParserData.Token.token = Tokens.token
sharing type ParserData.svalue = Tokens.svalue
end
