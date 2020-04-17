(*
    ml-lex specification for MetiTarski parsing

    Based on a specification of THF by Nik Sultana
    Computer Lab, Cambridge University

 Notes:
 * Got it working on Poly/ML thanks to Timothy Bourke's instructions:
   http://www.tbrk.org/software/poly_smlnj-lib.html
*)

structure T = Tokens
type pos = int             (* Position in file *)
type lineNo = int
type svalue = T.svalue
type ('a,'b) token = ('a,'b) T.token
type lexresult = (svalue,pos) token
type lexarg = string
type arg = lexarg

fun eof fileName = Tokens.EOF (0,0);

%%
%header (functor MTLexFun(structure Tokens: MT_TOKENS));

numeric             = [0-9];
sign                = [-+];
lower_alpha         = [a-z];
upper_alpha         = [A-Z];
alpha_numeric       = ({lower_alpha}|{upper_alpha}|{numeric}|_);
ddollar             = \$\$;

unsigned_int        = {numeric}+;
dot_decimal         = [.]{numeric}+;
exp_part            = [Ee]{sign}?{unsigned_int};
real                = ({unsigned_int}?{dot_decimal}{exp_part}? | {unsigned_int}{exp_part});
upper_word          = {upper_alpha}{alpha_numeric}*;

sq_char             = ([\040-\041\043-\126]|[\\]['\\]);

single_quote        = ['];
single_quoted       = {single_quote}{sq_char}+{single_quote};

lower_word                = {lower_alpha}{alpha_numeric}*;
system_comment_one        = [%][\ ]*{ddollar}[_]*;
system_comment_multi      = [/][\*][\ ]*(ddollar)([^\*]*[\*][\*]*[^/\*])*[^\*]*[\*][\*]*[/];
system_comment            = (system_comment_one)|(system_comment_multi);
comment_one               = [%][^\n]*;
comment_multi             = [/][\*]([^\*]*[\*]+[^/\*])*[^\*]*[\*]+[/];
comment                   = {comment_one}|{comment_multi};

ws                        = ([\ ]|[\t]);
eol                       = ("\013\010"|"\010"|"\013");

%%

"include"	=> (T.INCLUDE(yypos,yypos+size yytext));
"cnf"		=> (T.CNF(yypos,yypos+size yytext));
"fof"		=> (T.FOF(yypos,yypos+size yytext));

{ws}		=> (continue ());
{eol}		=> (continue ());
{comment}	=> (T.COMMENT(yytext,yypos,yypos+size yytext));

"&"             => (T.AMPERSAND(yypos,yypos+size yytext));
"~"             => (T.TILDE(yypos,yypos+size yytext));
"$false"        => (T.TOK_FALSE(yypos,yypos+size yytext));
"$true"         => (T.TOK_TRUE(yypos,yypos+size yytext));
"|"             => (T.VLINE(yypos,yypos+size yytext));

"+"		=> (T.PLUS(yypos,yypos+size yytext));
"-"		=> (T.MINUS(yypos,yypos+size yytext));
"*"		=> (T.AST(yypos,yypos+size yytext));
"/"		=> (T.SLASH(yypos,yypos+size yytext));
"^"             => (T.CARET(yypos,yypos+size yytext));

":"             => (T.COLON(yypos,yypos+size yytext));
","             => (T.COMMA(yypos,yypos+size yytext));
"="             => (T.EQUALS(yypos,yypos+size yytext));
"<="            => (T.LE(yypos,yypos+size yytext));
"<"             => (T.LESS(yypos,yypos+size yytext));
">="            => (T.GE(yypos,yypos+size yytext));
">"             => (T.GREATER(yypos,yypos+size yytext));
"!"             => (T.EXCLAMATION(yypos,yypos+size yytext));

"<=>"           => (T.IFF(yypos,yypos+size yytext));
"=>"            => (T.IMPLIES(yypos,yypos+size yytext));
"["             => (T.LBRKT(yypos,yypos+size yytext));
"("             => (T.LPAREN(yypos,yypos+size yytext));
"(="            => (T.LPARENQ(yypos,yypos+size yytext));
"~&"            => (T.NAMPERSAND(yypos,yypos+size yytext));
"!="            => (T.NEQUALS(yypos,yypos+size yytext));
"<~>"           => (T.NIFF(yypos,yypos+size yytext));
"~|"            => (T.NVLINE(yypos,yypos+size yytext));
"."             => (T.PERIOD(yypos,yypos+size yytext));
"?"             => (T.QUESTION(yypos,yypos+size yytext));
"]"             => (T.RBRKT(yypos,yypos+size yytext));
")"             => (T.RPAREN(yypos,yypos+size yytext));
"=)"            => (T.RPARENQ(yypos,yypos+size yytext));

{real}		=> (T.REAL(yytext,yypos,yypos+size yytext));
{unsigned_int} => (T.INTEGER(yytext,yypos,yypos+size yytext));
{single_quoted}	=> (T.SINGLE_QUOTED(yytext,yypos,yypos+size yytext));
{upper_word}	=> (T.UPPER_WORD(yytext,yypos,yypos+size yytext));
{lower_word}	=> (T.LOWER_WORD(yytext,yypos,yypos+size yytext));

.		=> (T.ILLEGAL_CHARACTER(yytext,yypos,yypos+size yytext));
