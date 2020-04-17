use"Syntax/lib/base.sig";
use"Syntax/lib/join.sml";
use"Syntax/lib/lrtable.sml";
use"Syntax/lib/stream.sml";
use"Syntax/lib/parser2.sml";

fun goodAtom (Term.Fn (s,_)) = size s > 0 andalso Char.isLower (String.sub (s,0))
  | goodAtom _ = false;

fun fmOfAtom t =
  Formula.Atom (if goodAtom t then Term.destFn t  else ("Bad_Formula",[t]));

fun termOfDecimal s =
  let val mant::rest = String.tokens (fn c => c = #"e" orelse c = #"E") s   (*remove exponent*)
      val e = Option.valOf (IntInf.fromString (hd rest)) handle Empty => 0
      val tenexp = Rat.exp (Rat.rat_of_intinf 10, Rat.rat_of_intinf e)
      val [uns] = String.tokens (fn c => c = #"+" orelse c = #"-") mant   (*remove sign*)
      val a::ss = String.fields (fn c => c = #".") uns                 (*integer part*)
      val b = hd ss handle Empty => ""
      val n = String.size b
      val i = (if a="" then 0 else Option.valOf (IntInf.fromString a))
      val j = (if b="" then 0 else Option.valOf (IntInf.fromString b))
      val tenn = Useful.exp IntInf.* 10 n 1
      val r = Rat.mult (tenexp, Rat.rat_of_quotient (i*tenn+j, tenn))
  in  Term.Rat (if String.isPrefix "-" s then Rat.neg r else r)  end
  handle _ => (print ("Unable to translate numeric constant " ^ s ^ "\n");
	  raise Parse.NoParse);

fun litOfInterval (x, (il,lower,iu,upper)) =
  (true, ("interval",
          [Term.Rat (Rat.rat_of_int il), lower,
           Term.Rat (Rat.rat_of_int iu), upper, x]));

use"Syntax/mt.grm.sig";
use"Syntax/mt.grm.sml";
use"Syntax/mt.lex.sml";

structure MTLrVals : MT_LRVALS =
   MTLrValsFun(structure Token = LrParser.Token);

structure MTLex =   (*ARG_LEXER if  %arg specified in mt.lex*)
   MTLexFun(structure Tokens = MTLrVals.Tokens);

structure MTParser : PARSER =
   Join(structure ParserData = MTLrVals.ParserData
               structure Lex = MTLex
	       structure LrParser = LrParser);

structure MT_Tptp =
struct

local open Tptp Useful
in

  fun report_errors fileName [] = ()
    | report_errors fileName errs =
	let val dev = TextIO.openIn fileName
	    val chp = ref 1
	    val errsp = ref errs
	    (*(i,j) identify character positions in the file, save that for EOF we have (0,0)*)
	    fun errInLine(e,i,j) = (if i=0 then TextIO.endOfStream dev else !chp >= j)
	in
	  while not (TextIO.endOfStream dev orelse null (!errsp)) do
	    let val line = getOpt (TextIO.inputLine dev, "")
	    in
	      chp := !chp + size line;
	      while not (null (!errsp)) andalso errInLine(hd (!errsp)) do
		let val (e,i,j) = hd (!errsp)
		    val arrow =
		      if i=0 then (nChars #" " (size line - 1)) ^ "^"
		      else nChars #" " (i + size line - !chp - 1) ^ nChars #"^" (j-i+1)
		in
		  TextIO.output (TextIO.stdErr, line);
		  TextIO.output (TextIO.stdErr, arrow ^ " " ^ e ^ "\n");
		  errsp := tl (!errsp)
		end
	    end;
	  TextIO.closeIn dev; raise Parse.NoParse
	end;

  fun parse fileName =
    let val dev = if fileName = "-" then TextIO.stdIn else TextIO.openIn fileName
	val errsp = ref []
	val stream = MTParser.makeLexer(fn i => TextIO.inputN(dev,i))
	fun error (e,i,j) = (errsp := (e,i,j) :: !errsp)
	fun cleanup errs = if fileName = "-" then
                   if (null (!errsp)) then () else print "syntax errors\n"
            else (TextIO.closeIn dev; report_errors fileName (rev (!errsp)))
     in MTParser.parse(15,stream,error,fileName)  (*lookahead = 15, recommended*)
	  before cleanup (rev (!errsp))
	handle LrParser.ParseError =>  (*Catch and report internal parser errors*)
	       (cleanup (rev (!errsp)); raise Parse.NoParse)
    end;

  val no_single_quotes = String.translate (fn c => if c = #"'" then "" else str c);

  fun toProblem items =
    let fun insert (Comment s, (cs,incs,fmls)) = (s::cs, incs, fmls)
	  | insert (Include s, (cs,incs,fmls)) = (cs, no_single_quotes s :: incs, fmls)
	  | insert (Fml fm,    (cs,incs,fmls)) = (cs, incs, fm::fmls)
	val (cs, incs, fmls) = foldl insert ([],[],[]) items
    in
      Problem
	{comments = rev cs,
	 includes = rev incs,
	 formulas = rev fmls}
    end;

  fun interFreeBound (CnfFormulaBody _) = NameSet.empty
    | interFreeBound (FofFormulaBody fm) =
        NameSet.intersect (Formula.boundVars fm) (Formula.freeVars fm);

  val bodyToString = Print.toString (Tptp.ppFormulaBody Tptp.defaultMapping)

  fun verify_fml (Formula {body, ...}) =
    if NameAritySet.exists (fn (s,_) => s = "Bad_Formula") (Tptp.formulaBodyRelations body)
    then (print ("Illegal atoms in formula.\n" ^ bodyToString body ^ "\n");
	  raise Parse.NoParse)
    else
      let val vs = NameSet.toList (interFreeBound body)
      in
	 if not (null vs)
	 then (print ("Overlapping free and bound variables in formula: " ^
	              Useful.join ", " vs ^ "\n" ^ bodyToString body ^ "\n");
	       raise Parse.NoParse)
	 else ()
      end;

  fun verify_prob (p as Problem {formulas,...}) = (List.app verify_fml formulas; p);

end;

fun read ({mapping, filename}) = verify_prob (toProblem (#1 (parse filename)));

end;
