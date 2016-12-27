
type pos = string -> Coord.t
type svalue = Tokens.svalue
type ('a,'b) token = ('a,'b) Tokens.token
type lexresult = (svalue, pos) token
type arg = string

val pos = ref Coord.init
val eof = fn (fileName : string) => Tokens.EOF (!pos, !pos)

fun incPos n = pos := (Coord.addchar n o (!pos))

fun posTuple n =
  let
    val l = !pos
    val () = incPos n
    val r = !pos
  in
    (l, r)
  end

fun posTupleWith n x =
  let
    val (l, r) = posTuple n
  in
    (x, l, r)
  end

%%
%arg (fileName : string);
%header (functor PmlLexFun (structure Tokens : Pml_TOKENS));
upper = [A-Z];
lower = [a-z];
digit = [0-9];
identChr = [a-zA-Z0-9\'/-];
whitespace = [\ \t];
%%

\n                 => (pos := (Coord.nextline o (!pos)); continue ());
{whitespace}+      => (incPos (size yytext); continue ());
{digit}+           => (Tokens.NUMERAL (posTupleWith (size yytext) (valOf (Int.fromString yytext))));
"//"[^\n]*         => (continue ());


{lower}{identChr}* => (Tokens.VARNAME (posTupleWith (size yytext) yytext));
{upper}{identChr}* => (Tokens.OPNAME (posTupleWith (size yytext) yytext));

.                  => (print ("lexical error: skipping unrecognized character '" ^ yytext ^ "'"); continue ());