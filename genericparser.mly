%{
  open Gtree
%}

%token ALEFT ARIGHT
%token COMMA SEMI EOL
%token LBRA RBRA
%token <string> QTEXT
%start <Gtree.gtree> main

%%

main:
| t = term EOL
    { t }
    
term:
| ALEFT t1 = QTEXT COMMA t2 = QTEXT ARIGHT
    { mkA (t1, t2) }
| ALEFT t1 = QTEXT COMMA ls = termlist ARIGHT
	{ mkC (t1,ls) }

termlist:
| LBRA ts = terms RBRA
	{ ts }

terms:
|
    { [] }
| t = term
    { [t] }
| t = term SEMI ts = terms
	{ t :: ts }
