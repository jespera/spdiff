(* *)

{
  open Genericparser

  exception Error of string

}

rule line = parse
  | ([^'\n']* '\n') as line
      { line }
  | eof
      { exit 0 }

and token = parse
  | [' ' '\t']
      { token lexbuf }
  | '\n'
      { EOL }
  | '('
      { ALEFT }
  | ')'
      { ARIGHT }
  | ','
      { COMMA }
  | '['
      { LBRA }
  | ']'
      { RBRA }
  | ';'
      { SEMI }
  | ('"' (([^'"']*) as txt) '"')
      { QTEXT (txt) }
  | eof
      { exit 0 }
