(*
* Copyright 2005-2009, Ecole des Mines de Nantes, University of Copenhagen
* Yoann Padioleau, Julia Lawall, Rene Rydhof Hansen, Henrik Stuart, Gilles Muller, Jesper Andersen
* This file is part of Coccinelle.
* 
* Coccinelle is free software: you can redistribute it and/or modify
* it under the terms of the GNU General Public License as published by
* the Free Software Foundation, according to version 2 of the License.
* 
* Coccinelle is distributed in the hope that it will be useful,
* but WITHOUT ANY WARRANTY; without even the implied warranty of
* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
* GNU General Public License for more details.
* 
* You should have received a copy of the GNU General Public License
* along with Coccinelle.  If not, see <http://www.gnu.org/licenses/>.
* 
* The authors reserve the right to distribute this or future versions of
* Coccinelle under other licenses.
*)


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
