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



let rec prefix a lists =
(*print_endline ("prefixing " ^*)
(*string_of_gtree str_of_ctype str_of_catom a);*)
match lists with(*{{{*)
| [] -> []
| lis :: lists -> (a :: lis) :: prefix a lists(*}}}*)

let rec prefix_all lis lists =
	match lis with(*{{{*)
  | [] -> []
	| elem :: lis -> (prefix elem lists) @ prefix_all lis lists(*}}}*)
			
let rec gen_perms lists =
  print_string "gen_perms sizes: ";
  List.iter (fun ec -> 
    print_string "<";
    print_string (string_of_int (List.length ec));
    print_string "> ";
    ) lists;
  print_newline ();
  assert(not(List.exists ((=) []) lists));
match lists with(*{{{*)
| [] -> [[]]
| lis :: lists -> prefix_all lis (gen_perms lists)(*}}}*)

let tv = [[1];[2]]
