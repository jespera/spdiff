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


(* global configuration used everywhere *)

let verbose = ref false
let print_abs = ref false
let read_generic = ref false
let useless_abs = ref false
let to_print = ref false

let (+>) o f = f o

let for_some n f ls = 
  let rec loop n ls =
    n = 0 ||
    match ls with
      | x :: xs when f x -> loop (n - 1) xs
      | _ :: xs -> loop n xs
      | [] -> false in
    loop n ls

let counter_tick counter total =
  begin
    ANSITerminal.save_cursor ();
    ANSITerminal.print_string 
      [ANSITerminal.on_default](
	counter +> string_of_int 
	^ "/" ^	total +> string_of_int);
    ANSITerminal.restore_cursor();
    flush stdout;
  end

