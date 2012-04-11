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


open Gtree

type 'a diff = 
  | PENDING_ID of 'a
  | PENDING_RM of 'a
  | ID of 'a 
  | ADD of 'a 
  | RM of 'a 
  | UP of 'a * 'a
  | SEQ of 'a diff * 'a diff

let rec csize bp = match bp with
| UP(t1,t2) -> zsize t1 + zsize t2
| SEQ(p1,p2) -> csize p1 + csize p2

let fsize bp = match bp with
  | UP(t,_) -> zsize t

let rec string_of_difftype f = function
  | PENDING_ID a -> "?= " ^ f a
  | PENDING_RM a -> "?- " ^ f a
  | ID a         -> "   " ^ f a
  | ADD a        -> "+  " ^ f a
  | RM a         -> "-  " ^ f a
  | UP (a, a')   -> f a ^ " -> " ^ f a'
  | SEQ (ad, ad')-> string_of_difftype f ad ^ "; " ^ string_of_difftype f ad'

