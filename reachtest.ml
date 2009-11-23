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


let f = "f"
  
let g = "g"
  
let h = "h"
  
let m = "m"
  
let p = "+"
  
let x = "x"
  
let i = "i"
  
let is = "stmti"
  
type node = | GNode of string list

let make_node n = GNode [ n ]
  
let make_entry (n, ns) = ((make_node n), (List.map make_node ns))
  
let pg1 =
  [ make_entry (is, [ f; g; h; m; p; x; i ]);
    make_entry (i, [ f; g; h; m; p; x; is ]); make_entry (f, [ g; h; m; p ]);
    make_entry (p, [ g; h ]); make_entry (g, []); make_entry (h, []);
    make_entry (m, []); make_entry (x, []) ]
  
let string_of_node = function | GNode ns -> String.concat ";" ns
  
let rec string_of_graph g =
  match g with
  | [] -> ""
  | (n, ns) :: g ->
      "(" ^
        ((string_of_node n) ^
           (", [" ^
              ((String.concat ", " (List.map string_of_node ns)) ^
                 ("])\n" ^ (string_of_graph g)))))
  
let equal_nodes =
  function
  | GNode ns ->
      (function
       | GNode ns' ->
           (List.for_all (fun n -> List.mem n ns') ns) &&
             (List.for_all (fun n -> List.mem n ns) ns'))
  
(* returns the sublist for a given node *)
let rec graph_assoc g n =
  match g with
  | [] -> raise Not_found
  | (n', ns) :: g when equal_nodes n n' -> ns
  | _ :: g -> graph_assoc g n
  
(* determines whether there is an arch from node n to node n' -- * i.e.    *)
(* whether n' is a subpatch of n                                           *)
let is_reachable g n n' =
  try
    let ns = graph_assoc g n
    in List.exists (fun n'' -> equal_nodes n' n'') ns
  with | _ -> raise Not_found
  
(* determines whether there is a cyclic dependency between node n and n' *)
let is_cyclic_nodes g n n' = (is_reachable g n n') && (is_reachable g n' n)
  
(* determine that the nodes in n' is a subset of the ones in n *)
let subset_nodes =
  function
  | GNode ns' ->
      (function | GNode ns -> List.for_all (fun n -> List.mem n ns) ns')
  
let rec graph_assoc_group g n =
  match g with
  | [] -> raise Not_found
  | (n', ns) :: g when subset_nodes n n' -> ns
  | _ :: g -> graph_assoc_group g n
  
let is_reachable_group g n n' =
  try
    let ns = graph_assoc_group g n
    in List.exists (fun n'' -> subset_nodes n' n'') ns
  with | _ -> raise Not_found
  
let rec group_of_node g n =
  match g with
  | [] -> raise Not_found
  | (n', _) :: g when subset_nodes n n' -> n'
  | _ :: g -> group_of_node g n
  
(* remove a node *)
let rec rm_node g n =
  match g with
  | [] -> raise Not_found
  | (n', _) :: g when equal_nodes n n' -> g
  | e :: g -> e :: (rm_node g n)
  
let truncate_node cs =
  let rec loop acc cs =
    match cs with | [] -> GNode acc | GNode ns :: cs -> loop (ns @ acc) cs
  in loop [] cs
  
let rec rm_list ls e =
  match ls with
  | [] -> raise Not_found
  | e' :: ls when e' = e -> ls
  | e' :: ls -> e :: (rm_list ls e)
  
(* after compressing cycles node lists for nodes may point to single nodes *)
(* * instead of the grouped ones; this functions change node lists such    *)
(* that they * point to the groups instead and removes possible duplicate  *)
(* entries                                                                 *)
let remap_nodes g =
  let rec loop g' =
    match g' with
    | [] -> []
    | (n, ns) :: g' ->
        let ns' =
          List.fold_left
            (fun acc_ns n' ->
               if List.mem n' acc_ns then acc_ns else n' :: acc_ns)
            [] (List.map (group_of_node g) ns)
        in (n, ns') :: (loop g')
  in loop g
  
(* ensure that there are no cycles in the graph by putting those together  *)
(* which * are cyclically dependend; assumes that no nodes have been       *)
(* collapsed at the * beginning so that each GNode is a singleton          *)
let rec compress_cycles' g =
  match g with
  | [] -> []
  | (n, ns) :: g' ->
      let cs =
        List.fold_left
          (fun acc_cs (n', ns') ->
             if is_cyclic_nodes g n n' then n' :: acc_cs else acc_cs)
          [] g' in
      let res =
        compress_cycles'
          (List.fold_left (fun acc_g c -> rm_node acc_g c) g' cs) in
      let ns' = List.filter (fun n'' -> not (List.mem n'' cs)) ns
      in ((truncate_node (n :: cs)), ns') :: res
  
let compress_cycles g = remap_nodes (compress_cycles' g)
  
(* assumes no (self) loops exists; also there can be only one top *)
let find_top g =
  let rec loop g' =
    match g' with
    | [] -> raise Not_found
    | (n, ns) :: g' ->
        if List.exists (fun (n', ns') -> is_reachable g n' n) g
        then loop g'
        else (n, ns)
  in loop g
  
(* this function (assuming g contains no cycles) turns a graph into        *)
(* compact * form; in compact form there are only edges that are not also  *)
(* expressible by * transitive closure                                     *)
let compact_graph g =
  let rec loop g' =
    match g' with
    | [] -> []
    | (n, ns) :: g' ->
        (n,
         (List.filter
            (fun n' ->
               List.for_all
                 (fun n'' ->
                    if not (equal_nodes n' n'')
                    then not (is_reachable g n'' n')
                    else true)
                 ns)
            ns)) ::
          (loop g')
  in loop g
  
(* generate all solutions given a graph this function turns makes a string *)
(* representing the graph in dot format                                    *)
let dot_of_graph g =
  let prefix = "digraph g {\n" in
  let suffix = "}" in
  let make_node n = "\"" ^ ((string_of_node n) ^ "\"") in
  let rec loop g' =
    match g' with
    | [] -> ""
    | (n, []) :: g' -> loop g'
    | (n, ns) :: g' ->
        (String.concat ";\n"
           (List.map (fun n' -> (make_node n) ^ ("->" ^ (make_node n'))) ns))
          ^ (";\n" ^ (loop g'))
  in prefix ^ ((loop g) ^ suffix)
  
(* merge code follows below *)
type term = | T of string * term list | M of term

exception Merge3 of term * term * term
  
let fold_left3 f acc t1 t2 t3 =
  let rec loop acc t1 t2 t3 =
    match (t1, t2, t3) with
    | ([], [], []) -> acc
    | (t1 :: ts1, t2 :: ts2, t3 :: ts3) -> loop (f acc t1 t2 t3) ts1 ts2 ts3
  in loop acc t1 t2 t3
  
let rec merge3 t1 t2 t3 =
  let m3 acc t1 t2 t3 = (merge3 t1 t2 t3) && acc
  in
    (t2 = t3) ||
      ((t1 = t2) ||
         (match (t1, t2, t3) with
          | (T (ct1, ts1), T (ct2, ts2), T (ct3, ts3)) when
              (ct1 = ct2) || (ct2 = ct3) -> fold_left3 m3 true ts1 ts2 ts3
          | (_, _, _) -> false))
  
exception Merge2 of term * term
  
(* invariant: t_tgt is the intended target, it should not contain marks; * *)
(* t_new is the middelterm which will contain marks                        *)
let rec merge2 t_new t_tgt =
  let m2 acc t1 t2 = (merge2 t1 t2) :: acc
  in
    match (t_new, t_tgt) with
    | (M t, t') when t = t' -> t
    | (M t, t') when not (t = t') -> raise (Merge2 (t_new, t_tgt))
    | (T (ct_n, ts_n), T (ct_t, ts_t)) when ct_n = ct_t ->
        T (ct_n, List.rev (List.fold_left2 m2 [] ts_n ts_t))
    | (_, _) -> t_tgt
  
let one = T ("int-1", [])
  
let two = T ("int-2", [])
  
let thr = T ("int-3", [])
  
let f = T ("id-f", [])
  
let x = T ("id-x", [])
  
let i = T ("id-i", [])
  
let ( @@ ) f args = T ("@", f :: args)
  
let fc = f @@ [ one ]
  
let xc = x @@ [ one ]
  
let ic = i @@ [ fc; xc ]
  
let mfc' = f @@ [ M two ]
  
let mxc' = x @@ [ M thr ]
  
let fc' = f @@ [ two ]
  
let xc' = x @@ [ thr ]
  
let micf = i @@ [ mfc'; xc ]
  
let micx = i @@ [ fc; mxc' ]
  
let icfx =
  (i @@ [ fc'; xc' ];
   print_endline (dot_of_graph (compact_graph (compress_cycles pg1))))
  
