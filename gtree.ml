(* A('t,'c) is an atom with content 'c and type 't while C('t,alist)
   is a node of type 't with arguments "alist"
*)

open Hashcons

type gtree = gtree_node hash_consed
and gtree_node =
    | A of string * string
    | C of string * gtree list

module Gtree_node = struct
  type t = gtree_node
  let equal t1 t2 = match t1, t2 with
  | A (t1,v1), A (t2,v2) -> t1 = t2 && v1 = v2
  | C (t1,ts1), C (t2,ts2) when 
      List.length ts1 = List.length ts2 -> t1 = t2 &&
      List.for_all2 (fun t t' -> t == t') ts1 ts2
  | _ -> false
  let hash = function
    | A (t, v) -> abs(19 * (Hashtbl.hash t + Hashtbl.hash v))
    | C (t,ts) -> abs(List.fold_left (fun acc_k t' -> 
        19 * (t'.hkey + acc_k)
        ) (Hashtbl.hash t) ts)
end

module HGtree = Make(Gtree_node)

let termht = HGtree.create 100313

let view t = t.node
let hcons t = HGtree.hashcons termht t

let mkA (a,b) = hcons (A(a,b))
let mkC (a,ts) = hcons (C(a,ts))

let rec occurs_loc small large =
  small == large ||
  (match view large with
    | C(ct, ts) -> List.exists (function t -> occurs_loc small t) ts
    | _ -> false
  )

let embedded a b =
  occurs_loc a b || occurs_loc b a

let rec gsize t =
  match view t with
  | A ("meta", _) -> 0
  | A _ -> 1
  | C ("TYPEDEXP", _) -> 0
  | C(ct, ts) -> 1 + List.fold_left 
      (fun a b -> a + gsize b) 1 ts

let rec zsize t =
  match view t with
  | A ("meta", _) -> 0
  | A (at, ac) -> 1 (* String.length ac *)
  | C ("TYPEDEXP", [ft;id]) -> zsize ft + zsize id
  | C(ct, ts) -> 1 + List.fold_left 
      (fun a b -> a + zsize b) 1 ts

let rec gdepth t =
  match view t with
  | A _ -> 0
  | C(ct, ts) -> List.fold_left
      (fun a b -> max a (gdepth b)) 1 ts


exception Found_leaf
(* returns true iff t does not contain any leaves *)
let no_leaves t = 
  let rec loop t = match view t with
    | A("meta",_) -> ()
    | A(_,_) -> raise Found_leaf
    | C(_,ts) -> List.iter loop ts;
  in
    try 
      begin 
	loop t;
	true
      end
    with Found_leaf -> false
