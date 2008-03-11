(* A('t,'c) is an atom with content 'c and type 't while C('t,alist)
   is a node of type 't with arguments "alist"
*)

type ('t, 'c) gtree = 
    | A of 't * 'c
    | C of 't * (('t, 'c) gtree list)

let rec occurs_loc small large =
  small = large ||
  (match large with
    | C(ct, ts) -> List.exists (function t -> occurs_loc small t) ts
    | _ -> false
  )

let embedded a b =
  occurs_loc a b || occurs_loc b a

let rec gsize t =
  match t with
  | A ("meta", _) -> 0
  | A _ -> 1
  | C(ct, ts) -> 1 + List.fold_left 
      (fun a b -> a + gsize b) 1 ts

let rec gdepth t =
  match t with
  | A _ -> 0
  | C(ct, ts) -> List.fold_left
      (fun a b -> max a (gdepth b)) 1 ts


