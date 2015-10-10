let grow
  stop_grow
  add_res
  ext_cur
  acc cur tail 
  =
  let rec loop acc cur tail =
    match tail with
    | [] -> add_res cur acc
    | ls :: tail -> List.fold_left
        (fun acc y -> 
          let ext = ext_cur y cur in
          if stop_grow ext acc
          then acc
          else loop acc ext tail
        )
        acc ls
  in
  loop acc cur tail

let all_seqs all_subterms =
  if List.length all_subterms = 1
  then List.map (fun x -> [x]) (List.hd all_subterms)
  else 
    let stop ext acc = List.mem ext acc in
    let add_res cur acc = cur :: acc in
    let ext_cur elt cur = elt :: cur in
    let h, t = List.hd all_subterms, List.tl all_subterms in
    List.fold_left (fun acc x ->
      grow stop add_res ext_cur acc [x] t) [] h

let all_patterns all_subterm_seqs =
  if List.length all_subterm_seqs = 1
  then List.map (fun x -> [x]) (List.hd all_subterm_seqs)
  else
    let stop ext acc = List.mem ext acc in
    let add_res cur acc = cur :: acc in
    let ext_cur elt cur = elt :: cur in
    let h, t = List.hd all_subterm_seqs, List.tl all_subterm_seqs in
    List.fold_left (fun acc x ->
      grow stop add_res ext_cur acc [x] t) [] h

									 
let for_some n f ls = 
  let rec loop n ls =
		n = 0 ||
			match ls with
      | x :: xs when f x -> loop (n - 1) xs
      | _ :: xs -> loop n xs
      | [] -> false in
  loop n ls

let (>>) f g x = g @@ (f @@ x)

exception Fail of string

let get_some x =
	match x with
  | None -> raise (Fail "get_some applied to none")
  | Some x -> x
								
let some x = Some x

let defaultArg ifNone opt =
	match opt with
	| None -> ifNone
	| Some x -> x
