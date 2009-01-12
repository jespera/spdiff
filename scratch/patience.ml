(* patience based diff *)

exception Fail of string

let (+>) o f = f o

let patience nums =
  let rec (>>) stacks n = 
    match stacks with 
    | [] -> [[n]]
    | (n' :: stack) :: stacks when n < n' -> (n :: n' :: stack) :: stacks
    | stack :: stacks  -> stack :: (stacks >> n)
    in
    List.fold_left (>>) [] nums
   
let get_unique ls =
  let rec loop acc ls = match ls with
  | [] -> acc
  | e :: ls when List.mem e ls -> loop (e :: acc) ls
  | _ :: ls -> loop acc ls in
  let dupl = loop [] ls in
  List.filter (function e -> not(List.mem e dupl)) ls

let get_common_unique ls1 ls2 =
  let uniq1 = get_unique ls1 in
  get_unique ls2 
  +> List.filter (function u2 -> List.mem u2 uniq1)

let patience_ref nums =
  let get_rev_index ls = List.length ls in
  let lookup_rev i ls = List.length ls - i +> List.nth ls  in
  let insert left e ls = match left with
  | None -> (None, e) :: ls
  | Some (stack) -> (Some (get_rev_index stack), e) :: ls in
  let (<) n n' = n < (snd n') in
  let (>>) stacks n = 
    let rec loop left stacks n =
      match stacks with 
      | [] -> [insert left n []]
      | (n' :: stack) :: stacks when n < n' -> (insert left n (n' :: stack)) :: stacks
      | stack :: stacks  -> stack :: (loop (Some stack) stacks n)
    in loop None stacks n
  in
  let stacks = List.fold_left (>>) [] nums in
  (* get the lcs *)
  let rec lcs acc_lcs id remaining_stacks =
    match remaining_stacks with
    | [] -> acc_lcs
    | stack :: stacks ->
        let (nid_opt, e) = lookup_rev id stack in
        (match nid_opt with 
        | None -> e :: acc_lcs
        | Some nid -> lcs (e :: acc_lcs) nid stacks)
  in
  match List.rev stacks with
  | [] -> []
  | [(_, e) :: stack] -> [e]
  | ((Some nid, e) :: _) :: stacks -> lcs [e] nid stacks
  
let patience_sort nums =
  let stacks = patience nums in
  let is_min x stacks =
    List.for_all (function xs -> match xs with 
    | [] -> true
    | y :: _ -> x < y) stacks in
  let rec get_min stacks = 
    match stacks with
    | [] -> None
    | [] :: stacks -> get_min stacks
    | (x :: xs) :: stacks when is_min x stacks -> Some (x, xs :: stacks)
    | xs :: stacks -> (match get_min stacks with
        | None -> Some(List.hd xs, List.tl xs :: stacks)
        | Some (n, stacks) -> Some(n, xs :: stacks))
  in
  let rec loop stacks =
    match get_min stacks with
    | None -> []
    | Some(x, nstacks) -> (
      print_endline (string_of_int x);
      x :: loop nstacks)
  in loop stacks

let slice_list (start_e, end_e) ls =
  let rec drop ls =
    match ls with 
    | [] -> raise (Fail "slice_list : drop")
    | e :: ls when e = start_e -> take ls
    | _ :: ls -> drop ls
  and take ls =
    match ls with
    | [] -> raise (Fail "slice_list : take")
    | e :: ls when e = end_e -> []
    | e :: ls -> e :: take ls
  in drop ls

let get_slices lcs ls =
  let take_until e ls =
    let rec loop acc ls = match ls with
    | [] -> raise (Fail ("get_slices:take_until " ^ string_of_int e))
    | e' :: ls when e = e' -> List.rev acc, ls
    | e' :: ls -> loop (e' :: acc) ls
    in loop [] ls
  in
  let rec loop lcs ls =
    match lcs with
    | [] -> [ls]
    | e :: lcs -> let slice, ls = take_until e ls in slice :: loop lcs ls
  in loop lcs ls

let lcs src tgt =
  let slen = List.length src in
  let tlen = List.length tgt in
  let m    = Array.make_matrix (slen + 1) (tlen + 1) 0 in
    Array.iteri (fun i jarr -> Array.iteri (fun j e -> 
      let i = if i = 0 then 1 else i in
      let j = if j = 0 then 1 else j in
      let s = List.nth src (i - 1) in
      let t = List.nth tgt (j - 1) in
	if s = t
	then
	  m.(i).(j) <- (try m.(i-1).(j-1) + 1 with _ -> 1)
	else 
	  let a = try m.(i).(j-1) with _ -> 0 in
	  let b = try m.(i-1).(j) with _ -> 0 in
	    m.(i).(j) <- max a b
    ) jarr) m;
    m

type 'a diff_elem = 
  | ID of 'a
  | RM of 'a
  | ADD of 'a

let rec get_diff_nonshared src tgt =
  let m = lcs src tgt in
  let slen = List.length src in
  let tlen = List.length tgt in
  let rec loop i j =
    (*     print_endline ("i,j = " ^ string_of_int i ^ "," ^ string_of_int j); *)
    if i > 0 && j > 0 && List.nth src (i - 1) = List.nth tgt (j - 1)
      (*if i > 0 && j > 0 && *)
      (*embedded (List.nth src (i - 1)) (List.nth tgt (j - 1))*)
    then
      loop (i - 1) (j - 1) @ [ID (List.nth src (i - 1))]
    else if j > 0 && (i = 0 || m.(i).(j - 1) >= m.(i - 1).(j))
    then 
      loop i (j - 1) @ [ADD (List.nth tgt (j - 1))]
    else if 
        i > 0 && (j = 0 || m.(i).(j - 1) < m.(i - 1).(j))
    then 
      loop (i - 1) j @ [RM (List.nth src (i - 1))]
    else (assert(i=j && j=0) ;
	  []) (* here we should have that i = j = 0*)
  in loop slen  tlen

let rec patience_diff ls1 ls2 =
  let lcs = get_common_unique ls1 ls2 +> patience_ref in
  if lcs = []
  then (* ordinary diff *) 
    get_diff_nonshared ls1 ls2
  else 
    let slices1 = get_slices lcs ls1 in
    let slices2 = get_slices lcs ls2 in
    let diff_slices = List.map2 patience_diff slices1 slices2 in
    let rec merge_slice lcs dslices = match dslices with
    | [] -> []
    | diff :: dslices -> diff @ merge_lcs lcs dslices
    and merge_lcs lcs dslices = match lcs with
    | [] -> (match dslices with
      | [] -> []
      | [diff] -> diff
      | _ -> raise (Fail "merge_lcs : dslice not singular"))
    | e :: lcs -> ID e :: merge_slice lcs dslices
    in merge_slice lcs diff_slices

let sa = [1;2;3;4;5;6;7;8;9;10;11;12;13;14]
let sb = [10;4;1;10;13;15]

let s1 = [1;2;3;2;4]
let s2 = [2;1;1;2;3;2]
