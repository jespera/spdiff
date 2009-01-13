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
      | [] -> raise (Fail "get_slices:take_until ")
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
  (* 
     print_endline ("lcs" ^
     List.length src +> string_of_int ^ " " ^
     List.length tgt +> string_of_int);
     print_endline 
     (String.concat ";" (List.map string_of_int src));
     print_endline 
     (String.concat ";" (List.map string_of_int tgt));
  *)
  let slen = List.length src in
  let tlen = List.length tgt in
    if slen = 0 || tlen = 0
    then raise (Fail "no lcs")
    else 
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
    | UP of 'a * 'a

let rec get_diff_nonshared src tgt =
  match src, tgt with
    | [], _ -> List.map (function e -> ADD e) tgt
    | _, [] -> List.map (function e -> RM e) src
    | _, _ -> 
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


(* correlate_diff tries to take sequences of -+ and put them in either
   UP(-,+) or ID. Notice, that permutations of arguments is not
   detected and not really supported in the current framework either
*)

(* sub_list p d takes a list d and returns the prefix-list of d of elements all
 * satisfying p and the rest of the list d
 *)
let sub_list p d =
  let rec loop d =
    match d with
      | [] -> [], []
      | x :: xs -> 
          if p x 
          then 
            let nxs, oxs = loop xs in
              x :: nxs, oxs
          else [], x :: xs
  in
    loop d

let rec correlate rm_list add_list =
  match rm_list, add_list with
    | [], [] -> []
    | [], al -> al
    | rl, [] -> rl
    | RM r :: rl, ADD a :: al ->
        let u = if r = a then ID a else UP(r,a) 
        in
          u :: correlate rl al
    | _ -> raise (Fail "correleate")
	
(* the list of diffs returned is not in the same order as the input list
*)
let correlate_diffs d =
  let rec loop d =
    match d with
      | [] -> [], []
      | RM a :: d -> 
          let rm_list, d = sub_list 
            (function x -> match x with 
              | RM _ -> true 
	      | _ -> false) ((RM a) :: d) in
          let add_list, d = sub_list
            (function x -> match x with 
              | ADD _ -> true 
              | _ -> false) d in
          let ups' = correlate rm_list add_list in
          let ups, d' = loop d in
            ups' @ ups , d'
      | x :: d -> match loop d with up, d' -> up, x :: d' in
  let rec fix_loop (ups, d_old) d =
    let ups_new, d_new = loop d in
      if d_new = d_old
      then ups_new @ ups, d_new
      else fix_loop (ups_new @ ups, d_new) d_new
  in
  let n, o = fix_loop ([], []) d in
    n @ o

let malign s1 s2 s3 = 
  let rec get_list e s = match s with
    | [] -> raise (Fail "get_list")
    | e' :: s when e = e' -> s
    | _  :: s -> get_list e s in
  let rec subseq s1 s2 = s1 = [] || match s1 with
    | [] -> true
    | e :: s1 -> try let s' = get_list e s2 in subseq s1 s' with _ -> false
  in
  let rec loop s1 s2 s3 = 
    match s1, s2, s3 with
      | s1, [], [] -> true (* the rest of s1 was deleted *)
      | [], [], s3 -> true (* the rest of s3 was added *)
      | [], _ , _  -> subseq s2 s3 (* s2 adds elems iff it is a subseq of s3 *)
      | e1 :: s1', e2 :: s2', e3 :: s3' -> 
          (* movement vectors: *)
          (** 1,1,1 => no change *)
          (e1 = e2 && e2 = e3 && loop s1' s2' s3') ||
            (** 1,1,0 => either e1,e2 was removed or changed *)
            (e1 = e2 && (loop s1' s2' s3 || loop s1' s2' s3')) ||
            (** 1,0,0 => e1 was removed *)
            (loop s1' s2 s3) ||
            (** 0,1,1 => e2 = e3 is a new elem *)
            (e2 = e3 && loop s1 s2' s3') ||
            (** 0,0,1 => e3 is a new elem *)
            (loop s1 s2 s3')
      | _, _, _ -> false
  in
    loop s1 s2 s3

type gterm = 
    | A of string * string
    | C of string * (gterm list)

let part_of gt1 gt2 gt3 =
  gt1 = gt2 || gt2 = gt3 || match gt1, gt2, gt3 with
    | C(t1,gts1), C(t2,gts2), C(t3, gts3) when t1 = t2 || t2 = t3 ->
	malign gts1 gts2 gts3
    | _ -> false

let rec flatten_tree gt = 
  match gt with 
    | A _ -> [gt]
    | C(_, gts) -> gt :: List.fold_left (fun acc gt -> flatten_tree gt @ acc) [] gts

let get_tree_changes gt1 gt2 = 
  let s1 = flatten_tree gt1 in
  let s2 = flatten_tree gt2 in
    patience_diff s1 s2 +>
      correlate_diffs +>
      List.filter (function u -> match u with UP _ -> true | _ -> false)

let f = A("id","f")
let x = A("id","x")
let g = A("id","g")
let h = A("id","h")
let x'= A("id","x'")
let y = A("id","y")
let z = A("id","z")
let fx = C("call",[f;x])
let fx' = C("call",[f;x'])
let hfg = C("call",[h;fx;g])
let hf'g = C("call",[h;fx';g])
let hyzf'g = C("call",[h;y;z;fx';g])

