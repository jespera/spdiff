(* Align three sequences of equal lenth such that for all elements, either e1=e2
 * or e2=e3
 *)

exception Fail of string

let checkAlignment s1 s2 s3 =
  let rec loop s1 s2 s3 =
    match s1, s2, s3 with
    | [], [], [] -> true
    | e1 :: s1', e2 :: s2', e3 :: s3' when e1 = e2 || e2 = e3 -> loop s1' s2' s3'
    | _ -> raise (Fail "checkAlignment")
  in
  loop s1 s2 s3

let (+>) x f = f x

exception Matching of string list * string list * string list 

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

let s1 = ["a";"b";"c";"d"]
let s2 = ["a";"b";"c'"]
let s3 = ["a'";"c'"]

let s11 = ["a";"b"]
let s13 = ["a'";"b'"]
let s12 = ["a'";"b"]
