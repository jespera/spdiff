let debug = false
let debug_msg x = if debug then print_endline x else ()
let fdebug_string f x = if f then print_string x else ()
let fdebug_endline f x = if f then print_endline x else ()
let debug_newline () = if debug then print_newline () else ()

exception Fail of string

open Gtree
open Db
open Difftype

type term = (string, string) gtree
type up = term diff

exception Merge3

module GT =
struct
  type t = (string, string) gtree
  let compare = Pervasives.compare
end

module DiffT =
struct
  (*type t = (((string,string) gtree) diff) list*)
  type t = ((string,string) gtree) diff
  let compare = Pervasives.compare
end


let ht = Hashtbl.create (591)

(*
 *module DiffT =
 *  struct
 *    type t = ((string,string) gtree) diff
 *    let compare = Pervasives.compare
 *  end
 *
 *)
module DBM = Db(GT)
module DBD = Db(DiffT)

(* user definable references here ! *)
(* terms are only abstracted until we reach this depth in the term *)
let abs_depth     = ref 0 
  (* (sub)terms of a term are only abstracted if they are smaller than this number
  *)
let abs_threshold = ref 0
  (* only allow abstraction of subterms of terms that are smaller than this number
  *)
let abs_subterms  = ref 0
  (* the FV of rhs should be equal to lhs -- thus lhs can not drop metavars under
   * strict mode
   *)
let be_strict     = ref false 
  (* allow the same term to be abstracted by different metavariables
  *)
let use_mvars     = ref false
  (* should we really use the fixed information to prevent terms from getting
   * abstracted
   *)
let be_fixed      = ref false
  (* not used atm: should have indicated the number of allow exceptions as to how
   * often a patch should be found
   *)
let no_exceptions = ref 0
let no_occurs = ref 0
  (* should we be printing the derived abstract updates during inference
  *)
let print_abs = ref false
  (* should we allow non-matching parts to be safe? 
  *)
let relax = ref false
(* copy of the main.ml var with the same name; initialized in main.ml *)
let do_dmine = ref false

(* check that list l1 is a sublist of l2 *)
let subset_list l1 l2 =
  List.for_all (function e1 -> (List.mem e1 l2)) l1


let rec string_of_gtree str_of_t str_of_c gt = 
  let rec string_of_itype itype = (match itype with
  | A("itype", c) -> "char"
  | C("itype", [sgn;base]) ->
    (match sgn, base with
    | A ("sgn", "signed") , A (_, b) -> b
    | A ("sgn", "unsigned"), A (_, b) -> "unsigned" ^ " " ^ b
    | A ("meta", _), A(_, b) -> b
    )) 
  and string_of_param param =
    match param with
    | C("param", [reg;name;ft]) ->
        let r = match reg with 
          | A("reg",r) -> r
          | A("meta",x0) -> x0 in
        let n = match name with
          | A("name", n) -> n
          | A("meta", x0) -> x0 in
        "(" ^ r ^ " " ^ n ^ ":" ^ string_of_ftype [ft] ^ ")"
    | gt -> loop gt
  and string_of_ftype fts = 
    let loc cvct = match cvct with
    | A("tqual","const") -> "const"
    | A("tqual","vola")  -> "volatile"
    | A("btype","void")  -> "void"
    | C("btype", [C("itype", _) as c])   -> string_of_itype c
    | C("btype", [A("itype", _) as a])   -> string_of_itype a
    | C("btype", [A("ftype", ft)]) -> ft
    | C("pointer", [ft]) -> "*" ^ string_of_ftype [ft]
    | C("array", [cexpopt; ft]) ->
        string_of_ftype [ft] ^ " " ^
        (match cexpopt with
        | A("constExp", "none") -> "[]"
        | C("constExp", [e]) -> "[" ^ loop e ^ "]"
    | A("meta", x0) -> x0
        )
    | C("funtype", rt :: pars) -> 
        let ret_type_string = string_of_ftype [rt] in
        let par_type_strings = List.map string_of_param pars in
        "("^ 
        String.concat "**" par_type_strings 
        ^ ")->" ^ ret_type_string
    | C("enum", [A ("enum_name", en); enumgt]) -> "enumTODO"
    | C("struct", [C(sname, [stype])]) -> 
        "struct " ^ sname ^ "{" ^ loop stype ^"}"
    | A ("struct", name) -> "struct " ^ name
    | t -> loop t
    | C(tp,ts) -> tp ^ "<" ^ String.concat ", " (List.map loop ts) ^ ">"
    | A(tp,t) -> tp ^ ":" ^ t ^ ":"
    in
    String.concat " " (List.map loc fts)
  and loop gt =
    match gt with
      | A ("meta", c) -> c
      | A ("itype", _) -> string_of_itype gt
      | A (t,c) -> c
      | C ("fulltype", ti) -> string_of_ftype ti
      | C ("const", [A(_, c)]) -> c
      | C ("itype", _ ) -> string_of_itype gt
      | C ("exp", [e]) -> loop e
      | C ("exp", [A("meta", x0); e]) -> "(" ^ loop e ^ ":_)"
      | C ("exp", [C ("TYPEDEXP", [t]) ; e]) -> 
          "(" ^ loop e ^ ":" ^ loop t ^ ")"
      | C ("call", f :: args) -> 
          loop f ^ "(" ^ String.concat "," (List.map loop args) ^ ")"
      | C ("binary_arith", [A("aop",op_str) ;e1;e2]) ->
          loop e1 ^ op_str ^ loop e2
      | C ("binary_logi", [A("logiop", op_str); e1;e2]) ->
          loop e1 ^ op_str ^ loop e2
      | C (t, gtrees) -> 
          str_of_t t ^ "[" ^
            String.concat "," (List.map loop gtrees)
          ^ "]"
  in
    loop gt

let str_of_ctype x = x
let str_of_catom a = a


let rec string_of_diff d =
  match d with
    | SEQ(p1,p2) -> "SEQ:  " ^ string_of_diff p1 ^ " ; " ^ string_of_diff p2
    | ID s -> "ID:  " ^ string_of_gtree str_of_ctype str_of_catom s
    | UP(s,s') -> 
	(string_of_gtree str_of_ctype str_of_catom s) ^ 
	  " ==> " ^
	  (string_of_gtree str_of_ctype str_of_catom s')
    | ADD s -> "ADD:  " ^ string_of_gtree str_of_ctype str_of_catom s
    | RM s -> "RM:  " ^ string_of_gtree str_of_ctype str_of_catom s

let string_of_gtree' = string_of_gtree str_of_ctype str_of_catom

(* a solution is a list of updates, diff list and the idea is that it will
 * transform an original gt into the updated gt' *)
let print_sol sol =
  print_endline "[[";
  List.iter (function dg ->
    print_endline (string_of_diff dg);
    print_endline "\t++"
  ) sol;
  print_endline "]]"


let print_sols solutions =
  (*List.iter print_sol solutions*)
  print_sol solutions

let explode st =
  let rec loop i acc =
    if i = 0 
    then acc
    else 
      let i' = i-1 in 
	loop i' (st.[i'] :: acc) in
    List.map Char.escaped (loop (String.length st) [])
      
let spacesep st =
  Str.split (Str.regexp "[ ]+") st

let subset lhs rhs =
  List.for_all (function e -> List.mem e rhs) lhs

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

let rm_dub ls =
  (*List.rev *)
  (List.fold_left
      (fun acc e -> if List.mem e acc then acc else e :: acc)
      [] ls)

let lcs_shared size_f src tgt =
  let slen = List.length src in
  let tlen = List.length tgt in
  let m    = Array.make_matrix (slen + 1) (tlen + 1) 0 in
    Array.iteri (fun i jarr -> Array.iteri (fun j e -> 
      (* make sure we stay within the boundaries of the matrix *)
      let i = if i = 0 then 1 else i in
      let j = if j = 0 then 1 else j in
	(* get the values we need to compare in s and t *)
      let s = List.nth src (i - 1) in
      let t = List.nth tgt (j - 1) in
	(* now see how much of s and t is shared *)
      let size = size_f s t in
	if size > 0 
	then
	  (* some parts of s and t were equal *)
	  m.(i).(j) <- (try m.(i-1).(j-1) + size with _ -> size)
	else 
	  let a = try m.(i).(j-1) with _ -> 0 in
	  let b = try m.(i-1).(j) with _ -> 0 in
	    m.(i).(j) <- max a b
    ) jarr) m; (*
		 print_endline "M:";
		 Array.iteri (fun i jarr ->
		 print_string "[";
		 Array.iteri (fun j e ->
		 print_string ((string_of_int m.(i).(j)) ^ " ")
		 ) jarr;
		 print_endline "]";
		 ) m; *)
    m

let rec shared_gtree t1 t2 =
  let localeq a b = if a = b then 1 else 0 in
  let rec comp l1 l2 =
    match l1, l2 with
      | [], _ | _, [] -> 0
	  (* below: only do shallow comparison *)
	  (*| x :: xs, y :: ys -> localeq x y + comp xs ys in*)
      | x :: xs, y :: ys -> shared_gtree x y + comp xs ys in
    match t1, t2 with
      | A (ct1, at1), A (ct2, at2) -> 
	  localeq ct1 ct2 + localeq at1 at2
      | C(ct1, ts1), C(ct2, ts2) ->
	  localeq ct1 ct2 + comp ts1 ts2
      | _, _ -> 0

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

let rec get_diff src tgt =
  let m = lcs_shared shared_gtree src tgt in
  let slen = List.length src in
  let tlen = List.length tgt in
  let rec loop i j =
    (*     print_endline ("i,j = " ^ string_of_int i ^ "," ^ string_of_int j); *)
    let i' = if i > 0 then i else 1 in
    let j' = if j > 0 then j else 1 in
      (*print_endline ("d: "^ string_of_int i' ^", " ^ string_of_int j');*)
    let s = List.nth src (i' - 1) in
    let t = List.nth tgt (j' - 1) in
      (*print_endline "d";*)
      if i > 0 && j > 0 && (shared_gtree s t > 0)
	(*&& (List.nth src (i - 1)) = (List.nth tgt (j - 1))*)
	(*if i > 0 && j > 0 && *)
	(*embedded (List.nth src (i - 1)) (List.nth tgt (j - 1))*)
      then
	let up = if s = t then ID s else UP(s,t) in
	  (*loop (i - 1) (j - 1) @ [ID (List.nth src (i - 1))]*)
	  loop (i - 1) (j - 1) @ [up]
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


(*
  Either there is a conflict and we return the super-tree (this is the
  overapproximation we take atm) as the result of the make_diff or there is not
  a conflict in which case we must identify the change in the list of changes,
  return that as the result of make_diff. If there was no change, the identity
  update is returned. Two updates (s,t) (s',t') does NOT conflict iff
  (s,t) = (s',t') OR
  make_diff (s,t) = make_diff (s',t')
*)

  (* occurs s l checks whether s occurs as a subterm of l; it is used to check for
   * conflicting updates; TODO extened to also handle meta variables
   *)
let rec occurs small large =
  small = large ||
  (match large with
    | C(ct, ts) -> List.exists (function t -> occurs small t) ts
    | _ -> false
  )

let (<==) a b = occurs a b

(* this function is too coarse; it fails to realise some cases when there is
 * no_conflict TODO
 *)


let rec no_conflict up1 up2 =(*{{{*)
  (up1 = up2) ||
    match up1, up2 with
      | ID s, ID s' -> true
      | UP(s,t), UP(s',t') ->
          let diff1, diff2 = make_diff s t, make_diff s' t' in
            if diff1 = diff2
            then true
            else (
              print_endline "diff1:"
              ; print_endline (string_of_diff diff1)
              ; print_endline "diff2:"
              ; print_endline (string_of_diff diff2)
              ; print_endline "conflict1:"
              ; print_endline (string_of_diff up1)
              ; print_endline "and"
              ; print_endline (string_of_diff up2)
              ; false)
      | UP(s,t), ID s' | ID s', UP(s,t) -> (match make_diff s t with
	  | UP(w,p) when w <== s' -> (
              print_endline "conflict2:"
              ; print_endline (string_of_diff up1)
              ; print_endline "and"
              ; print_endline (string_of_diff up2)
              ; false)
	  | RM w when w <== s' -> (
              print_endline "conflict3:"
              ; print_endline (string_of_diff up1)
              ; print_endline "and"
              ; print_endline (string_of_diff up2)
              ; false)
	  | ADD w when w <== s' -> (
              print_endline "conflict4:"
              ; print_endline (string_of_diff up1)
              ; print_endline "and"
              ; print_endline (string_of_diff up2)
              ; false)
	  | _ -> true) 
      | _, _ -> false (* there IS an conflict *)(*}}}*)

and unsafe up1 up2 =
  match up1, up2 with
    | UP(s,t), ID s' | ID s', UP(s,t) when s = s' -> (debug_msg "##" ; true)
    | UP(s,t), UP(s',t') when s = s' -> (debug_msg "$$"; not(t = t'))
    | _ -> (debug_msg "%%"; false)


and no_conflicts diff dlist =(*{{{*)
  match dlist with
    | [] -> true
    | (d :: ds) -> no_conflict diff d && no_conflicts diff ds (*}}}*)

and make_diff s t =
  let rec all_id diffs =(*{{{*)
    match diffs with 
      | [] -> true
      | d :: ds -> (match d with 
	  | ID _ -> all_id ds
	  | _ -> false) in(*}}}*)
    match s, t with
      | s, t when s = t -> ID s
      | A (_,_), C (_,_) | C (_,_), A(_,_) | A(_,_) , A(_,_) -> UP (s, t)
      | C (st, slist), C (tt, tlist) 
          when not(st = tt) -> 
          debug_msg "when not";
            UP(s, t)
      | C (st, slist), C (tt, tlist)
          when st = tt -> 
          debug_msg "when";
            let diff_list = get_diff slist tlist in
            let cor_diffs = correlate_diffs diff_list in
            let (no_c, _) = List.fold_left 
              (fun (flag, rest) diff -> no_conflicts diff rest && flag, List.tl rest) 
              (true,cor_diffs) cor_diffs in
              if no_c && not(all_id cor_diffs)
              then 
		(* there was no conflict, so we have the complicated task of finding(*{{{*)
		 * the change in the cor_diffs list; we can make use of the fact
		 * that since there was no conflict and not_all_ids then there must
		 * be at least ONE change to find in cor_list; and since none were
		 * in conflict, it does not matter which we select as they will all
		 * be the same.
		 *)(*}}}*)
		let l = List.filter 
		  (function d -> match d with ID s -> false | _ -> true) 
		  cor_diffs in
		  match l with
		    | [] -> raise (Fail "no diffs?")
		    | d :: _ -> 
			(*
			 * At this point, we have found out that there was an/*{{{*/
			 * non-conflicting update in a sub-part of a C(t,ts),C(t,ts')
			 * pair. That is, there is one a=>b in (ts, ts'); however, when
			 * 'd' is an UP(a,b) then we should actually recurse make_diff
			 * with a and b as parameters since UP(a,b) may not be minimal/*}}}*/
			 *)
			(match d with
			  | UP(a,b) -> (debug_msg "diving..."; make_diff a b)
			  | _ -> d
			)
              else
		(* there was a conflict (if there is a conflict we can trivially not(*{{{*)
		 * have all_id in cor_diffs; this is the easy case as we simply
		 * return the super-tree update
		 *)(*}}}*)
		UP(s,t)
      | _ -> raise (Fail "Some weird matching")

exception Nomatch

(* Take an env and new binding for m = t; if m is already bound to t then we
 * return the same env, and else we insert it in front The key point is that we
 * get an exception when we try to bind a variable to a NEW value!
 *)
let merge_update env (m, t) =
  try
    let v = List.assoc m env in
      if v = t
      then env
      else raise Nomatch
  with _ -> (m,t) :: env

(* take two environments; for each binding of m that is in both env1 and env2,
 * the binding must be equal; for variables that are in only one env, we simply
 * add it
 *)
let merge_envs env1 env2 =
  List.fold_left (fun env (m,t) -> merge_update env (m,t)) env2 env1

let mk_env (m, t) = [(m, t)]
let empty_env = ([] : (string * (string, string) gtree) list)

let rec sub env t =
  if env = [] then t else
    let rec loop t' = match t' with
    | C (ct, ts) ->
        C(ct, List.rev (
          List.fold_left (fun b a -> (loop a) :: b) [] ts
        ))
    | A ("meta", mvar) -> (try 
      List.assoc mvar env with (Fail _) ->
        (print_endline "sub?"; A ("meta", mvar)))
    | _ -> t'
    in
    loop t

(* try to see if a term st matches another term t
 * st may contain metas while t may not; TODO: why? there does not seem to
 * be any inherint reason local to the match_term function
 *)
let rec match_term st t =
  match st, t with
    | A("meta",mvar), _ -> mk_env (mvar, t)
    | A(sct,sat), A(ct,at) when sct = ct && sat = at -> empty_env
	(* notice that the below lists s :: sts and t :: ts will always match due to
	 * the way things are translated into gtrees. a C(type,args) must always have
	 * at least ONE argument in args 
	 *)
    | C(sct,s :: sts), C(ct, t :: ts) when 
	  sct = ct && List.length sts = List.length ts -> 
	List.rev (
          List.fold_left2 (fun acc_env st t ->
            merge_envs (match_term st t) acc_env
          ) (match_term s t) sts ts)
    | _ -> raise Nomatch

let is_read_only t = match t with 
  | C("RO", [t']) -> true
  | _ -> false
let get_read_only_val t = match t with
  | C("RO", [t']) -> t'
  | _ -> raise Nomatch

let mark_as_read_only t = C("RO", [t])

let can_match p t = try match match_term p t with _ -> true with Nomatch -> false

let find_match pat t =
  let cm = can_match pat in
  let rec loop t =
    cm t || match t with
    | A _ -> false
    | C(ct, ts) -> List.exists (fun t' -> loop t') ts
  in loop t

(* apply up t, applies up to t and returns the new term and the environment bindings *)
let rec apply up t =
  match up with (*
  | RM p -> (match t with 
  | C(ct, ts) -> 
      let ts' = List.rev (List.fold_left (fun acc_ts t ->
        if can_match p t
        then acc_ts
        else 
          let t1 = fst(try apply up t with Nomatch -> (t, empty_env)) 
in t1 :: acc_ts
) [] ts) in
C(ct,ts), empty_env
  | _ -> raise Nomatch
) *)
  | SEQ(d1, d2) -> 
        let t1, env1 = (try 
          apply d1 t with Nomatch -> 
            if !relax then t, empty_env else raise Nomatch)
        in
        (try apply d2 t1 with Nomatch ->
          if !relax 
          then t1, empty_env
          else raise Nomatch
        )
  | UP(src, tgt) -> 
      try 
        Hashtbl.find ht (up,t)
      with Not_found ->
      (match src, t with
      | A ("meta", mvar), _ -> 
          let env = mk_env (mvar, t) in 
            Hashtbl.add ht (up, t) (sub env tgt,env)
      | A (sct, sat), A(ct, at) when sct = ct && sat = at ->
          tgt, empty_env
      | C (sct, sts), C(ct, ts) when sct = ct -> 
          (try
            (*print_endline *)
            (*("trying " ^ string_of_gtree str_of_ctype str_of_catom t);*)
            let fenv = List.fold_left2 (fun acc_env st t ->
              let envn = match_term st t in
              merge_envs envn acc_env
            ) empty_env sts ts in
            let res = sub fenv tgt in
            (*print_endline ("result: " ^*)
            (*string_of_gtree str_of_ctype str_of_catom res); *)
            res, fenv
          with _ -> 
            (*print_endline "_";*)
            let ft, flag = List.fold_left
            (fun (acc_ts, acc_flag) tn -> 
              let nt, flag = (match apply_some up tn with
              | None -> tn, false
              | Some t -> t, true) in
              nt :: acc_ts, flag || acc_flag
            ) ([], false) ts in
            if flag 
            then C(ct, List.rev ft), empty_env
            else (* no matches at all *) raise Nomatch
            (*let ft = List.fold_right (fun tn acc_ts ->*)
            (*let nt, _ = apply up tn in*)
            (*nt :: acc_ts) (t :: ts) [] in*)
            (*C(ct, ft), empty_env*)
          )
      | _, C (ct, ts) -> 
          (*print_endline ("dive " ^ ct);*)
          let ft, flag = List.fold_left
          (fun (acc_ts, acc_flag) tn -> 
            let nt, flag = (match apply_some up tn with
            | None -> tn, false
            | Some t -> t, true) in
            nt :: acc_ts, flag || acc_flag
          ) ([], false) ts in
          if flag 
          then C(ct, List.rev ft), empty_env
          else (* no matches at all *) raise Nomatch
      | _ -> (
              (*print_endline "nomatch of ";*)
              (*print_endline (string_of_diff up);*)
              (*print_endline "with";*)
              (*print_endline (string_of_gtree str_of_ctype str_of_catom t);*)
              raise Nomatch)
  )
  | _ -> raise (Fail "Not implemented application")

and apply_noenv up t =
  let newterm, _ = apply up t in newterm


and eq_term t bp1 bp2 =
  (try
    let t1 = apply_noenv bp1 t in 
      (try
          t1 = apply_noenv bp2 t
        with Nomatch -> false)
    with Nomatch -> 
      try let _ = apply_noenv bp2 t in 
	  false 
    with Nomatch -> true)

and eq_changeset chgset bp1 bp2 =
  List.for_all (function (t,_) -> eq_term t bp1 bp2) chgset

and apply_some up t = 
  try ( 
    let nt, _ = (apply up t) 
    in Some nt) with Nomatch -> None

and safe_apply up t =
  try apply_noenv up t with Nomatch -> t

(* this function tries to match the assumed smaller term small with the assumed
 * larger term large; meta-variables are allowed in both terms, but only the
 * ones in small forces a binding; we assume that either the smaller term can
 * only match in one way to the larger; we use an eager matching strategy
 *)
and occurs_meta small large =
  let rec loc_loop env s ts =
    (match ts with
      | [] -> raise Nomatch
      | t :: ts -> try loop env s t with Nomatch -> loc_loop env s ts)
  and loop env s l = match s, l with
    | _, _ when s = l -> [] 
    | A ("meta", mvar), _ -> merge_update env (mvar, l)
    | C (lt, lts), C(rt, rts) ->
	(* first try to match eagerly *)
	(try
            (if lt = rt && List.length lts = List.length rts
            then 
              (* each term from lts must match one from rts *)
              List.fold_left2 (fun acc_env s l -> loop acc_env s l) env lts rts
              else raise Nomatch)
	  with Nomatch ->
	    (* since that failed try to find a matching of the smaller terms of the
	     * large term*)
	    loc_loop env s rts)
    | _, _ -> raise Nomatch
  in
    (try (loop [] small large; true) with Nomatch -> false)

(* this function takes a term t1 and finds all the subterms of t2 where t1 can
 * match; the returned result is a list of all the subterms of t2 that were
 * matched
 *)
and matched_terms t t' =
  match t, t' with
    | A _, A _ -> (try let env = match_term t t' in [t', env] with Nomatch -> [])
    | _, C(ct, ts) ->
	let res  = try [t', match_term t t'] with Nomatch -> [] in
	let mres = List.map (matched_terms t) ts in
	let g' acc (ti, envi) = 
          try 
            let envj = List.assoc ti acc in
              if subset envj envi && subset envi envj
              then acc
              else (ti, envi) :: acc
          with Not_found -> (ti, envi) :: acc in
	let g acc rlist = List.fold_left g' acc rlist in
	  List.fold_left g res mres
    | _, _ -> []

and safe_update_old gt1 gt2 up =
  match up with 
    | UP(l,r) -> (
	try 
          let tgt = apply_noenv up gt1 in
            if tgt = gt2
            then (
              (*print_endline ("patch applied cleanly:" ^ *)
              (*string_of_diff up);*)
              true)
            else (
              (*print_endline ("nonequal apply  :::: " ^*)
              (*string_of_diff up);*)
              try (
		let mt1 = matched_terms r gt2 in
		  (*print_string "mt1 {";*)
		  (*List.iter (fun (t, _) -> print_endline (string_of_gtree' t)) mt1;*)
		  (*print_endline "}";*)
		let mt2 = matched_terms r tgt in
		  (*print_string "mt2 {";*)
		  (*List.iter (fun (t, _) -> print_endline (string_of_gtree' t)) mt2;*)
		  (*print_endline "}";*)
		  subset mt1 mt2 && subset mt2 mt1
              ) with Nomatch -> (print_endline "nope";false)
            )
	      (* since the update did'nt apply, it is *safe* to include it as it will
	       * not transform the gt1,gt2 pair *)
	with Nomatch -> true 
      )
    | _ -> raise (Fail "unsup safe_up")

and invert_up up = 
  match up with
    | UP(l,r) -> UP(r, l)
    | _ -> raise (Fail "unsup invert_up")


(* check that up is a part of the update from term gt1 to gt2;
 * either up ~= (gt1, gt2)
 * orelse (gt1,gt2);up-1 ~= up
 *)
and safe_update gt1 gt2 up =
  try
    let tgt_l = apply_noenv up gt1 in
      if tgt_l = gt2 
      then true
      else
	try
          let tgt_r = apply_noenv (invert_up up) gt2 in
          let gt2'  = apply_noenv up tgt_r in
            gt2' = gt2
	with Nomatch -> false
  with Nomatch -> false

(* sometime it is useful to be able to check that a patch can be applied safely
 * before another patch
 *)
and safe_before (gt1, gt2) up1 up2 = 
  try
    not(subpatch_single up1 up2 (gt1, gt2)) && 
      safe_part (SEQ(up1,up2)) (gt1, gt2)
  with Nomatch -> false

and safe_before_pairs term_pairs up1 up2 =
  let safe_pred = fun p -> safe_before p up1 up2 in
    List.for_all safe_pred term_pairs

and sort_safe_before_pairs term_pairs upds =
  let (-->) up1 up2 = safe_before_pairs term_pairs up1 up2 in
  let rec insert_before d ds = match ds with 
    | [] -> [d]
    | d' :: ds when d --> d' -> d :: d' :: ds
    | d' :: ds -> d' :: insert_before d ds in
  let rec sort ds = match ds with 
    | [] -> []
    | d :: ds -> insert_before d (sort ds) in
    sort upds

and add_update up up_list =
  match up_list with
    | [] -> [up]
    | up' :: _ when up = up' -> 
	(*print_endline "equal"; *)
	up_list
    | up' :: up_list ->
	(match up, up' with
	  | UP(lhs,rhs), UP(lhs',rhs') when lhs = lhs' ->
              (*print_endline ("conflict \n" ^ string_of_diff up);*)
              (* this is a conflict because we know the the rhs' are not equal at
               * this point in the function and consequently we remove BOTH the up
               * and the old up' from the returned list and rely on larger updates
               * to be present in the (final) uplist *)
              up_list
	  | UP(lhs,rhs), UP(lhs',rhs') when lhs <== lhs' ->
              (* we are attempting to add an update which applies to the same (and
               * possibly more) lhs's as the old (lhs'); we then need to check that
               * the new update is compatible with the existing because otherwise
               * they can not both be in the resulting up_list and we should be
               * removing the smallest ???
               *)
              let tgt = apply_noenv up lhs' in
		if tgt = rhs'
		then
		  (* equal, but smaller update *)
		  up' :: add_update up up_list
		else 
		  (* non-equal *)
		  if not(lhs <== rhs')
		  then
		    (* smaller and seemingly part of *)
		    up' :: add_update up up_list 
		else (
		  (*print_endline "\ntgt::::";*)
		  (*print_endline (string_of_gtree' tgt);*)
		  (*print_endline ":::: not adding:";*)
		  (*print_endline (string_of_diff up);*)
		  (*print_endline ":::: because of:";*)
		  (*print_endline (string_of_diff up');*)
		  up' :: up_list)
	  | UP(lhs, rhs), (ID s | RM s | ADD s) when lhs = s ->
              (*print_endline ("adding\n" ^ string_of_diff up);*)
              (*add_update up up_list*)
              (* we do not add updates that we have already discovered should either
               * not change differently RM, ADD *)
              up' :: up_list
	  | (ID s | RM s | ADD s), UP(lhs, rhs) when lhs = s ->
              (*print_endline "?";*)
              (*add_update up up_list*)
              (* we override (old) updates in case we discover something that tells
               * us that the old update was ambiguous; e.i. we have found a place,
               * where the old update would do "the wrong thing"
               *)
              up :: up_list
	  | _, _ -> up' :: add_update up up_list
	)

and add_diffs diving_pred diff_list up_list =
  let local_add up_list d =
    match d with 
      | ID s -> get_ctf_diffs diving_pred up_list s s
      | RM _ | ADD _ -> add_update d up_list
      | UP(lhs, rhs) -> get_ctf_diffs diving_pred up_list lhs rhs

  in
    List.rev (List.fold_left local_add up_list diff_list)
and get_up lhs rhs = if lhs = rhs then ID lhs else UP(lhs, rhs)
and get_ctf_diffs diving_pred start_acc lhs rhs =
  let rec loop acc_diffs lhs rhs =
    match lhs, rhs with
      | A _, A _ -> add_update (get_up lhs rhs) acc_diffs
      | C(lct, lts), C(rct, rts) when diving_pred lhs rhs ->
          let top_up    = get_up lhs rhs in
          let acc_diffs = add_update top_up acc_diffs in
          let diffs     = get_diff lts rts in
          let c_diffs   = correlate_diffs diffs in
            add_diffs diving_pred c_diffs acc_diffs 
      | _, _  ->
          (*print_endline "other case";*)
          (*print_endline (string_of_diff (UP(lhs, rhs)));*)
          add_update (get_up lhs rhs) acc_diffs
  in
    loop start_acc lhs rhs

and traverse pred work lhs rhs =
  let rec add_ups pred ups work = 
    List.fold_left pred work ups in
  let rec loop work t t' = match t, t' with
    | C(tp,ts), C(tp',ts') when tp = tp' && List.length ts = List.length ts' ->
	(*List.fold_left2 loop (add_ups pred [UP(t,t')] work) ts ts'*)
	List.fold_left2 loop (pred work (UP(t,t'))) ts ts'
	  (* TODO: we should consider how to handle removals as they could also
	     be considered "context-free", but for the time being we have no good
	     way to handle those *)
	  (*
	    | C(tp,ts), C(tp',ts') when tp = tp' && List.length ts < List.length ts' ->
	  (* we have a removal-case; there could be more than one
	    removed term though so we need to be careful to find the ones
	    that were actually removed *)
*)
    | _, _ -> pred work (UP(t,t')) (*add_ups pred [UP(t,t')] work *) in
    loop work lhs rhs

and complete_part lhs rhs w u =
  try
    if apply_noenv u lhs = rhs 
    then u :: w else w
  with Nomatch -> w

and complete_parts gt1 gt2 =
  traverse (complete_part gt1 gt2) [] gt1 gt2
and isid_up (UP(a,b)) = a = b
  (* returns every[1] term update that could have occurred when updating the term
   * given by gt1 into the term given by gt2; one should notice that such an
   * update may not be safe to apply directly as it might transform parts of gt1
   * that were not supposed to be transformed; maybe a better notion for what this
   * function returns is a mapping from terms that changed into what they were
   * changed into
   *
   * [1] when we reach a pair of terms c(ts), c'(ts') and c!=c' and |ts|!=|ts'| we
   * stop the recursion and simply return the pair; one could consider whether it
   * would be appropriate to also dive into at least the parts of ts and ts' that
   * were the same
   *)
and all_maps gt1 gt2 =
  let all_pred lhs rhs w u =
    if 
      not(List.mem u w) && 
	not(isid_up u)
    then u :: w
    else w
  in
    traverse (all_pred gt1 gt2) [] gt1 gt2

and part_of lhs rhs w u =
  let gta     = apply_noenv u lhs in
  let gtb     = apply_noenv (invert_up u) rhs in
    if gta = rhs || gtb = lhs 
    then u :: w 
    else
      let parts_a = complete_parts gta rhs in
      let parts_b = complete_parts lhs gtb in
	if List.exists (fun bp -> List.mem bp parts_b) parts_a
	then u :: w
	else w


and get_ctf_diffs_new f work gt1 gt2 =
  traverse (part_of gt1 gt2) work gt1 gt2


(*and safe_list (UP(l,r)) c_parts =*)
and safe_list u c_parts =
  (* check that there no parts transforming read_only parts *)
  (debug_msg "****";
   List.iter (function p -> debug_msg (string_of_diff p)) c_parts;
   debug_msg "####";
   List.for_all (function u -> match u with
     | UP(a,b) when is_read_only a -> 
         if get_read_only_val a = b
         then true
         else (
           debug_msg ("violation: " ^ string_of_diff (UP(a,b))); 
           false)
     | UP(a,b) -> true
   ) 
     c_parts)
    
and mark_update up = match up with 
  | UP(l, r) -> UP(l, mark_as_read_only r)
  | SEQ(d1,d2) -> SEQ(mark_update d1, mark_update d2)

and safe_part_old t t' up =
  try
    let up_marked = mark_update up in
    let t'' = apply_noenv up_marked t in
      (debug_msg ("checking safety : " ^ string_of_diff up);
       debug_newline ();
       let c_parts = all_maps t'' t' in
	 if safe_list up c_parts
	 then (debug_msg "... safe"; true)
	 else (debug_msg "...unsafe"; false)
      )
  with Nomatch -> false


and fold_left3 f acc ts1 ts2 ts3 =
  let rec loop acc ts1 ts2 ts3 = match ts1, ts2, ts3 with
    | [], [], [] -> acc 
    | t1 :: ts1, t2 :: ts2, t3 :: ts3 -> loop (f acc t1 t2 t3) ts1 ts2 ts3 
    | _, _, _ -> raise Merge3 in
    loop acc ts1 ts2 ts3

(* t'' is safely reachable from t' which originated in t *)
and merge3 t1 t2 t3 =
  let m3 acc t1 t2 t3 = merge3 t1 t2 t3 && acc in
    t2 = t3 ||
      t1 = t2 ||
      match t1, t2, t3 with
	| C(ct1, ts1), C(ct2, ts2), C(ct3, ts3) when ct1 = ct2 || ct2 = ct3
	    -> fold_left3 m3 true ts1 ts2 ts3
	| _, _, _ -> false

(* is up a safe part of the term pair (t, t'') 
 *
 * bp<=(t,t')
 *)
and safe_part up (t, t'') =
  try 
    let t' = apply_noenv up t in
      merge3 t t' t''
  with (Nomatch | Merge3) -> (
    if !print_abs
    then (
      print_string "[Diff] rejecting:\n\t";
      print_endline (string_of_diff up)
    );
    false)

and relaxed_safe_part up (t, t'') =
  try 
    let t' = apply_noenv up t in
      merge3 t t' t''
  with 
  | Nomatch -> true 
  | Merge3 -> false

(* is the basic patch bp safe with respect to the changeset 
 *
 * bp<=C
 * *)
and safe_part_changeset bp chgset = 
  let safe_f = if !relax then relaxed_safe_part bp else safe_part bp in
  (*
   * List.for_all safe_f chgset
   *)
  let len = List.length (List.filter safe_f chgset) in
  len >= !no_occurs

(* the changeset after application of the basic patch bp; if there is a term to
 * which bp does not apply an exception is raised unless we are in relaxed mode
 * *)
and chop_changeset chgset bp =
(*  List.map (function (t, t'') -> (t,apply_noenv bp t)) chgset *)
  List.map (function (t, t'') -> (t,safe_apply bp t)) chgset

(* bp <=(t,t) bp' <=> bp'<=(t,t') & bp'(t)=>t'' & bp<=(t,t'') *)
and subpatch_single bp bp' (t, t') =
  safe_part bp' (t, t') &&
    let t'' = apply_noenv bp' t in
      safe_part bp (t, t'')

and subpatch_changeset chgset bp bp' = 
  if safe_part_changeset bp' chgset 
  then
    let chop = chop_changeset chgset bp' in
    if safe_part_changeset bp chop
    then true
    else 
      (
        (*print_string "[Diff] <\n\t";*)
        (*print_endline (string_of_diff bp);*)
        false)
  else 
    (
      (*print_string "[Diff] .\n\t";*)
      (*print_endline (string_of_diff bp');*)
      false
    )
    

and get_ctf_diffs_all work gt1 gt2 =
  let all_pred lhs rhs w u =
    if 
      not(List.mem u w) && 
      match u with UP(a,b) -> not(a = b)
	  then u :: w
	  else w
    in
      traverse (all_pred gt1 gt2) work gt1 gt2

  and get_ctf_diffs_safe work gt1 gt2 =
    let all_pred lhs rhs w u =
      if 
	not(List.mem u w) && 
	  (match u with 
	    | UP(a,b) -> not(a = b)
	    | RM a -> true )
	&&
	  safe_part u (gt1, gt2)
      then u :: w
      else w
      in
	traverse (all_pred gt1 gt2) work gt1 gt2

let complete_changeset chgset bp_list =
  let app_f t bp = safe_apply bp t in
  List.for_all
    (function (t,t'') ->
      List.fold_left app_f t bp_list = t''
    )
    chgset

let make_subpatch_tree parts t t' =
  (*let parts = get_ctf_diffs_safe [] t t' in*)
  List.map (function p -> 
    (p, 
    List.filter (function p' -> 
      subpatch_single p' p (t,t')) parts)) 
    parts

(* this function sorts patches according to the subpatch relation in descending
 * order ; notice that when equivalent patches are encountered either could be
 * sorted before the other; it can be the case that two patches in the list are
 * simply not in a subpatch relation to each; then we must find out which one to
 * put first
 *)
let sort_patches chgset parts =
  let comp_patches a b =
    match 
      subpatch_changeset chgset a b, 
      subpatch_changeset chgset b a with
	| true, true -> 0
	| false, true -> -1
	| true, false -> 1
	| false, false -> 0 
            (*
             *(print_string "[Diff] comparing\n\t";
             *print_endline (string_of_diff a);
             *print_string "[Diff] with\n\t";
             *print_endline (string_of_diff b);
             *raise (Fail "incomparable"))
             *)
  in
    List.sort comp_patches parts
      
let make_subpatch_tree_changeset parts chgset =
  let subp = subpatch_changeset chgset in
    (* for each part, find all the parts that are subparts *)
    List.map
      (function bp ->
	(bp, sort_patches chgset  (List.filter (function bp' -> subp bp' bp) parts))
      )
      parts

(* this function takes a list of pairs of patch and subpatches as constructed by
 * make_subpatch_tree_changeset and removes those pairs for which the
 * index-patch is a subpatch of some other
 *)
let filter_subsumed parted =
  let in_subs (bp, _) = List.for_all
    (function (bp' , subs) -> 
      bp = bp' ||
	not(List.mem bp subs
	)) 
    parted in
    List.filter in_subs parted

let string_of_subtree_single (p, ps) =
  ">>> " ^ string_of_diff p ^ "\n" ^
    String.concat " ,\n" (List.map string_of_diff ps)

let string_of_subtree tr = 
  String.concat ";;\n\n" 
    (List.map string_of_subtree_single tr)

(* rejects bp bp'; predicate that decides whether bp rejects bp' with
   respect to term pair (t, t'') *)
let reject_term_pair (t, t'') bp bp' =
  try
    let t' = apply_noenv bp t in
      not(safe_part bp' (t', t''))
  with Nomatch -> (
    print_endline "[Diff] non-applying part?";
    print_endline (string_of_diff bp);
    raise Nomatch
  )

(* apply a bp to all term pairs and return the new pairs *)
let apply_changeset bp chgset =
  let app_f = 
    if !relax 
    then safe_apply
    else apply_noenv in
  List.map (function (t,t'') -> (app_f bp t, t'')) chgset

(* return the list of all those bp' that bp does not reject;
   i.e. which are still applicable AFTER application of bp *)
let get_applicable chgset bp bps =
  try 
    let chgset' = apply_changeset bp chgset in
    (chgset', List.filter (function bp' -> 
      not(chgset' = chgset) &&
      not(subpatch_changeset chgset' bp' bp) &&
      safe_part_changeset bp' chgset') bps)
  with Nomatch -> (
    print_endline "[Diff] non-applying part-changeset?";
    print_endline (string_of_diff bp);
    raise Nomatch
    )

let gtree_of_ast_c parsed = Visitor_j.trans_prg2 parsed

(* first, let's try to parse a C program with Yoann's parser *)
let read_ast file =
  let (pgm2, parse_stats) = 
    Parse_c.parse_print_error_heuristic file in
    pgm2
      

let valOf x = match x with
  | None -> raise (Fail "valOf: None")
  | Some y -> y

let safe up tup = 
  match tup with
    | UP (o, n) -> (try 
	  debug_msg ("applying : \n" ^
			string_of_diff tup);
	match apply_noenv up o = n with
	  | true -> debug_msg "good"; true
	  | false -> debug_msg "bad"; false
      with Nomatch -> debug_msg "N/M"; true)
    | _ -> raise (Fail "tup not supported")


exception No_abs

let filter_conflicts orgs news =
  if news = [] then raise No_abs
  else
    let cands = List.filter 
      (fun nup -> List.for_all (fun org -> not(unsafe nup org)) orgs) 
      news in
      match cands with
	| [] -> raise No_abs
	|  x -> x


let rec free_vars t =
  let no_dub_app l1 l2 = List.rev_append 
    (List.filter (fun x -> not(List.mem x l2)) l1)
    l2 
  in
    match t with
      | A ("meta", mvar) -> [mvar]
      | C (_, ts) -> List.fold_left
	  (fun fvs_acc t -> no_dub_app (free_vars t) fvs_acc)
	    [] ts
      | _ -> []

let rec count_vars t =
  match t with
    | A("meta", _) -> 1
    | C(_, ts) -> List.fold_left
	(fun var_count t -> count_vars t + var_count) 0 ts
    | _ -> 0

(* assume only RELATED terms are given as arguments; this should hold a the
 * function is only called from make_compat_pairs which is always called on
 * related terms (somehow?)
 *)
let compatible_with lhs rhs =
  let fv_l = free_vars lhs in
  let fv_r = free_vars rhs in
    if fv_r = []
    then debug_msg "fv_r = []";
    (*
     *let b = subset fv_r fv_l in
     *if b && fv_r = [] then debug_msg "compat and empty";
     *b
     *)
    (* strict compatibility: equal metas *)
    if !be_strict
    then subset fv_r fv_l && subset fv_l fv_r
      (* loose compatibility: lhs <= rhs *)
    else subset fv_r fv_l

let make_compat_pairs lhs rhs_list acc =
  List.fold_left (fun pairs rhs ->
    if compatible_with lhs rhs
    then UP (lhs, rhs) :: pairs
    else pairs
  ) acc rhs_list

let make_gmeta name = A ("meta", name)

let metactx = ref 0
let reset_meta () = metactx := 0
let inc x = let v = !x in (x := v + 1; v)
let ref_meta () = inc metactx
let new_meta env t =
  let m = "X" ^ string_of_int (ref_meta ()) in
    (*print_endline *)
    (*("binding " ^ m ^ "->" ^ *)
    (*string_of_gtree str_of_ctype str_of_catom t);*)
    [make_gmeta m], [(m,t)]


let get_metas build_mode org_env t = 
  let rec loop env =
    match env with
      | [] when build_mode -> (
          debug_msg ("bind: " ^ string_of_gtree str_of_ctype str_of_catom t);
          debug_msg (">>>>>>>>>>> with size: " ^ string_of_int (gsize t));
          new_meta org_env t)
      | [] -> [], []
      | (m, t') :: env when (t = t') ->
          (* below we assume that equal terms need not be abstracted by equal
           * meta-variables
           *)
          if !use_mvars
          then
            let metas, env' = loop env in
              (make_gmeta m) :: metas, (m, t') :: env'
		(* below we make sure that equal terms are abstracted by the SAME
		 * meta-variabel; so once we find one reverse binding to t, we can
		 * return the corresponding metavariable and need not look any further
		 *)
          else
            [make_gmeta m], org_env
      | b :: env ->
          let metas, env' = loop env in
            if build_mode
            then metas, b :: env'
            else metas, org_env

  in
    loop org_env

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
  (*
   *print_endline "gen_perms sizes: ";
   *List.iter (fun ec ->
   * print_string "<";
   * print_string (string_of_int (List.length ec));
   * print_string "> ";
   * ) lists;
   *)
  (*print_newline ();*)
  (* FIXME: figure out why this assertion was put here in the first place *)
  (*assert(not(List.exists ((=) []) lists));*)
  (*debug_msg "perms of ";*)
  (*List.iter (fun l -> List.iter (fun e -> debug_msg ((string_of_gtree*)
  (*str_of_ctype str_of_catom e) ^ " ")) l; debug_msg "%%") lists;*)
  match lists with(*{{{*)
    | [] -> (debug_msg "."; [[]])
    | lis :: lists -> (debug_msg ","; prefix_all lis (gen_perms lists))(*}}}*)


(*
let rec abs_term_size terms_changed is_fixed should_abs up =
  let rec loop build_mode env t = match t with
    | A (ct, at) -> 
	if is_fixed t
	then 
          if terms_changed t
          then [t], env
          else 
            let metas, renv = get_metas build_mode env t in
              t :: metas, renv
	else 
          if not(should_abs t)
          then [t], env
        else 
          (* now we have an atomic term that we should abstract and thus we will
           * not also return the concrete term as a possibility; the problem is
           * that then we may abstract atoms which should not have been because
           * they were actually changed -- for those atoms that change, we
           * therefore return both the concrete term and an abstracted one
           *)
          if terms_changed t
          then
            (*[t], env*)
            let metas, renv = get_metas build_mode env t in
              t :: metas, renv
        else 
          get_metas build_mode env t (*}}}*)
    | C (ct, []) -> raise (Fail "whhaaattt")
    | C (ct, ts) ->
	debug_msg ("CC: " ^ string_of_gtree str_of_ctype str_of_catom t);(*{{{*)
	if !abs_subterms <= gsize t
	then [t], env
	else
	  let metas, env = 
            if not(is_fixed t) && (if build_mode then should_abs t else true)
            then
              get_metas build_mode env t 
            else 
              (* the term is fixed, but it did not change "by itself" so we should
               * actually abstract it
               *)
              if terms_changed t
              then
		[], env 
            else 
              get_metas build_mode env t
	  in
	  let ts_lists, env_ts = List.fold_left
            (fun (ts_lists_acc, acc_env) tn ->
              (* each abs_tns is a list of possible abstractions for the term tn
               * and env_n is the new environment (for build_mode)
               *)
              let abs_tns, env_n = 
		(*if not(is_fixed tn)*)
		(*then*)
		loop build_mode acc_env tn 
		  (*else*)
		  (*[tn], acc_env*)
              in
              let abs_tns = if abs_tns = [] then [tn] else abs_tns in
		abs_tns :: ts_lists_acc, env_n
            ) ([], env) (List.rev ts) in
	    (* note how we reverse the list ts given to the fold_left function above
	     * to ensure that subterms are visited in left-to-right order and
	     * inserted in left-to-right order
	     *)
	    (* ts_lists is a list of lists of possible abstractions of each 
	     * term in ts we now wish to generate a new list of lists such 
	     * that each list in this new list contains one element from 
	     * each of the old lists in the same order
	     *)
	    (*print_string "input size to gen_perms: ";*)
	    (*print_endline (string_of_int (List.length ts_lists));*)
	    (*List.iter (fun l ->*)
            (*print_string ("<" ^ string_of_int (List.length l) ^ "> ");*)
            (*if List.length l > 128 then raise (Fail "not going to work")*)
            (*List.iter (fun gt -> print_endline (string_of_gtree' gt)) l;*)
            (*flush stdout;*)
	    (* ) ts_lists;*)
	    (*print_newline ();*)
	  let perms = gen_perms ts_lists in
	    (* given the perms we now construct the complete term C(ct,arg) *)
	  let rs = List.rev (List.fold_left (fun acc_t args -> 
            C(ct, args) :: acc_t) [] perms) in
	    (* finally, we return the version of t where sub-terms have been
	     * abstracted as well as the possible metas that could replace t
	     *)
	    metas @ rs, env_ts in(*}}}*)
    match up with 
      | UP(lhs, rhs) -> 
	  (* first build up all possible lhs's along with the environment(*{{{*)
	   * that gives bindings for all abstracted variables in lhs's
	   *)
          reset_meta ();
          (*print_endline ("loop :: \n" ^ string_of_diff up);*)
          let abs_lhss, lhs_env = loop true [] lhs in
            (*List.iter (fun (m,t) -> print_string*)
            (*("[" ^ m ^ "~>" ^ string_of_gtree' t ^ "] ")) lhs_env;*)
            (*print_newline ();*)
            (*print_endline ("lhss : " ^ string_of_int (List.length abs_lhss));*)
            (*print_endline "lhss = ";*)
            (*List.iter (fun d -> print_endline (string_of_gtree' d)) abs_lhss;*)
            assert(not(abs_lhss = []));
            (* now we check that the only solution is not "X0" so that we will end
             * up transforming everything into whatever rhs
             *)
            let abs_lhss = (match abs_lhss with
              | [A ("meta", _) ] -> (debug_msg 
					("contextless lhs: " ^ string_of_diff up); [lhs])
              | _ -> abs_lhss)
              (* now use the environment to abstract the rhs term
              *) in
            let abs_rhss, rhs_env = loop false lhs_env rhs in
              (*print_endline ("rhss : " ^ string_of_int (List.length abs_rhss));*)
              (*print_endline "rhss = ";*)
              (*List.iter (fun d -> print_endline (string_of_gtree' d)) abs_rhss;*)
              (*List.iter (fun (m,t) -> print_string*)
              (*("[" ^ m ^ "~>" ^ string_of_gtree' t ^ "] ")) rhs_env;*)
              (*print_newline ();*)
              (* if the below assertion fails, there is something wrong with the
               * environments generated
               *)
              (*assert(lhs_env = rhs_env);*)
              (* we now wish to combine each abs_lhs with a compatible abs_rhs
              *)
              (* if the rhs had no possible abstractions then we return simply the
               * original rhs; this can not happen for lhs's as the "bind" mode is
               * "on" unless the fixed_list dissallows all abstractions
               *)
            let abs_rhss = if abs_rhss = [] then [rhs] else abs_rhss in
            let lres = List.fold_left (fun pairs lhs ->
              make_compat_pairs lhs abs_rhss pairs
            ) [] abs_lhss
            in
              lres, lhs_env (* = rhs_env *)(*}}}*)
      | _ -> raise (Fail "non supported update given to abs_term")

*)

let renumber_metas t metas =
  match t with
    | A ("meta", mvar) -> (try 
	  let v = List.assoc mvar metas in
	    A ("meta", v), metas
      with _ -> let nm = "X" ^ string_of_int (ref_meta ()) in
		  A ("meta", nm), (mvar, nm) :: metas)
    | t -> t, metas

let fold_botup term upfun initial_result =
  let rec loop t acc_result =
    match t with
      | A _ -> upfun t acc_result
      | C (ct, ts) -> 
          let new_terms, new_acc_result = List.fold_left
            (fun (ts, acc_res) t ->
              let new_t, new_acc = loop t acc_res in
		new_t :: ts, new_acc
            ) ([], acc_result) ts
          in
            upfun (C(ct, List.rev new_terms)) new_acc_result
  in
    loop term initial_result

let renumber_metas_up up =
  (*print_endline "[Diff] renumbering metas";*)
  reset_meta ();
  match up with
    | UP(lhs, rhs) -> 
	let lhs_re, lhs_env = fold_botup lhs renumber_metas [] in
	let rhs_re, rhs_env = fold_botup rhs renumber_metas lhs_env in
	  assert(lhs_env = rhs_env);
	  UP(lhs_re, rhs_re)
    | ID s -> 
	let nm, new_env = renumber_metas s [] in ID nm
    | RM s -> 
	let nm, new_env = renumber_metas s [] in RM nm
    | ADD s -> 
	let nm, new_env = renumber_metas s [] in ADD nm

let rec abs_term_imp terms_changed is_fixed up =
  let cur_depth = ref !abs_depth in
  let should_abs t = 
    !cur_depth >= 0
    (*if !cur_depth >= 0*)
    (*then (print_endline ("[Diff] allowed at depth: " ^ string_of_int !cur_depth); true)*)
    (*else (print_endline ("[Diff] not allowed at depth " ^ string_of_int !cur_depth); false)*)
    (*then (print_endline ("[Diff] allowing " ^ string_of_gtree' t); true)*)
    (*else (print_endline ("[Diff] current depth " ^ string_of_int !cur_depth); false)*)
  in
  let rec loop build_mode env t = match t with
  | A (ct, at) -> 
      if should_abs t
      then
        if terms_changed t
        then
          let metas, renv = get_metas build_mode env t in
          t :: metas, renv
          (*[t], env*)
    else
      if is_fixed t
      then
        let metas, renv = get_metas build_mode env t in
        t :: metas, renv
        else 
          get_metas build_mode env t
      else (
        debug_msg ("[Diff] not abstracting atom: " ^ string_of_gtree' t);
        [t], env)
  | C (ct, []) -> 
      (* raise (Fail ("whhaaattt: "^ct^"")) *)
      (* this case has been reached we could have an empty file;
       * this can happen, you know! we return simply an atom
       *)
      [A(ct, "new file")], env
  | C (ct, ts) when !abs_subterms <= gsize t -> 
      (fdebug_endline !print_abs ("[Diff] abs_subterms " ^ string_of_gtree' t);
      [t], env)
  | C (ct, ts) ->
      let metas, env = 
        if should_abs t && not(terms_changed t)
        then get_metas build_mode env t 
        else [], env
      in
      cur_depth := !cur_depth - 1;
      let ts_lists, env_ts = List.fold_left
        (fun (ts_lists_acc, acc_env) tn ->
          let abs_tns, env_n = loop build_mode acc_env tn 
          in
          let abs_tns = if abs_tns = [] then [tn] else abs_tns in
          abs_tns :: ts_lists_acc, env_n) 
        ([], env) (List.rev ts) 
      in
      cur_depth := !cur_depth + 1;
      let perms = gen_perms ts_lists in
      let rs = List.rev (List.fold_left (fun acc_t args -> 
          C(ct, args) :: acc_t) [] perms) 
      in
        metas @ rs, env_ts in(*}}}*)
  match up with 
  | UP(lhs, rhs) -> 
      (* first build up all possible lhs's along with the environment(*{{{*)
      * that gives bindings for all abstracted variables in lhs's
      *)
      reset_meta ();
      (*print_endline ("loop :: \n" ^ string_of_diff up);*)
      let abs_lhss, lhs_env = loop true [] lhs in
      (*List.iter (fun (m,t) -> print_string*)
      (*("[" ^ m ^ "~>" ^ string_of_gtree' t ^ "] ")) lhs_env;*)
      (*print_newline ();*)
      (*print_endline ("lhss : " ^ string_of_int (List.length abs_lhss));*)
      (*print_endline "lhss = ";*)
      (*List.iter (fun d -> print_endline (string_of_gtree' d)) abs_lhss;*)
      assert(not(abs_lhss = []));
      (* now we check that the only solution is not "X0" so that we will end
             * up transforming everything into whatever rhs
             *)
let abs_lhss = (match abs_lhss with
| [A ("meta", _) ] -> (debug_msg 
("contextless lhs: " ^ string_of_diff up); [lhs])
  | _ -> abs_lhss)
(* now use the environment to abstract the rhs term
 *) in
let abs_rhss, rhs_env = loop false lhs_env rhs in
(*print_endline ("rhss : " ^ string_of_int (List.length abs_rhss));*)
(*print_endline "rhss = ";*)
(*List.iter (fun d -> print_endline (string_of_gtree' d)) abs_rhss;*)
(*List.iter (fun (m,t) -> print_string*)
(*("[" ^ m ^ "~>" ^ string_of_gtree' t ^ "] ")) rhs_env;*)
(*print_newline ();*)
(* if the below assertion fails, there is something wrong with the
 * environments generated
 *)
(*assert(lhs_env = rhs_env);*)
(* we now wish to combine each abs_lhs with a compatible abs_rhs
 *)
(* if the rhs had no possible abstractions then we return simply the
 * original rhs; this can not happen for lhs's as the "bind" mode is
 * "on" unless the fixed_list dissallows all abstractions
 *)
let abs_rhss = if abs_rhss = [] then [rhs] else abs_rhss in
let lres = List.fold_left (fun pairs lhs ->
  make_compat_pairs lhs abs_rhss pairs
            ) [] abs_lhss
in
lres, lhs_env (* = rhs_env *)(*}}}*)
  | _ -> raise (Fail "non supported update given to abs_term_size_imp")

let abs_term_noenv terms_changed is_fixed should_abs up = 
  fdebug_endline !print_abs ("[Diff] abstracting concrete update with size:" ^
        string_of_int (Difftype.csize up) ^ " " ^
		    string_of_diff up);
  (*let res, _ = abs_term_size terms_changed is_fixed should_abs up in *)
  let res, _ = abs_term_imp terms_changed is_fixed up in 
  let res_norm = List.map renumber_metas_up res in
    fdebug_endline !print_abs ("[Diff] resulting abstract updates: " ^ 
		      string_of_int (List.length res));
    if !print_abs 
    then List.iter (function d -> print_endline (string_of_diff d)) res_norm;
    res_norm

(* according to this function a term is fixed if it occurs in a given list
 * the assumption is that this list have been constructed by a previous
 * analysis, eg. datamining of frequent identifiers
 * if it does not occur and is an atom, then it is not fixed
 * if it does not occur and is an "appliction" and the op. does 
 * occur, then it is fixed
 * otherwise it is not fixed, even though it does not occur
 *)
let list_fixed flist t =
  if !be_fixed
  then List.mem t flist 
  else false
    (*
     *||
     *match t with
     *| A _ -> false
     *| C (_, op :: args) when List.mem op flist -> true
     *| C (_, op :: args) -> true
     *| _ -> false
     *)

(* this function always allows abstraction when the term is not fixed
 * one could maybe imagine more complex cases, where even though a term
 * is not fixed one would rather not abstract it; one example is that for very
 * large complex terms that are not frequent; very large terms could be
 * considered inappropriate for abstraction as we are not interested in finding
 * very large common structures, but are mostly concerned about smaller things;
 * at least we can make the decision be up to the user by defining a threshold
 * as to how large terms we allow to be abstracted
 *)

let should_abs_always t = true
  (* size-based abstraction predicate; only terms smaller than a certain threshold
   * are abstracted 
   *)
let should_abs_size t = gsize t <= !abs_threshold

(* depth based abstraction pred: only abstract "shallow" terms -- i.e. terms
 * with depth less than threshold
 *)
(* let should_abs_depth t = gdepth t <= !abs_threshold *)
let should_abs_depth t = gdepth t <= !abs_depth

let s = A("ident","s")
let g = A("ident","g")
let h = A("ident","h")
let f = A("ident","f")
let w = A("ident","w")
let x = A("ident","x")
let patch = UP( 
  C( "call", [h;C ("call",[f;s])] ) , 
  C( "call", [h;C ("call",[f;x])] )
)

let non_dub_cons x xs = if List.mem x xs then xs else x :: xs 
let ($$) a b = non_dub_cons a b
let non_dub_app ls1 ls2 = List.fold_left (fun acc l -> l $$ acc) ls1 ls2
let (%) ls1 ls2 = non_dub_app ls1 ls2

(* construct all the possible sub-terms of a given term in the gtree format; the
 * resulting list does not have any order that one should rely on
 *)
let make_all_subterms t =
  let rec loop ts t =
    match t with
      | C(_, ts_sub) -> List.fold_left loop (t $$ ts) ts_sub
      | _ -> t $$ ts in
    loop [] t

(* in order to make a list of the things that are supposed to be fixed when
 * doing abstraction, we need a list of (org,up) programs to work with;
 * the idea is to use datamining to find a subset of items that occurs
 * frequently and use that to construct the fixed_list
 *)

let select_max a b =
  if List.length a > List.length b
  then a
  else b
let union_lists unioned_list new_list =
  new_list % unioned_list

let unique l =
  let len = List.length l in
  let tbl = Hashtbl.create (len) in
    print_endline ("[Diff] inserting " ^ 
		      string_of_int len ^ " elements");
    let lct = ref 0 in
      List.iter (fun i -> 
	Hashtbl.replace tbl i ();
	debug_msg (string_of_int !lct);
	lct := !lct + 1
      ) l;
      print_endline ("[Diff] extracting " ^ 
			string_of_int (Hashtbl.length tbl) ^ " elements");
      Hashtbl.fold (fun key data accu -> key :: accu) tbl []

let always_dive lhs rhs = 
  match lhs, rhs with
    | C (_,_), C (_,_) -> true
    | _ -> false

let no_calls_dive lhs rhs = 
  match lhs, rhs with
    | C("call", f::_), C("call", f'::_) -> (debug_msg "$"; false)
    | C (_,_), C (_,_) -> true
    | _ -> false

let print_diffs ds =
  print_endline "{{{";
  List.iter (fun d -> print_endline (string_of_diff d)) ds;
  print_endline "}}}"

let print_additions d =
  match d with
    | ADD d -> print_endline ("\n+ " ^ string_of_gtree' d)
    | RM d -> print_endline ("\n- " ^ string_of_gtree' d)
    | UP(s,t) -> 
	(print_endline (string_of_diff d);
	 print_newline ())
    | ID d -> () (* print_endline ("\n= " ^ string_of_gtree' d)*)
    | _ -> ()

let apply_list gt1 ds = 
  let app_nonexec s d = try apply_noenv d s with omatch -> s in
    List.fold_left app_nonexec s ds

let unabstracted_sol gt1 gt2 = 
  get_ctf_diffs_safe [] gt1 gt2
    (*print_endline "\n== get_ctf_diffs succeeded ==";*)
    (*List.iter print_additions dgts;*)
    (*print_endline "== those were the additions ==";*)
    (*print_endline "<< hierarchy >>";*)
    (*print_endline (string_of_subtree (make_subpatch_tree dgts gt1 gt2));*)
    (* get the list of those diffs that are complete *)
    (*let cgts = List.filter (fun d -> complete_patch gt1 gt2 [d]) dgts in*)
    (* take out those that are complete in them selves *)
    (*let dgts = List.filter (fun d -> not(List.mem d cgts)) dgts in*)
    (*print_endline "dgts::::::";*)
    (*List.iter (fun d -> print_endline (string_of_diff d)) dgts;*)
    (*print_newline ();*)
    (*if dgts = []*)
    (* there were only complete updates; thus we should simply return the smallest
     * one of those; there does not seem to be any good reason to return any
     * others
     *)
    (*then*)
    (*try [[List.hd cgts]] with (Failure "hd") -> []*)
    (*else*)
    (* since we now have to look at the smaller updates, we can rest assured
     * that if the constructed patches update the smallest of the complete one
     * correctly, they will also update the entire program correctly; this means
     * in turn that we look at smaller terms and can expect faster running time;
     * furthermore, and this is the important part, the collect function returns
     * the gt1,gt2 pair if a constructed patch was not complete and that would
     * imply that if NONE of the constructed patches were complete, which could
     * be caused by only having wrong/incomplete updates inferred, we would
     * return the entire gt1,gt2 pair as the result. In other words we ensure
     * gt1 and gt2 correspond to the smallest possible terms (which is safe as
     * said just before)
     *)
    (*let UP(gt1, gt2) = List.hd cgts in*)
    (*let parted = partition dgts in*)
    (*print_endline "parted::::::";*)
    (*List.iter print_diffs parted;*)
    (*let all_perms = gen_perms parted in*)
    (*print_endline "all_perms 1 :::::";*)
    (*List.iter print_diffs all_perms;*)
    (*print_newline ();*)
    (*let all_perms = List.map sort all_perms in*)
    (*print_endline "all_perms 2 :::::";*)
    (*List.iter print_diffs all_perms;*)
    (*print_newline ();*)
    (*let all_perms = List.map (fun d -> collect gt1 gt2 d) all_perms in*)
    (*print_endline "collected :::::";*)
    (*List.iter print_diffs all_perms;*)
    (*print_newline ();*)
    (*let all_perms = rm_dub all_perms in*)
    (*print_endline ">>>>>>>>>>>>> now we have:";*)
    (*print_sols all_perms;*)
    (*all_perms*)

let make_subterms_update up =
  match up with
    | UP(lhs, rhs) -> 
	(make_all_subterms lhs) % 
	  (make_all_subterms rhs)
    | RM t | ADD t | ID t -> make_all_subterms t

let make_subterms_patch ds =
  List.fold_left (fun subt_acc up ->
    make_subterms_update up % subt_acc) [] ds

(* takes an e list list and returns the e list with the property that all e's in
 * the returned list appear in all the input e lists
 *)

let inAll e ell = List.for_all (fun l -> List.mem e l) ell

let filter_all_old ell =
  List.fold_left (fun acc l -> List.fold_left (fun acc e ->
    if inAll e ell
    then e $$ acc
    else acc
  ) acc l) [] ell

let filter_all ell =
  match ell with
  | sublist :: lists -> 
      List.filter (function e -> inAll e lists) sublist
  | [] -> []


let inSome e ell = 
  let occurs = List.length (List.filter (fun l -> List.mem e l) ell) in
  (*occurs >= List.length ell - !no_exceptions*)
  occurs >= !no_occurs

let filter_some ell =
  List.fold_left (fun acc l -> List.fold_left (fun acc e ->
    if inSome e ell
    then e $$ acc
    else acc
  ) acc l) [] ell

(* takes a diff list (patch) and finds the subterms in the small updates;
 * we should take a flag to enable strict frequency or relaxed
 * with strict freq. an item, must be in all small updates in all patches
 * with relaxed an item, must appear somewhere in all patches (not necessarily
 * in all small updates as in the strict version
 *
 *)
let frequent_subterms_patch ds =
  debug_msg "Frequent subterms in patch";
  let tll = List.map make_subterms_update ds in
    debug_msg "filtering in patch";
    (*filter_all tll*)
    List.flatten tll

let frequent_subterms_patches ps =
  debug_msg "Frequent subterms in patches";
  let freq_subterms_lists = 
    List.map frequent_subterms_patch ps in
    debug_msg "filtering in patches";
    filter_all freq_subterms_lists

let frequent_subterms_changeset cs =
  debug_msg "Frequent subterms in changeset";
  let freq_subterms = 
    (*List.map frequent_subterms_patches cs in*)
    List.map frequent_subterms_patch cs in
    debug_msg "filtering in changeset";
    (* TODO: Use dmine instead of filter_all so that we can support an exception
     * level. The idea is that if we allow exceptions to the number of times a
     * term can appear, then we must somehow compensate for that when we look for
     * frequent items.
     *)
    filter_all freq_subterms


let make_fixed_list term_pairs =
  let subterms = List.map 
    (function (gtn, _) -> 
      fdebug_string !print_abs ("[Diff] making all subterms for :\n\t");
      fdebug_endline !print_abs (string_of_gtree' gtn);
      make_all_subterms gtn) term_pairs in
    (* Here we should allow frequent subterms that are not global; we could use
     * dmine to implement it, but I think it is so simple that we need only do a
     * simple filtering
     *)
    if !do_dmine
    then
      filter_some subterms
    else 
      filter_all subterms

let make_fixed_list_old updates =
  let subterms_list =
    List.fold_left (fun acc_list (gt1, gt2) ->
      ((make_all_subterms gt1) % (make_all_subterms gt2)) :: acc_list
    ) [] updates in
  let empty_db = DBM.makeEmpty () in
  let subterm_db = List.fold_left DBM.add_itemset empty_db subterms_list in
  let db_size = DBM.sizeOf subterm_db in
    (*print_string  "There are ";*)
    (*print_string  (string_of_int db_size);*)
    (*print_endline " itemsets";*)
    (*print_endline "With sizes:";*)
    DBM.fold_itemset subterm_db 
      (fun () is -> print_string ("[" ^ string_of_int
				     (List.length is) ^"]")) ();
    print_newline ();
    print_string "Finding frequent subterms...";
    flush stdout;
    let mdb = DBM.dmine subterm_db db_size in
    let cdb = mdb in (* DBM.close_db subterm_db mdb in *)
      print_endline "done.";
      (*DBM.print_db (string_of_gtree str_of_ctype str_of_catom) cdb;*)
      (*let itemset = DBM.fold_itemset cdb select_max [] in*)
      let itemset = DBM.fold_itemset cdb union_lists [] in
	print_endline "Frequent items selected:";
	List.iter (fun e -> 
	  print_endline 
	    (string_of_gtree str_of_ctype str_of_catom e)) 
	  itemset;
	list_fixed itemset

(*let jlist = [s;f;h;w]*)
(*let jfix  = list_fixed jlist*)


let read_src_tgt src tgt =
  let gt1 = gtree_of_ast_c (read_ast src) in
  let gt2 = gtree_of_ast_c (read_ast tgt) in
    gt1, gt2

(* this function takes a list of patches (diff list list) and looks for the
 * smallest size of any update; the size of an update is determined by the gsize
 * of the left-hand-side 
 *)
let gsize_diff d =
  match d with
    | ID l | RM l | ADD l | UP (l,_) -> Some (gsize l)
let opt_min a b =
  match a, b with
    | None, c | c, None -> c
    | Some l, Some r -> Some (min l r)
let min_list size_f cur_min ls =
  List.fold_left (fun a_min el -> opt_min a_min (size_f el)) cur_min ls

let find_smallest_level ps_list =
  match List.fold_left (min_list gsize_diff) None ps_list with
    | None -> (print_endline "no minimal size!"; 0)
    | Some n -> n

(* we consider it beneficial that atoms that are common among all drivers which
 * also change should not be abstracted
 *)

let find_changed_terms_pair freq_fun (gt1, gt2) = 
  let c_parts = get_ctf_diffs_all [] gt1 gt2 in
  let rec loop c_parts =
    match c_parts with
      | [] -> []
      | UP(t, t') :: parts -> 
	  (*print_string ("[Diff: considering atom: " ^ string_of_gtree' t);*)
	  if freq_fun t
	  then (
            (*print_endline " changed AND common";*)
            t :: loop parts)
	  else (
            (*print_newline ();*)
            loop parts)
      | _ :: parts -> loop parts in
    loop c_parts

let find_changed_terms freq_fun term_pairs =
  let changed_t_lists = List.map (find_changed_terms_pair freq_fun) term_pairs in
    filter_all changed_t_lists


let filter_safe (gt1, gt2) parts =
  List.filter (function bp -> safe_part bp (gt1, gt2)
    (* if safe_part bp (gt1, gt2) *)
    (* then true *)
    (* else ( *)
    (*   print_string "[Diff] unsafe part:\n\t"; *)
    (*   print_endline (string_of_diff bp); *)
    (*   false *)
    (* ) *)
  ) parts

    

(* two patches commute with respect to a changeset if the order in
   which they are applied does not matter (and the combined version is a
   safe part)
*)
let commutes chgset bp bp' =
  let bp1 = SEQ(bp,bp') in
  let bp2 = SEQ(bp',bp) in
    eq_changeset chgset bp1 bp2

let make_abs terms_changed fixf (gt1, gt2) =
  (* inital type annotation *)
  (* first make the list of concrete safe parts *)
  debug_msg "[Diff] getting safe concrete parts";
  let c_parts = get_ctf_diffs_safe [] gt1 gt2 in
    debug_msg ("[Diff] number of concrete parts: " ^ string_of_int (List.length c_parts));
    (* new generalize each such part and add it to our resulting list in case it
     * is not already there and in case it is still a safe part
     *)
    debug_msg "[Diff] finding abstract parts";
    let a_parts = List.flatten (
      List.map (function c_up ->
	  (filter_safe (gt1, gt2) (abs_term_noenv terms_changed fixf
				      should_abs_depth c_up)))
  	c_parts) in
      a_parts
	  (*print_endline "[Diff] removing duplicates";*)
	  (*let nodup_a_parts = rm_dub a_parts in*)
	  (*let nodup_a_parts = unique a_parts in*)
	  (*print_endline "[Diff] filtering unsafe parts";*)
	  (*let lct = ref (List.length nodup_a_parts) in*)
	  (*let safe_a_parts = List.filter *)
	  (*(function bp -> *)
	  (*if (!lct mod 10000 = 0)*)
	  (*then print_endline (string_of_int !lct);*)
	  (*lct := !lct - 1;*)
	  (*safe_part bp (gt1, gt2))*)
	  (*nodup_a_parts in*)
	  (*print_endline ("[Diff] removed "^*)
	  (*string_of_int (List.length nodup_a_parts - List.length a_parts) ^*)
	  (*" duplicates");*)
	  (*nodup_a_parts*)

	  
(*
  let make_sol fixf gt1 gt2 =
  let unabs_solutions = unabstracted_sol gt1 gt2 in
(*print_endline "unabs solutions";*)
(*print_sols unabs_solutions;*)
(*print_endline "starting abstraction";*)
(*let min_size = find_smallest_level unabs_solutions in*)
(*print_endline ("minimal term size: " ^ string_of_int min_size);*)

(* the unabs_solutions is now a list of possible patches that could 
  * update gt1 to gt2; 
  * 
*)
(*print_endline "renumbering metas";*)
  let all_perms = List.map (function sol ->
(*print_endline "abstracting the following solution now";*)
(*print_sol sol;*)
  gen_perms 
  (List.map (function up ->
(*print_endline ("\nhandling :::::" ^string_of_diff up);*)
(*(match up with (UP(l,_)) ->*)
(*print_endline ("of size  :::: " ^ (string_of_int (gsize l))));*)
  List.map renumber_metas_up (
  let rs = abs_term_noenv fixf should_abs up in
(*print_endline "\nwith result :::::";*)
(*List.iter (fun d -> print_endline (string_of_diff d)) rs;*)
(*print_endline ("\t#no of abstracted update: " ^ *)
(*string_of_int (List.length rs));*)
  rs
  )
  ) sol)
  ) unabs_solutions in
(*print_endline "flattening lists";*)
  let all_perms = (List.flatten all_perms) in
(*
  print_endline ("filtering " ^ string_of_int (List.length all_perms));
  let c = ref 0 in
  let all_perms = List.filter 
  (function patches -> (
  print_string (" " ^ string_of_int (inc c));
  flush stdout;
  if complete_patch gt1 gt2 patches
  then (
  print_string "#"; 
(*
  print_endline "keeping:";
  print_sol patches;
*)
  true)
  else (
  print_string "."; 
(*
  print_endline "removing:";
  print_sol patches;
*)
  false))
  ) all_perms in
  print_newline ();
*)
  all_perms
*)
(*
  let make_sol_old fixf gt1 gt2 =
  print_endline "dgts :::::::";
  let dgts = List.filter (function x -> match x with (ID _ | RM _ | ADD _)->
  false | _ -> true) (get_ctf_diffs always_dive [] gt1 gt2) in
  List.iter (fun d -> print_endline (string_of_diff d)) dgts;
  print_newline ();
  let parted = partition dgts in
  print_endline "parted::::::";
  List.iter print_diffs parted;
  debug_msg "partitioned sizes: ";
(*
  *List.iter (fun ec -> 
  *  debug_msg "<";
  *  debug_msg (string_of_int (List.length ec));
  *  debug_msg "> ";
  *  ) parted;
  *print_newline ();
*)
(*
  *List.iter 
  *  (fun ec -> 
  *    debug_msg "{{";
  *    List.iter (fun df ->
  *     debug_msg ((string_of_diff df) ^ " ++ ")) ec;
  *   debug_msg "\n}}")
  *  parted;
*)
  print_endline "making permuted by selecting one from each eq_class";
  let all_perms = gen_perms parted in
  print_endline "sorting reversed";
  let all_perms = List.map sort_rev all_perms in
  print_endline "collecting";
  let all_perms = List.map (fun d -> collect gt1 gt2 d) all_perms in
  print_endline "removing duplicates";
  let all_perms = rm_dub all_perms in
  print_string "number: ";
  print_endline (string_of_int (List.length all_perms));
  print_endline "renumbering metas";
  let all_perms = List.map (function sol ->
  gen_perms 
  (List.map (function up ->
  print_endline ("handling :::::" ^string_of_diff up);
  List.map renumber_metas_up (abs_term_noenv fixf should_abs up)
  ) sol)
  ) all_perms in
  print_endline "flattening lists";
  let all_perms = (List.flatten all_perms) in
  print_endline "filtering";
  let all_perms = List.filter 
  (function patches -> complete_patch gt1 gt2 patches) all_perms in
  all_perms
*)

let print_sol_lists sol_lists =
  List.iter 
    (fun sl -> 
      print_endline "<<<<<<< sol list >>>>>>>";
      if sl = []
      then
	print_endline "[]"
      else
	print_sols sl
    ) sol_lists
