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


let debug = false
let debug_msg x = if debug then print_endline x else ()
let fdebug_string f x = if f then print_string x else ()
let fdebug_endline f x = if f then print_endline x else ()
let debug_newline () = if debug then print_newline () else ()


exception Impossible of int
exception Unsafe

open Hashcons
open Gtree
open Gtree_util
open Env
open Difftype
open Util
			 
type term = gtree
type up = term diff

type node = gtree
type edge = Control_flow_c2.edge

type gflow = (node, edge) Ograph_extended.ograph_mutable

exception Merge3

module GT =
struct
  type t = gtree
  let compare = Pervasives.compare
end

module DiffT =
struct
  (*type t = (((string,string) gtree) diff) list*)
  type t = gtree diff
  let compare = Pervasives.compare
end


let pfold fold_f l opid concat = 
  List.fold_left (fun acc ls -> concat (fold_f ls acc) acc) opid l

(*
 *module DiffT =
 *  struct
 *    type t = ((string,string) gtree) diff
 *    let compare = Pervasives.compare
 *  end
 *
 *)

(* user definable references here ! *)
  (* copy from main.ml initialized in main-function *)
let patterns = ref false
let verbose = ref false
(* use new and fancy malign algo to decide subpatch relation *)
let malign_mode = ref false
  (* terms are only abstracted until we reach this depth in the term *)
let abs_depth     = ref 0 
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
  (* should we allow non-matching parts to be safe? 
  *)
let relax = ref false
  (* copy of the main.ml var with the same name; initialized in main.ml *)
let do_dmine = ref false
  (* copy from main.ml; initialized in main.ml *)
let nesting_depth = ref 0
  (* have we not already initialized the table of abstracted terms *)
let not_counted = ref true
(* should the type of expressions be printed inline ? *)
let inline_type_print = ref false

let v_print s = if !verbose then (print_string s; flush stdout)
let v_print_string = v_print
let v_print_endline s = if !verbose then print_endline s
let v_print_newline () = v_print_endline ""


(* non-duplicating cons *)
let (+++) x xs = if List.mem x xs then xs else x :: xs



(* convenience for application *)
let (+>) o f = f o

(* sublist *)
let sublist l1 l2 = l1 +> List.for_all (function e -> List.mem e l2)

(* equality of lists *)
let eq_lists l1 l2 = sublist l1 l2 && sublist l2 l1

let skip = mkA("SKIP","...")

(* check that list l1 is a sublist of l2 *)
let subset_list l1 l2 =
  List.for_all (function e1 -> (List.mem e1 l2)) l1

let string_of_meta p = match view p with
    (*| A ("meta", m) -> "$" ^ m*)
  | A ("meta", m) -> m
  | A (_, b) -> b
  | C _ -> raise (Fail "not meta")

let not_compound gt = match view gt with
  | C("comp{}", _) | A("comp{}", _) 
  | C("onedecl", _) 
  | C("onedecl_ini", _) -> false
  | _ -> true

let non_phony p = match view p with
  | A("phony", _) 
  | C("phony", _) -> false
(*
  | A(_, "N/H") 
  | A(_, "N/A") -> false
  | A(head,_)
  | C(head,_) -> not(is_header head)
*)
  | _ -> true

let is_assignment a_string = match a_string with 
  | "assign="
  | "assign+="
  | "assign-="
  | "assign*="
  | "assign%="
  | "assign/="
  | "assign&="
  | "assign|="
  | "assignx="
  | "assign?=?" -> true
  | _ -> false
      
let extract_aop a_string = match a_string with
  | "assign="  -> "="
  | "assign+=" -> "+="
  | "assign-=" -> "-="
  | "assign*=" -> "*="
  | "assign%=" -> "%="
  | "assign/=" -> "/="
  | "assign&=" -> "&="
  | "assign|=" -> "|="
  | "assignx=" -> "^="
  | "assign?=?" -> "?=?"
  | _ -> raise (Fail "Not assign operator?")

let rec string_of_gtree str_of_t str_of_c gt = 
  let rec string_of_itype itype = (match view itype with
             | A("itype", c) -> "char"
             | C("itype", [sgn;base]) ->
           (match view sgn, view base with
              | A ("sgn", "signed") , A (_, b) -> "signed " ^ string_of_meta base
              | A ("sgn", "unsigned"), A (_, b) -> "unsigned " ^ string_of_meta base
              | A ("meta", _), A(_, b) -> b
              | _ -> raise (Fail "string_of_itype inner")
           )
             | _ -> raise (Fail "string_of_itype outer")
          ) 
  and string_of_param param =
    match view param with
      | C("param", [reg;name;ft]) ->
          let r = match view reg with 
            | A("reg",r) -> r
            | A("meta",x0) -> string_of_meta reg 
            | _ -> raise (Fail "string_of_param reg") in
          let n = match view name with
            | A("ident", n) -> n
            | A("meta", x0) -> string_of_meta name 
            | _ -> raise (Fail "string_of_param name") in
            r ^ " " ^ string_of_ftype [ft] ^ " " ^ n
      | _ -> loop param
  and string_of_ftype fts = 
    let loc cvct = match view cvct with
      | A("tqual","const") -> "const"
      | A("tqual","vola")  -> "volatile"
      | A("btype","void")  -> "void"
      | C("btype", [{node=C("itype", _)} as c])   -> string_of_itype c
      | C("btype", [{node=A("itype", _)} as a])   -> string_of_itype a
      | C("btype", [{node=A("ftype", ft)}]) -> ft
      | C("pointer", [ft]) -> string_of_ftype [ft] ^ " * "
      | C("array", [cexpopt; ft]) ->
          string_of_ftype [ft] ^ " " ^
            (match view cexpopt with
               | A("constExp", "none") -> "[]"
               | C("constExp", [e]) -> "[" ^ loop e ^ "]"
               | A("meta", x0) -> string_of_meta cexpopt
               | _ -> raise (Fail "fail:array")
            )
      | C("funtype", rt :: pars) -> 
          let ret_type_string = string_of_ftype [rt] in
          let par_type_strings = List.map string_of_param pars in
            "("^ String.concat ", " par_type_strings 
            ^ ")->" ^ ret_type_string
      | C("enum", [{node=A ("enum_name", en)}; enumgt]) -> "enumTODO"
      | C("struct", [{node=C(sname, [stype])}]) -> 
          "struct " ^ sname ^ "{" ^ loop stype ^"}"
      | A ("struct", name) -> "struct " ^ name
      | C ("typeName", [{node=A("meta",id)}; {node=A("fullType","unknown")}])
      | C ("typeName", [{node=A("ident",id)}; {node=A("fullType","unknown")}]) -> id
      | C ("typeName", [{node=A("ident",id)}; ft]) 
      | C ("typeName", [{node=A("meta",id)}; ft]) -> string_of_ftype [ft] ^ " " ^ id
      | _ -> loop cvct
      (* | C(tp,ts) -> tp ^ "<" ^ String.concat ", " (List.map loop ts) ^ ">" *)
      (* | A(tp,t) -> tp ^ ":" ^ t ^ ":" *)
    in
      String.concat " " (List.map loc fts)
  and string_of_aop aop = match view aop with
    | A("aop", op_str) -> op_str
    | A("meta", x) -> x
    | _ -> raise (Impossible 1017)
  and none_exprstmt es = match view es with
    | C("stmt", [e]) when none_exprstmt e -> true
    | A("exprstmt", "none") -> true
    | _ -> false
  and loop gt = match view gt with
    | A ("meta", c) -> string_of_meta gt
        (*      | A ("itype", _) -> string_of_itype gt 
    | A (t,c) -> t ^ ":" ^ c *)
    | C ("cast", [totype; exp]) -> "(" ^ loop totype ^ ")" ^ loop exp
    | C ("if", [c;b1;b2]) ->
        "if(" ^ loop c ^") " ^ loop b1 ^
          (if none_exprstmt b2
           then ""
           else " else " ^ loop b2)
    | C ("binary_arith", [aop;e1;e2]) ->
        let aop_str = string_of_aop aop in
        let e1_str = loop e1 in
        let e2_str = loop e2 in
          e1_str ^ " " ^ aop_str ^ " " ^ e2_str
    | C ("fulltype", ti) -> string_of_ftype ti
    | C ("const", [{node=A(_, c)}]) -> c
    | C ("itype", _ ) -> string_of_itype gt
    | C ("exp", [e]) -> loop e 
        (*| C ("exp", [{node=A("meta", x0)}; e]) -> "(" ^ loop e ^ ":_)"*)
    | C ("exp", [{node=C ("TYPEDEXP", [t])} ; e]) ->
  if !inline_type_print
  then
          "(" ^ loop e ^ ":" ^ loop t ^ ")"
  else
          loop e
    | C ("call", f :: args) ->
        loop f ^ "(" ^ String.concat "," (List.map loop args) ^ ")"
    | C ("binary_logi", [{node=A("logiop", op_str)}; e1;e2]) ->
        loop e1 ^ op_str ^ loop e2
    | C ("record_ptr", [e;f]) -> 
        loop e ^ "->" ^ loop f
    | C ("record_acc", [e;f]) ->
        loop e ^ "." ^ loop f
    | C ("array_acc", [e1;e2]) ->
  loop e1 ^ "[" ^ loop e2 ^ "]"
    | C ("stmt", [st]) when not_compound st -> 
        loop st ^ ";"
    | C ("exprstmt", [gt]) -> loop gt
    | C (assignment, [l;r]) when is_assignment assignment ->
        loop l ^ extract_aop assignment ^ loop r
    | C ("&ref", [gt]) -> "&" ^ loop gt
    | C ("dlist", ds) -> 
        ds 
        +> List.map loop 
        +> String.concat ", " 
    | C ("onedecl", [v;ft;sto]) ->
        loop ft ^ " " ^ loop v(* storage and inline ignored *)
    | C ("onedecl_ini", [var_gt; ini_exp; ftype; stor]) ->
        loop ftype ^ " "
        ^ loop var_gt ^ " = " 
        ^ loop ini_exp
    | C ("ini", [e]) -> loop e
    | C ("stmt", [s]) -> loop s ^ ";"
    | C ("return", [e]) -> "return " ^ loop e
    | A ("goto", lab) -> "goto " ^ lab
    | C ("comp{}", compound) -> 
        "{" ^ 
          compound +> List.map loop +> String.concat " "
        ^ "}"
    | C ("def", [{node=A("fname", n)}; {node=C("funtype", rt :: args)}; body]) 
    | C ("def", [{node=A("meta", n)};  {node=C("funtype", rt :: args)}; body]) ->
        string_of_ftype [rt] ^ " " ^ n ^ " (" ^ 
          List.map string_of_param args +> String.concat ", "
        ^ ") " ^ 
          loop body
    | C ("cond3", [cond_gt;t_gt;f_gt]) ->
        loop cond_gt ^ " ? " ^
          loop t_gt ^ " : " ^
          loop f_gt
    | C ("argtype", [at]) ->loop at
    | C ("macroargs", args) -> 
        "(" ^ args +> List.map loop +> String.concat "," ^ ")"
    | C ("param", ps) -> string_of_param gt
    | C ("iniList", inis) -> 
        "{" ^ inis +> List.map loop
        +> String.concat ","
        ^ "}"
    | C (t, gtrees) -> 
        str_of_t t ^ "[" ^
          String.concat "," (List.map loop gtrees)
        ^ "]"
    | A (t,c) -> c
        (*      | A (t,c) -> str_of_t t ^ "<" ^ str_of_c c ^ ">" *)
  in
    loop gt

let verbose_string_of_gtree gt =
  let rec loop gt = match view gt with
      (*
  | A(t,c) -> t ^ "⟨" ^ c ^ "⟩"
  | C (t, gtrees) -> 
        t ^ "⟦" ^
        String.concat "," (List.map loop gtrees)
        ^ "⟧"
      *)
    | A(t,c) -> t ^ "(" ^ c ^ ")"
    | C (t, gtrees) -> 
        t ^ "[" ^
          String.concat "," (List.map loop gtrees)
        ^ "]"

  in loop gt

let str_of_ctype x = x
let str_of_catom a = a

let string_of_gtree' gt =	
  if !verbose
  then
    verbose_string_of_gtree gt
  else
    string_of_gtree str_of_ctype str_of_catom gt


let collect_metas gt = 
  let gs gt = match view gt with
    | A("meta",x) -> x ^ ";" 
    | _ -> raise (Fail "fail:collect_metas gs") in
  let (!!) gt = match view gt with
    | A("meta", _) -> true | _ -> false in
  let gtype gt = string_of_gtree' gt in
  let rec loop acc_metas gt = 
    if !!gt then (gs gt) +++ acc_metas
    else match view gt with
      | A _ -> acc_metas
      | C("const", [gt]) when !! gt -> ("const " ^ gs gt) +++ acc_metas
      | C("call", fargs) -> 
          fargs +> List.fold_left (fun acc_metas gt -> 
            match view gt with
              | _ when !! gt -> ("expression " ^ gs gt) +++ acc_metas
              | _ -> loop acc_metas gt
          ) acc_metas
      | C("exp",[gt']) when !!gt' -> ("expression " ^ gs gt') +++ acc_metas
      | C ("exp", [{node=C ("TYPEDEXP", [t])} ; e]) 
    when !!e -> (gtype t ^ " " ^ gs e) +++ acc_metas
      | C ("record_acc", [e;f]) -> 
          let acc = if !! f 
          then ("identifier " ^ gs f) +++ acc_metas 
            else loop acc_metas f in
            if !! e 
            then ("expression " ^ gs e) +++ acc
            else loop acc e
      | C ("record_ptr", [e;f]) -> 
          let acc = if !! f 
          then ("identifier " ^ gs f) +++ acc_metas 
            else loop acc_metas f in
            if !! e 
            then ("expression " ^ gs e) +++ acc
            else loop acc e
      | C (_, gts) -> gts +> List.fold_left 
    (fun acc_meta gt ->
      loop acc_meta gt
    ) acc_metas
  in
    loop [] gt
      
let rec string_of_diff d =
  let make_string_header gt = collect_metas gt in
    match d with
      | SEQ(p1,p2) -> "SEQ:  " ^ string_of_diff p1 ^ " ; " ^ string_of_diff p2
      | UP(s,s') -> 
    "@@\n" ^ String.concat "\n" (make_string_header s) ^
      "\n@@\n" ^
      "- " ^ (string_of_gtree' s) ^ 
      "\n" ^
      "+ " ^ (string_of_gtree' s')
      | ADD s -> "ADD:  " ^ string_of_gtree' s
      | ID s -> "ID:  " ^ string_of_gtree' s
      | RM s -> "RM:  " ^ string_of_gtree' s
      | PENDING_ID s -> "PID:  " ^ string_of_gtree' s
      | PENDING_RM s -> "PRM:  " ^ string_of_gtree' s

let print_diffs ds =
  print_endline "{{{";
  List.iter (fun d -> print_endline (string_of_diff d)) ds;
  print_endline "}}}"

let extract_pat p = match view p with
| C("CM", [p]) -> p
| _ -> raise (Match_failure (string_of_gtree' p, 772,0))

let rec string_of_spdiff d =
  let make_string_header gt = collect_metas gt in
    match d with
      | SEQ(p1,p2) -> "SEQ:  " ^ string_of_spdiff p1 ^ " ; " ^ string_of_spdiff p2
      | ID s when s == skip -> "  ..."
      | ID s -> "  " ^ extract_pat s +> string_of_gtree'
      | UP(s,s') -> "@@\n" ^ String.concat "\n" (make_string_header s) ^
                    "\n@@\n" ^
                    "- " ^ (string_of_gtree' s) ^ "\n" ^
                    "+ " ^ (string_of_gtree' s')
      | ADD s -> "+ " ^ s +> string_of_gtree'
      | RM s -> "- " ^ extract_pat s +> string_of_gtree'
      | _ -> failwith "Unhandled string_of_spdiff"

let string_of_spdiff_header sp =
  let meta_vars = List.fold_left 
    (fun acc_meta d -> 
      match d with 
      | ID s 
      | RM s
      | ADD s -> List.fold_left 
          (fun acc_ms meta -> meta +++ acc_ms) 
          acc_meta
          (collect_metas s)
      | _ -> acc_meta
    ) [] sp
  in
    "@@\n" ^ String.concat "\n" meta_vars ^ "\n" ^
    "@@"

let string_of_spdiff_full sp =
  string_of_spdiff_header sp ^ "\n" ^
  String.concat "\n" (List.map string_of_spdiff sp)


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

let max3 a b c = max a (max b c)

let lcs_shared size_f src tgt =
  let slen = List.length src in
  let tlen = List.length tgt in
  let m    = Array.make_matrix (slen + 1) (tlen + 1) 0 in
    Array.iteri 
      (fun i jarr -> Array.iteri 
   (fun j e -> 
      (* make sure we stay within the boundaries of the matrix *)
      let i = if i = 0 then 1 else i in
      let j = if j = 0 then 1 else j in
        (* get the values we need to compare in s and t *)
      let s = List.nth src (i - 1) in
      let t = List.nth tgt (j - 1) in
        (* now see how much of s and t is shared *)
      let size = size_f s t in
      let c = (try m.(i-1).(j-1) + size with _ -> size) in (* update/equal *)
      let a = try m.(i).(j-1) with _ -> 0 in (* adding is better *)
      let b = try m.(i-1).(j) with _ -> 0 in (* removing is better *)
        m.(i).(j) <- max3 a b c
   ) jarr) m; 
    m

let extract_base_name orig_s =
  try 
    let idx = String.index orig_s '@' in
    String.sub orig_s 0 idx
  with Not_found -> orig_s

let rec shared_gtree t1 t2 =
  let (+=) a b = if a = b then 1 else 0 in
  let rec comp l1 l2 =
    match l1, l2 with
      | [], _ | _, [] -> 0
          (* below: only do shallow comparison *)
          (*| x :: xs, y :: ys -> localeq x y + comp xs ys in*)
      | x :: xs, y :: ys -> shared_gtree x y + comp xs ys in
    match view t1, view t2 with
      | A ("ident", name1), A ("ident", name2) ->
    if extract_base_name name1 
      = extract_base_name name2
    then 0
    else 1
      | A (ct1, at1), A (ct2, at2) -> 
          (ct1 += ct2) + (at1 += at2)
      | C(ct1, ts1), C(ct2, ts2) ->
          (ct1 += ct2) + comp ts1 ts2
      | _, _ -> 0

let rec get_diff_old src tgt =
  match src, tgt with
    | [], _ -> List.map (function e -> ADD e) tgt
    | _, [] -> List.map (function e -> RM e) src
    | _, _ -> 
  let m = lcs_shared shared_gtree src tgt in
  let slen = List.length src in
  let tlen = List.length tgt in
  let rec loop i j =
    let i' = if i > 0 then i else 1 in
    let j' = if j > 0 then j else 1 in
    let s = List.nth src (i' - 1) in
    let t = List.nth tgt (j' - 1) in
      if i > 0 && j > 0 && (shared_gtree s t > 0)
      then
        let up = if s = t then ID s else UP(s,t) in
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

let rec get_diff src tgt =
  match src, tgt with
    | [], _ -> List.map (function e -> ADD e) tgt
    | _, [] -> List.map (function e -> RM e) src
    | _, _ -> 
  let m = lcs_shared shared_gtree src tgt in
  let slen = List.length src in
  let tlen = List.length tgt in
  let rec loop i j =
    if i > 0 && j = 0
    then
      loop (i - 1) j @ [RM (List.nth src (i - 1))]
    else if j > 0 && i = 0
    then
      loop i (j - 1) @ [ADD (List.nth tgt (j - 1))]
    else if i > 0 && j > 0
    then
      let s = List.nth src (i - 1) in
      let t = List.nth tgt (j - 1) in
      let score      = m.(i).(j) in
      let score_diag = m.(i-1).(j-1) in
      let score_up   = m.(i).(j-1) in
      let score_left = m.(i-1).(j) in
        if score = score_diag + (shared_gtree s t)
        then
    let up = if s = t then ID s else UP(s,t) in
      loop (i - 1) (j - 1) @ [up]
        else if score = score_left
        then
    loop (i - 1) j @ [RM (List.nth src (i - 1))]
        else if score = score_up
        then
    loop i (j - 1) @ [ADD (List.nth tgt (j - 1))]
        else raise (Fail "?????")
    else
      (assert(i=j && j = 0); [])
  in loop slen  tlen
       

(* normalize diff rearranges a diff so that there are no consequtive
 * removals/additions if possible.
 *)
let normalize_diff diff =
  let rec get_next_add prefix diff = 
    match diff with
      | [] -> None, prefix
      | ADD t :: diff -> Some (ADD t), prefix @ diff
      | t :: diff -> get_next_add (prefix @ [t]) diff
  in 
  let rec loop diff =
    match diff with
      | [] -> []
      | RM t :: diff' -> 
          let add, tail = get_next_add [] diff' in
            (match add with
               | None -> RM t :: loop tail
               | Some add -> RM t :: add :: loop tail)
      | UP(t,t') :: diff -> RM t :: ADD t' :: loop diff
      | i :: diff' -> i :: loop diff' in 
    loop diff

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

let correlate_diffs_new ds =
  if !Jconfig.verbose 
  then begin
    print_endline "[Diff] correlate new called on : ";
    ds +> List.map string_of_diff +> List.iter print_endline;
  end;
  let rec next_adds acc ds = 
    match ds with 
      | [] -> acc
      | ADD d :: ds -> next_adds (d :: acc) ds
      | RM _ :: ds 
      | UP _ :: ds -> next_adds acc ds
      | _ -> acc in
  let rec loop acc_ds prefix suffix = 
    match suffix with 
      | [] -> acc_ds
      | RM a :: suffix -> 
    let suffix_adds = next_adds [] suffix in
    let pre_suf_adds = next_adds suffix_adds prefix in
      if pre_suf_adds = []
      then acc_ds
      else pre_suf_adds +> List.fold_left 
        (fun acc_ds add -> 
     UP(a, add) :: acc_ds) acc_ds
      | up :: suffix -> loop (up :: acc_ds) (up :: prefix) suffix in
    loop [] [] ds 
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
  with Not_found -> (m,t) :: env

(* take two environments; for each binding of m that is in both env1 and env2,
 * the binding must be equal; for variables that are in only one env, we simply
 * add it
 *)
let merge_envs env1 env2 =
  List.fold_left (fun env (m,t) -> merge_update env (m,t)) env2 env1





(* try to see if a term st matches another term t
*)
let rec match_term st t =
  match view st, view t with
    | C("head:def", [defp]), C("head:def", [deft]) -> 
          match_term defp deft
    | A("meta",mvar), _ -> mk_env (mvar, t)
    | A(sct,sat), A(ct,at) when sct = ct && sat = at -> empty_env
  (* notice that the below lists s :: sts and t :: ts will always match due to
   * the way things are translated into gtrees. a C(type,args) must always have
   * at least ONE argument in args 
   *)
    | C("def", [namep;paramsp;bodyp]), C("def", [name;params;body]) ->
          match_term namep name +> merge_envs (match_term paramsp params)
    | C(sct,s :: sts), C(ct, t :: ts) 
      when sct = ct && List.length sts = List.length ts -> 
        List.rev (
          List.fold_left2 (fun acc_env st t ->
            merge_envs (match_term st t) acc_env
          ) (match_term s t) sts ts)
    | _ -> raise Nomatch


let is_read_only t = match view t with 
  | C("RO", [t']) -> true
  | _ -> false
let get_read_only_val t = match view t with
  | C("RO", [t']) -> t'
  | _ -> raise Nomatch

let mark_as_read_only t = mkC("RO", [t])

let can_match p t =
  try (match match_term p t with | _ -> true) 
  with
    | Nomatch -> false
    | _ -> raise (Impossible 191)

(* 
 * occursht is a hashtable indexed by a pair of a pattern and term 
 * the idea is that each (p,t) maps to a boolean which gives the result of
 * previous computations of "occurs p t"; if no previous result exists, one is
 * computed
 *)

module PatternTerm = struct
  type t = gtree * gtree
  let equal (p1,t1) (p2,t2) =
    p1 == p2 && t1 == t2
  let hash (p,t) = abs (19 * (19 * p.hkey + t.hkey) + 2)
end

module Term = struct
  type t = gtree
  let equal t t' = t == t'
  let hash t = t.hkey
end

module TT = Hashtbl.Make(Term)

module PT = Hashtbl.Make(PatternTerm)


(* hashtable for counting patterns *)
let count_ht = TT.create 591
let prepruned_ht = TT.create 591


(* let occursht = PT.create 591 *)

let find_match pat t =
  let cm = can_match pat in
  let rec loop t =
    cm t || match view t with
      | A _ -> false
      | C(ct, ts) -> List.exists (fun t' -> loop t') ts
  in
    loop t
   (* 
    try 
      if
  PT.find occursht (pat,t) 
      then true
      else (
    print_endline ("pattern: " ^ string_of_gtree' pat);
    print_endline ("not occurring in ");
    print_endline ("term: " ^ string_of_gtree' t); 
    print_newline ();
  false)

    with Not_found -> 
      let res = loop t in
  (PT.add occursht (pat,t) res; 
   res)
*)
let is_header head_str = 
  head_str.[0] = 'h' &&
  head_str.[1] = 'e' &&
  head_str.[2] = 'a' &&
  head_str.[3] = 'd'


let control_else = mkA("control:else", "Else")
let control_true = mkA("control:true", "True")
let control_inloop = mkA("control:loop", "InLoop")

let is_control_node n =
  n = control_else
  || n = control_true
  || n = control_inloop

let is_head_node n = 
  n = control_else ||
  n = control_inloop || 
  match view n with
  | C("head:def", _) -> false
  | A(hd,_ ) | C(hd, _ ) -> is_header hd


let find_nested_matches pat t =
  let mt t = try Some (match_term pat t) with Nomatch -> None in
  let rec loop depth acc_envs t = 
    if depth = 0
    then acc_envs
    else 
      let acc_envs' = (match mt t with
        | Some e -> e :: acc_envs
        | None -> acc_envs) in
        match view t with 
          | A _ -> acc_envs'
          | C(_, ts) -> let l = loop (depth - 1) in
                          List.fold_left l acc_envs' ts
  in
    (* loop !nesting_depth [] t *)
    if non_phony t
    then loop !nesting_depth [] t
    else []

let can_match_nested pat t =
  match find_nested_matches pat t with
    | [] -> false 
    | _ -> true

let return_and_bind (up,t) (t',env) = (
  t',env
)

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
      | _ -> raise (Fail "lcs stacks")

let get_slices lcs_orig ls_orig =
  let take_until e ls =
    let rec loop acc ls = match ls with
      | [] -> (
          let lcs_str = List.map string_of_gtree' lcs_orig +> String.concat " " in
          let ls_str = List.map string_of_gtree' ls_orig +> String.concat " " in
            print_endline "Exception";
            print_endline ("lcs: " ^ lcs_str);
            print_endline ("ls_str: " ^ ls_str);
            raise (Fail "get_slices:take_until "))
      | e' :: ls when e = e' -> List.rev acc, ls
      | e' :: ls -> loop (e' :: acc) ls
    in loop [] ls
  in
  let rec loop lcs ls =
    match lcs with
      | [] -> [ls]
      | e :: lcs -> let slice, ls = take_until e ls in 
                      slice :: loop lcs ls
  in loop lcs_orig ls_orig

let rec patience_diff ls1 ls2 =
  (* find the index of the given unique term t in ls *)
  let get_uniq_index ls t = 
    let rec loop ls n = match ls with
      | [] -> raise (Fail "not found get_uniq_index")
      | t' :: ls when t = t' -> n
      | _ :: ls -> loop ls (n + 1)
    in
      loop ls 0 in
    (* translate a list of terms from ls2 such that each term is replaced with its index in ls1 *)
  let rec to_nums c_uniq_terms = match c_uniq_terms with
    | [] -> []
    | t :: terms -> get_uniq_index ls1 t :: to_nums terms in
  let common_uniq = get_common_unique ls1 ls2 in
  let nums = to_nums common_uniq in
    (* translate a list of nums to their corresponding terms in ls1 *)
  let to_terms ns = List.map (List.nth ls1) ns in
  let lcs = nums +> patience_ref +> to_terms in
    if lcs = []
    then (* ordinary diff *) 
      get_diff ls1 ls2
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

let a_of_type t = mkA("nodetype", t)
let begin_c t = mkA("begin",t)
let end_c t = mkA("end",t)
    
let flatht = TT.create 1000001

let rec flatten_tree gt = 
  let loop gt =
    match view gt with 
      | A _ -> [gt]
    (*| C(t, gts) -> List.fold_left (fun acc gt -> List.rev_append (flatten_tree gt) acc) [] gts*)
(*
      | C(t, gts) -> a_of_type t :: List.fold_left 
             (fun acc gt -> List.rev_append (flatten_tree gt) acc) 
             [] (List.rev gts)
*)
      | C(t, gts) -> 
    begin_c t ::
      List.fold_left
      (fun acc gt -> List.rev_append (flatten_tree gt) acc) 
      [end_c t] (List.rev gts)
  in 
    try 
      TT.find flatht gt
    with Not_found ->
      let 
    res = loop gt in
  (
    TT.add flatht gt res;
    res
  )

let rec linearize_tree gt =
  let rec loop acc gt = 
    match view gt with
      | A _ -> gt +++ acc
      | C(_, gts) -> gts +> List.fold_left loop (gt +++ acc)
  in
    loop [] gt

let tail_flatten lss =
  lss +> List.fold_left List.rev_append []

let get_tree_changes (gt1, gt2) =
  let is_up op = match op with UP _ -> true | _ -> false in
  let get_ups up = match up with
          | (UP(gt1,gt2)) ->
                if gt1 = gt2 then []
                else (match view gt1, view gt2 with
                      | C(t1, gts1), C(t2, gts2) when t1 = t2 ->
                                (patience_diff gts1 gts2
                                +> correlate_diffs_new
                                +> List.filter is_up)
                      | _, _ -> [])
          | _ -> raise (Fail "get_tree_changes get_ups") in
  let (@@) ls1 ls2 = ls1 +> List.fold_left (fun acc_ls e -> e +++ acc_ls) ls2 in
  let rec loop work acc = match work with 
                | [] -> acc
                | up :: work ->
                    let new_work = get_ups up in
                    loop (new_work @@ work) (up :: acc) in
  if gt1 = gt2
  then []
  else loop [UP(gt1,gt2)] []


let editht = PT.create 1000001


type 'a label = V of 'a | L

let get_tree_label t = match view t with
  | A (c,l) -> c^l
  | C(l,_) -> l

let label_dist l1 l2 = match l1, l2 with
  | L, L -> 0
  | L, _ | _, L -> 1
  | V t1, V t2 -> 
      if get_tree_label t1 = get_tree_label t2
      then 0
    else 1


let min3 a b c = min a (min b c) 

  (*
  if b < c 
  then if a < b
  then (print_endline "a"; a)
  else (print_endline "b"; b)
  else if a < c 
  then (print_endline "a"; a)
  else (print_endline "c"; c)
*)

exception Rm_leftmost

let rm_leftmost f1 =
        match f1 with
        | [] -> raise Rm_leftmost
        | t :: f -> (match view t with
          | A _ -> t, f
          | C(_, ts) -> t, ts @ f)

exception Rm_leftmost_tree

let rm_leftmost_tree f1 = match f1 with
  | [] -> raise Rm_leftmost_tree
  | _ :: f -> f

let get_head_forest f = match f with
  | [] -> raise (Fail "empty forest in get_head_forest")
  | t :: _ -> (match view t with
    | A _ -> []
    | C(_,ts) -> ts)

let get_leftmost f = match f with
  | [] -> raise (Fail "no leftmost")
  | t :: _ -> t

let rec forest_dist f1 f2 =
  match f1, f2 with
    | [], [] -> 0
    |  _, [] -> let v, f1' = rm_leftmost f1 in
         forest_dist f1' f2 + 
           label_dist (V v) L
    | [],  _ -> let w, f2' = rm_leftmost f2 in
        forest_dist f1 f2' +
          label_dist L (V w)
    |  _,  _ -> 
   let v, f1mv = rm_leftmost f1 in
   let w, f2mw = rm_leftmost f2 in
     min3 
             (
         forest_dist f1mv f2 + label_dist (V v) L
             )
             (
         forest_dist f1 f2mw + label_dist L (V w)
             )
             (let f1v  = get_head_forest f1 in
              let f2w  = get_head_forest f2 in
              let f1mv = rm_leftmost_tree f1 in
              let f2mw = rm_leftmost_tree f2 in
    forest_dist f1v f2w +
      forest_dist f1mv f2mw +
      label_dist (V v) (V w)
             )


let minimal_tree_dist t1 t2 = forest_dist [t1] [t2]

let rec msa_cost gt1 gt2 gt3 =
  gt1 = gt2 || gt2 = gt3 ||
  match view gt1, view gt2, view gt3 with
    | C(ty1,ts1), C(ty2,ts2), C(ty3,ts3) when 
  ty1 = ty2 || ty2 = ty3 ->
  Msa.falign msa_cost 
    (Array.of_list ts1)
    (Array.of_list ts2)
    (Array.of_list ts3)
    | _ -> false
(*
  let seq1 = Array.of_list (flatten_tree gt1) in
  let seq2 = Array.of_list (flatten_tree gt2) in
  let seq3 = Array.of_list (flatten_tree gt3) in
  let callb t1 t2 t3 = t1 = t2 || t2 = t3 in
    Msa.falign callb seq1 seq2 seq3
*)

let rec edit_cost gt1 gt2 =
  let rec node_size gt = match view gt with
    | A _ -> 1
    | C (_, ts) -> ts +> List.fold_left (fun sum t -> sum + node_size t) 1 in
  let up_cost up = match up with
    | ID _ -> 0
    | RM t | ADD t -> node_size t
    | UP (t1,t2) when t1  = t2 -> 0
    | UP (t,t') -> node_size t + node_size t'
    | _ -> raise (Fail "edit_cost upcost") in
  let rec get_cost_tree gt1 gt2 = 
    if gt1 = gt2 then 0
    else 
      match view gt1, view gt2 with
      | C(t1,gts1), C(t2,gts2) -> 
          (if t1 = t2 then 0 else 1) + (
            patience_diff gts1 gts2 
            +> List.fold_left (fun acc_sum up -> match up with
                    | UP(t1,t2) -> edit_cost t1 t2 + acc_sum
                    | _ -> up_cost up + acc_sum) 0)
      | _ -> up_cost (UP(gt1,gt2)) in
  try
    PT.find editht (gt1,gt2)
  with Not_found ->
      let res = get_cost_tree gt1 gt2 in
      begin
        PT.add editht (gt1,gt2) res;
        res
      end
  

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
        (* For a sequence, we must actually apply all embedded rules in parallel
         * so that the result of applying rule1 is never used for rule2 otherwise
         * the presence of p->p' and p'->p would cause the inference to never
         * terminate! At the moment we silently ignore such cases!
         *)
        (* ---> this is old code <--- *)
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
        (*
         * This is where we now wish to introduce the occurs check using
         * a hashtable to memoize previous calls to "find_match"
         *)
        if not(find_match src t)
        then raise Nomatch
        else
          (match view src, view t with
            | A ("meta", mvar), _ -> 
                let env = mk_env (mvar, t) in 
                  return_and_bind  (up, t) (sub env tgt,env)
            | A (sct, sat), A(ct, at) when sct = ct && sat = at ->
                return_and_bind  (up, t) (tgt, empty_env)
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
                      return_and_bind  (up,t) (res, fenv)
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
                      then return_and_bind  (up,t) (mkC(ct, List.rev ft), empty_env)
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
                  then return_and_bind  (up,t) (mkC(ct, List.rev ft), empty_env)
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


and traverse pred work lhs rhs =
(*
  let rec add_ups pred ups work = 
    List.fold_left pred work ups in
*)
  let rec loop work t t' = match view t, view t' with
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
and isid_up up = match up with
  | UP(a,b) -> a = b
  | _ -> false

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
      match view t1, view t2, view t3 with
  | C(ct1, ts1), C(ct2, ts2), C(ct3, ts3) when ct1 = ct2 || ct2 = ct3
      -> fold_left3 m3 true ts1 ts2 ts3
  | _, _, _ -> false
and malign' s1 s2 s3 = 
  (s1 = [] && s2 = [] && s3 = [])
  || (try (List.hd s1 = List.hd s2 && malign' (List.tl s1) (List.tl s2) s3)
      with _ -> false)
  || (try (List.hd s2 = List.hd s3 && malign' s1 (List.tl s2) (List.tl s3))
      with _ -> false)
  || (try (malign' s1 s2 (List.tl s3))
      with _ -> false)
  || (try (malign' (List.tl s1) s2 s3)
      with _ -> false)
  || (try (merge3 (List.hd s1) (List.hd s2) (List.hd s3) 
     && malign' (List.tl s1) (List.tl s2) (List.tl s3)
    )
      with _ -> false)
and malign s1 s2 s3 = 
  let rec get_list e s = match s with
    | [] -> raise (Fail "get_list")
    | e' :: s when e = e' -> s
    | _  :: s -> get_list e s in
  let subseq s1 s2 = 
    let rec sloop s1 s2 =
      s1 = [] || match s1 with
  | [] -> true
  | e :: s1 -> sloop s1 (get_list e s2) in
      if List.length s1 > List.length s2
      then false
      else
  if (try sloop s1 s2 with _ -> false)
  then 
    true
      else 
  false in
    (* lists of all suffixes of ls (incl. ls) *)
  let rec tail_lists acc ls = match ls with
    | [] -> [] :: acc
    | x :: xs -> tail_lists ((x :: xs) :: acc) xs in
  let rec loop s1 s2 s3 = 
    match s1, s2, s3 with
      | s1, [], [] -> true (* the rest of s1 was deleted *)
      | [], [], s3 -> true (* the rest of s3 was added *)
      | [], _ , _  -> subseq s2 s3 (* s2 adds elems iff it is a subseq of s3 *)
      | e1 :: s1', e2 :: s2', e3 :: s3' when e1 = e2 -> 
    (* e1 = e2 
       => loop s1' s2' [s3]
    *)
    tail_lists [] s3 +> List.fold_left (fun res tl ->
      loop s1' s2' tl || res) false 
      | e1 :: s1', e2 :: s2', e3 :: s3' when e2 = e3 -> 
    (* e2 = e3 
       => loop [s1] 
    *)
    tail_lists [] s1 +> List.fold_left (fun res tl ->
      loop tl s2' s3' || res) false
      | _, _, _ -> false
  in
    loop s1 s2 s3
(*
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
*)
and part_of_malign gt1 gt2 gt3 =
  gt1 = gt2 || gt2 = gt3 || 
  (print_endline "[Diff] flattening";
   let f_gt1 = flatten_tree gt1 in
   let l1    = List.length f_gt1 in
   let f_gt2 = flatten_tree gt2 in
   let l2    = List.length f_gt2 in
   let f_gt3 = flatten_tree gt3 in
   let l3    = List.length f_gt3 in
     print_endline ("[Diff] malign "
         ^ string_of_int l1 ^ " "
         ^ string_of_int l2 ^ " "
         ^ string_of_int l3
     );
     print_endline (String.concat " " (f_gt1 +> List.map string_of_gtree'));
     print_endline (String.concat " " (f_gt2 +> List.map string_of_gtree'));
     print_endline (String.concat " " (f_gt3 +> List.map string_of_gtree'));
     let r = malign' f_gt1 f_gt2 f_gt3 in
       print_endline "[Diff] return";
       r)

and part_of_edit_dist gt1 gt2 gt3 =
  let dist12 = edit_cost gt1 gt2 in
  let dist23 = edit_cost gt2 gt3 in
  let dist13 = edit_cost gt1 gt3 in
  if dist12 + dist23 < dist13
  then (
(*    string_of_gtree' gt1 +> print_endline;    
    string_of_gtree' gt2 +> print_endline; 
    string_of_gtree' gt3 +> print_endline;
    ("12: " ^ string_of_int dist12 ^ " 23: " ^ string_of_int dist23 ^ 
    " 13: " ^ string_of_int dist13) +> print_endline;
*)
    false
    (*raise (Fail "<")*)
   )    
  else
    dist12 + dist23 = dist13

(* is up a safe part of the term pair (t, t'') 
 *
 * bp<=(t,t')
 *)
and safe_part up (t, t'') =
  (*
    print_endline "[Diff] safe_part : ";
    print_endline (string_of_diff up);
  *)
  try 
    let t' = apply_noenv up t in
      if !malign_mode
      then 
(*   part_of_malign t t' t'' (* still too slow *) *)
        part_of_edit_dist t t' t'' 
(*  msa_cost t t' t'' *)
      else 
        merge3 t t' t''
  with (Nomatch | Merge3) -> (
    if !Jconfig.print_abs
    then (
      print_string "[Diff] rejecting:\n\t";
      print_endline (string_of_diff up);
			print_endline ("relative to: " ^ (string_of_diff (UP(t,t''))))
    );
    false)

and relaxed_safe_part up (t, t'') =
    let t' = apply_noenv up t in
      merge3 t t' t''

(* is the basic patch bp safe with respect to the changeset 
 *
 * bp<=C
 * *)

and safe_part_changeset bp chgset = 
  let cnt = ref 0 in
  if List.for_all (
    function (t,t') ->
      try
        let t'' = apply_noenv bp t in
        if part_of_edit_dist t t'' t'
        then (cnt := !cnt + 1; true)
        else false
      with Nomatch -> true
  ) chgset
  then (
    !cnt >= !no_occurs
  ) else false
and list_choose ls f =
	ls
	+> List.map f
	+> List.filter (fun x -> x <> None)
	+> List.map (fun (Some x) -> x)

and safe_part_changeset_with_changeset bp chgset threshold =
	let is_safe (t, t') =
      try
        let t'' = apply_noenv bp t in
        if part_of_edit_dist t t'' t'
        then Some(t,t'')
        else (print_endline "Unsafe!"; raise Unsafe)
      with Nomatch -> None
	in
	try
		let chop = list_choose chgset is_safe
		in
		if List.length chop >= threshold
		then Some chop
		else None
	with Unsafe -> None

and safe_part_changeset_unsafe bp chgset = 
  for_some !no_occurs (safe_part bp) chgset

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
  match safe_part_changeset_with_changeset bp' chgset !no_occurs with
	| Some chop -> (
     match safe_part_changeset_with_changeset bp chop (List.length chop) with
		 | Some chop' -> List.length chop = List.length chop'
		 | None -> false)
	| None -> false
      

and get_ctf_diffs_all work gt1 gt2 =
  let all_pred lhs rhs w u =
    if 
      not(List.mem u w) 
      && (match u with | UP(a,b) -> not(a = b) 
                       | _ -> failwith "Unexpected at get_ctf_diffs_all")
    then u :: w
    else w
    in
      traverse (all_pred gt1 gt2) work gt1 gt2

and get_ctf_diffs_safe work gt1 gt2 =
    let all_pred lhs rhs w u =
      if not(List.mem u w) && 
         (match u with 
          | UP(a,b) -> not(a = b)
          | RM a -> true
          | _ -> failwith "Unexpected at get_ctf_diffs_safe")
         && safe_part u (gt1, gt2)
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






type environment = (string * gtree) list
type res = {last : int option; skip : int list ; env : environment}
type res_trace = {last_t : int option; skip_t : int list; env_t : environment ; trace : int list}

let print_environment env =
  List.iter (function (x, v) ->
    print_string " ;";
    print_string (x ^ " -> " ^ string_of_gtree' v);
  ) env; print_newline ()

let bind env (x, v) = 
  try match List.assoc x env with
    | v' when not(v=v') -> raise (Match_failure ("Diff.bind: " ^
                x ^ " => " ^
                string_of_gtree' v ^ " != " ^
                string_of_gtree' v' , 1232, 0))
    | _ -> env
  with Not_found -> (x,v) :: env

let string_of_bind string_of_val (x, v) = 
  "(" ^ x ^ "->" ^ string_of_val v ^ ")"

let string_of_env env = 
  String.concat "; " (List.map (string_of_bind string_of_gtree') env)

let extend_env env1 env2 =
  List.fold_left bind env1 env2
let ddd = mkA("SKIP", "...")
let (%%) e1 e2 = extend_env e1 e2
let (=>) (k,v) env = bind env (k,v)
let get_val n g = g#nodes#find n
let get_succ n g = 
  match (g#successors n)#tolist with
    | [] -> []
(*
  (
    raise Nomatch
  )
*)
    | ns -> ns

let get_next_vp'' g vp n = 
  List.rev_map fst (get_succ n g) 
    (* below we filter those, that have already be visited
       let ns = get_succ n g in
       List.fold_left (fun acc_n (n',_) -> 
       if not(List.mem n' vp.skip)
       then n' :: acc_n
       else acc_n) [] ns
    *)


type skip_action = SKIP | LOOP | FALSE | ALWAYSTRUE

let is_error_exit t = 
  match view t with
  | A("phony", "[errorexit]") -> true
  (* | A("phony", "[after]") -> true *)
  | _ -> false


let string_of_pattern p =
  let loc p = match view p with
    | C("CM", [t]) -> string_of_gtree' t
    | skip when skip == view ddd -> "..."
    | gt -> raise (Match_failure (string_of_gtree' p, 1263,0)) in
    String.concat " " (List.map loc p)

exception ErrorSpec
(*
let cont_match_spec spec g cp n =
  let init_vp = {skip = []; env = []; last = None;} in 
  let matched_vp vp n env = 
    (* let f, env' = try true, env %% vp.env with Bind_error -> false, [] in *)
    (* in this semantic, we never allow visiting the same node twice *)
    let f, env' = try 
  not(List.mem n vp.skip) && 
    not(List.exists (function nh -> get_val nh g = get_val n g ) vp.skip)
    , env %% vp.env with Match_failure _ -> false, [] in
      f, {last = Some (get_val n g); skip = n :: vp.skip; env = env'} in
  let skipped_vp vp n = {
    last = vp.last;
    skip = n :: vp.skip; 
    env = vp.env} in
  let check_vp vp n  = 
    let t_val = get_val n g in
      if Some t_val = vp.last
      then FALSE 
      else if List.mem n vp.skip
      then (
  (* print_endline ("[Diff] LOOP on " ^ 
           string_of_int n); *)
  LOOP)
      else if is_error_exit t_val 
      then ALWAYSTRUE
      else SKIP
  in
  let rec trans_cp cp c = match cp with
    | [] -> c
    | bp :: cp -> trans_bp bp (trans_cp cp c)
  and trans_bp bp c vp n = match view bp with
    | C("CM", [gt]) ->
  (try 
            let env = spec gt (get_val n g) in
            let f,vp' = matched_vp vp n env in
              f && List.for_all (function (n',_) -> c vp' n') (get_succ n g)
    with Nomatch -> false)
    | _ when bp == ddd ->
  c vp n || (
          match check_vp vp n with
            | FALSE -> false
            | LOOP -> true
            | SKIP -> 
    let ns = get_next_vp'' g vp n in
                  not(ns = []) &&
        ns +> List.exists (function n' -> not(n = n'))
                  &&
                    let vp' = skipped_vp vp n in
                      List.for_all (trans_bp ddd c vp') ns
      | ALWAYSTRUE -> true
  )
  in
  let matcher = trans_cp cp (fun vp x -> true) in
    try matcher init_vp n with ErrorSpec -> false

let find_embedded_succ g n p =
  let spec pat t = if find_match pat t then [] else raise ErrorSpec in
  let ns = (g#successors n)#tolist in
    if ns = []
    then (print_endline ("[Diff] term: " ^ string_of_gtree' (get_val n g) ^ " has no successors");
    true)
    else 
      List.for_all (function (n, _) -> cont_match_spec spec g [ddd; mkC("CM", [p])] n) ((g#successors n)#tolist)
*)

(* returns true if node with index n in graph g is an errorexit
   return/exit-node; this is the case when the unique successor to n
   is head/phony/control and eventually an errorexit node or if the
   node value matches "return X"
*)

let rec matches_exit node_gt =
  match view node_gt with
    | C("return", _) 
    | C("exit", _) -> true
    | C(_, ns) -> ns +> List.exists matches_exit
    | _ -> false

let is_exit_index g (n : int) =
  let rec loop cur_idx =
    let node_val = get_val cur_idx g in
      if is_error_exit node_val
      then true
      else next cur_idx
  and next n =
    match get_succ n g with
      | [(n',_)] ->
    let node_val = get_val n' g in
        (not(non_phony node_val) || is_head_node node_val)
        && loop n'
      | _ -> false
  in
    matches_exit (get_val n g) || loop n


let valOf x = match x with
  | None -> raise (Fail "valOf: None")
  | Some y -> y

      
let traces_ref = ref []
let envs_ref = Hashtbl.create 117

let print_trace tr =
  print_string ("[Diff] " ^ string_of_int (List.length tr) ^ ": ");
  tr +> List.iter 
    (function i_list -> 
      print_string ("<" ^ List.length i_list +> string_of_int ^ ">");
      print_string "[[ ";
      i_list 
      +> List.map string_of_int
      +> String.concat " > "
      +> print_string;
      print_string "]] "
    );
  print_newline ()


let get_fun_name_gflow f =
  let head_node = f#nodes#tolist +> List.find (function (i,n) -> match view n with
    | C("head:def", [{node=C("def",_)}]) -> true
    | _ -> false) in
    match view (snd head_node) with
      | C("head:def",[{node=C("def",name::_)}]) -> (match view name with
          | A("fname",name_str) -> name_str
    | _ -> raise (Fail "impossible match get_fun_name_gflow")
  )
      | _ -> raise (Fail "get_fun_name?")


exception Bailout
exception UNSAT

exception Fatal_error

type dfs_action = 
  | STOP
  | NOT_FOUND

let dfs_iter_with_path xi f g = 
  let already = Hashtbl.create 101 in
  let rec aux_dfs path xi = 
    if Hashtbl.mem already xi then ()
    else begin
      Hashtbl.add already xi true;
      match f xi path with
      | STOP-> ()
      | NOT_FOUND ->
        let succ = g#successors xi in
        let succ' = succ#tolist +> List.map fst in
        succ' +> List.iter (fun yi -> 
            aux_dfs (xi::path) yi
        );
      end
  in
  aux_dfs [] xi
  
    


let get_match pattern gt = 
  match view pattern with
  | C("CM", [pat]) -> begin
        match find_nested_matches pat gt with
        | [env] -> env
        | _ -> raise Fatal_error
    end
  | _ -> raise Fatal_error

(* Find the first matches of node_p starting from 
 * from_n in g. On each path to node_p there can 
 * be no occurrences of node_p or (get_val from_n)
 *
 * also: if from_node matches an exit-node, there are no successors
 *)
let get_succ_nodes env node_p from_n g =
  let from_node = get_val from_n g in
  if matches_exit from_node
  then []
  else 
    let res_nodes = ref [] in
    let f xi node_path =
      let xi_val = get_val xi g in
      if xi_val = from_node 
      then 
        if node_path = []
        then NOT_FOUND (* skip the initial node that we started in *)
        else STOP (* we encountered the from_node along some non-empty path*)
      else 
        try
          let env' = get_match node_p xi_val in
          begin
            try
              let _ = merge_envs env env' in
              res_nodes := xi :: !res_nodes;
              STOP
            with _ -> NOT_FOUND
          end
        with Fatal_error | Nomatch -> 
          NOT_FOUND
    in begin 
      dfs_iter_with_path from_n f g;
      !res_nodes
    end


let cont_match_new_internal (g : gflow) cp n =
  let rec loop cp n = 
    match cp with
    | [] -> raise Fatal_error
    | [np] -> 
        begin
          match view np with
          | C("CM", [gt]) -> (* check that gt matches n and return a singleton
          list with a single pair of (n, env) *)
            let envs = 
              try find_nested_matches gt (get_val n g)
              with Nomatch -> [] in
            (* there should actually only be one match because of a
             * simplification that we never use a nesting_depth > 1
             *)
            begin match envs with
            | [env] -> [([n], env)]
            | _ -> raise Fatal_error
            end
          | _ -> raise Fatal_error
        end
    | np1 :: nddd :: np2 :: rest 
      when view nddd == view ddd ->
        begin
          (* check that npv1 matches n *)
          let env1 = get_match np1 (get_val n g) in
          (* find all nodes matching npv2 reachable from n;
           * this can be implemented by dfs_search from n *)
          (* for each node : compute witnesses *)
          let nodes2 = get_succ_nodes env1 np2 n g in
          (* for each succ-node: combine with match of npv1 *)
          List.fold_left
          (fun acc_ws succ_node -> 
            (* traces_succ : (matched_nodes * env) list *)
            let traces_succ = loop (np2 :: rest) succ_node in
            (* for each trace: try to merge with current env1 and prefix n *)
            List.fold_left (fun acc_traces (match_nodes, env') ->
              try 
                let env'' = merge_envs env1 env' in
                (n :: match_nodes, env'') :: acc_traces
              with Nomatch -> acc_traces 
            ) acc_ws traces_succ
          ) [] nodes2
        end
    | _ -> 
        begin
          raise Fatal_error
        end
  in
    loop cp n

let cont_match_new g sp n =
  if !Jconfig.to_print then print_endline ("[Diff] matching " ^ string_of_pattern sp ^ " on node " ^ string_of_int n);
    try 
      match cont_match_new_internal g sp n with
      | [] -> false
      | r -> true
    with Fatal_error | Nomatch -> false

let cont_match_traces_new g sp n =
  try 
    match cont_match_new_internal g sp n with
    | [] -> None
    | r  -> Some r
  with Fatal_error | Nomatch -> None

(*
   * Given a graph g, semantic pattern sp, and node of graph n, this function
   * tries to figure out whether the pattern matches starting at the node given.
   * if the node matches, the function returns a 'trace' of how the node
   * matched. (wrapping in the option type)
   * A trace is a list of pairs. The first component of the pair is a list of
   * nodes corresponding to where each node pattern in the given semantic
   * pattern matched the graph. The second component of the pair is the
   * environment used to make the node patterns match along the 'path' matched.
   *)

let cont_match_param matcher g cp n = 
  let can_have_follow vp =
    match vp.last_t with
    | None -> true
    | Some n_last -> not(is_exit_index g n_last)
  in
  let init_vp = {skip_t = []; env_t = []; last_t = None; trace = []} in 
  let matched_vp vp n env = 
    (* let f, env' = try true, env %% vp.env with Bind_error -> false, [] in *)
    (* in this semantic, we never allow visiting the same node twice *)
    let f, env' = try 
      not(List.mem n vp.skip_t) 
      && not(List.exists (function nh -> get_val nh g = get_val n g ) vp.skip_t)
      && can_have_follow vp 
      , env %% vp.env_t with Match_failure _ -> false, [] in
    f, {
      last_t = Some n; 
      skip_t = n :: vp.skip_t; 
      env_t = env'; 
      trace = n :: vp.trace
  } in
  let skipped_vp vp n = {
    last_t = vp.last_t;
    skip_t = n :: vp.skip_t; 
    env_t = vp.env_t;
    trace = vp.trace;
    } in
  let check_vp vp n  = 
    let t_val = get_val n g 
    in
      if Some t_val = 
        (try Some (get_val (valOf vp.last_t) g) with (Fail _) -> None)
      then FALSE 
      else if List.mem n vp.skip_t
      then (
        (*print_endline ("[Diff] LOOP on " ^ string_of_int n);*)
        LOOP)
      else if is_error_exit t_val 
      then raise Bailout
      else if can_have_follow vp
      then SKIP
      else FALSE 
    (* we are trying to skip when the previous match did not have
    (should not have) successors *)
  in
  let rec trans_cp cp c = match cp with
    | [] -> c
    | bp :: cp -> trans_bp bp (trans_cp cp c)
  and trans_bp bp c vp n = match view bp with
  | C("CM", [gt]) -> (
    try 
    (* let env = match_term gt (get_val n g) in *)
    let envs = 
      try 
        let res = find_nested_matches gt (get_val n g)
        in
        begin
          res
        end     
      with Nomatch -> []
    in
      List.exists 
      (function env ->
          let f,vp' = 
            try matched_vp vp n env 
            with Nomatch -> begin
              print_endline "matched_vp raising Nomatch";
              raise Nomatch
            end
          in
            if f
            then
              begin
                (*print_endline (">>> match: " ^ string_of_int n ^ " : " ^ string_of_gtree' gt);*)
                try 
                  List.exists (*for_all*) 
                  (function (n',_) -> 
                    try c vp' n'
                    with Nomatch -> raise Nomatch) 
                  (get_succ n g)
                with Nomatch -> raise Nomatch
              end
            else false) 
      envs 
    with Nomatch -> false)
  | _ when bp == ddd ->
      c vp n || (
        match check_vp vp n with
        | FALSE -> raise UNSAT
        | SKIP 
        | LOOP -> 
            begin
              (* we've reached a loop; we should continue with the remaining
               * pattern (as represented by the current continuation) but
               * not _follow_ a path that leads back to where we came
               *)
              v_print_endline "L";    
              let ns = 
                get_next_vp'' g vp n 
                +> List.filter 
                   (function n' -> 
                       let r = not(n = n' || List.mem n' vp.skip_t) in
                       if r
                       then begin
                         v_print_endline("[" ^ string_of_int n ^ "->" ^ string_of_int n' ^ "]");
                         r
                       end
                       else begin
                         v_print_endline("<" ^ string_of_int n ^ "->" ^ string_of_int n' ^ ">");
                         r
                       end
                   )  
                (* remove current and previous from succs *)
              in
                not(ns = []) &&
                let vp' = skipped_vp vp n
                in
                  List.exists (function n' -> 
                      let r = try trans_bp ddd c vp' n' with Bailout -> false in
                      begin
                        if r
                        then v_print_endline ("true: " ^ string_of_int n ^ "->" ^ string_of_int n')
                        else begin
                          v_print_endline ("false: "^ string_of_int n ^ "->" ^ string_of_int n');
                          v_print_endline ("skipped: " ^ String.concat " " (List.map string_of_int (n :: vp'.skip_t)));
                        end;
                        r
                      end
                  ) ns
            end
        | ALWAYSTRUE -> 
            begin
              print_endline ("TOP: " ^ string_of_int n);
              true
            end
            )
        | _ -> raise (Match_failure (string_of_gtree' bp, 1429,0))
      in
      let real_matcher = 
        trans_cp cp matcher
    in
    begin
      (*print_endline ("## " ^ String.concat " " (List.map string_of_gtree' cp));*)
      try real_matcher init_vp n with UNSAT -> (traces_ref := []; false)
    end

let cont_match_traces g sp n =
  let matcher vp x = 
    begin
      traces_ref := List.rev (vp.trace) :: !traces_ref; (* recall that indices come in reverse order *)
      true
    end 
  in
    cont_match_param matcher g sp n

let matching_ht = Hashtbl.create 319

let cont_match (g : gflow) sp n =
  traces_ref := [];
  let result =
    try 
      let res = Hashtbl.find matching_ht (g,sp,n)
      in begin
        (*print_string "Cache HIT : ";*)
        (*sp +> List.map string_of_gtree' +> String.concat " " *)
        (*+> print_endline;*)
        res
      end
    with Not_found ->
      let res = cont_match_traces g sp n
      in begin
        (*print_string "Cache miss : ";*)
        (*sp +> List.map string_of_gtree' +> String.concat " " *)
        (*+> print_endline;*)
        Hashtbl.replace matching_ht (g,sp,n) res;
        res
      end
  in begin
      traces_ref := [];
      result
    end

let check_matches g sp n =
  try 
    let res = Hashtbl.find matching_ht (g,sp,n)
    in
      begin
        Some res
      end
  with Not_found -> begin
    (*print_string "Cache miss : ";*)
    (*sp +> List.map string_of_gtree' +> String.concat " "*)
    (*+> print_endline;*)
    let res = cont_match_traces g sp n
    in
    if res
    then begin
      Hashtbl.replace matching_ht (g,sp,n) res;
      Some true
    end
    else
      None
  end

let get_traces_old g sp n =
    (* check whether we know whether sp matches g at all *)
    match check_matches g sp n with
    | Some true -> begin
      traces_ref := [];
      Hashtbl.clear envs_ref;
      if cont_match_traces g sp n
      then (
        let v = !traces_ref in (
        traces_ref := []; 
        Hashtbl.clear envs_ref;
        Some v)
      )
      else 
        None
      end
    | _ -> None 

let uncurry f = fun (x,y) -> f x y

let get_traces g sp n =
  match cont_match_traces_new g sp n with
  | Some tr -> Some (List.rev_map fst tr)
  | None -> None

let get_merged_env g sp n =
  match cont_match_traces_new g sp n with
  | Some tr -> 
      let ht = Hashtbl.create 117 in
      begin
        List.iter (fun (_, env) -> 
          List.iter (Hashtbl.add ht +> uncurry) env
        ) tr;
        Some ht
      end
  | None -> None


let get_merged_env_old g sp n =
  match check_matches g sp n with
  | Some true -> begin
    traces_ref := [];
    Hashtbl.clear envs_ref;
    let matcher vp x = 
      begin
        List.iter (function (x,v) -> 
          Hashtbl.add envs_ref x v     
        ) vp.env_t;
        true
      end 
    in
      if cont_match_param matcher g sp n
      then (
        let v = Hashtbl.copy envs_ref in 
        traces_ref := []; 
        Hashtbl.clear envs_ref;
        Some v)
      else 
        None
    end
  | _ -> None

let get_env_traces = cont_match_traces_new

let get_env_traces_old g sp n =
  match check_matches g sp n with
  | Some true -> begin
    let seq_env_lists = ref [] 
    in
      begin
        traces_ref := [];
        let matcher vp x = 
          begin
            seq_env_lists := (List.rev vp.trace, vp.env_t) :: !seq_env_lists;
            true
          end 
        in
          if cont_match_param matcher g sp n
          then 
            begin
              traces_ref := []; 
              Some !seq_env_lists
            end
          else 
            None
      end
    end
  | _ -> None
  



(* let get_last_locs g cp n = *)
(*   let loc_list = ref [] in *)
(*   let init_vp = {skip = []; env = []; last = None;} in  *)
(*   let matched_vp vp n env =  *)
(*     (\* let f, env' = try true, env %% vp.env with Bind_error -> false, [] in *\) *)
(*     (\* in this semantic, we never allow visiting the same node twice *\) *)
(*     let f, env' = try not(List.mem n vp.skip), env %% vp.env with Match_failure _ -> false, [] in *)
(*       f, {last = Some (get_val n g); skip = n :: vp.skip; env = env'} in *)
(*   let skipped_vp vp n = { *)
(*     last = vp.last; *)
(*     skip = n :: vp.skip;  *)
(*     env = vp.env} in *)
(*   let check_vp vp n  = not(List.mem n vp.skip) &&  *)
(*     not(Some (get_val n g) = vp.last) *)
(*   in *)
(*   let rec trans_cp cp c = match cp with *)
(*     | [] -> c *)
(*     | bp :: cp -> trans_bp bp (trans_cp cp c) *)
(*   and trans_bp bp c vp n = match view bp with *)
(*     | C("CM", [gt]) -> *)
(*   (try  *)
(*             let env = match_term gt (get_val n g) in *)
(*             let f,vp' = matched_vp vp n env in *)
(*               f && List.for_all (function (n',_) -> c vp' n') (get_succ n g) *)
(*     with Nomatch -> false) *)
(*     | _ when bp == ddd -> *)
(*   c vp n || ( *)
(*           check_vp vp n && *)
(*             let ns = get_next_vp'' g vp n in *)
(*               not(ns = []) && *)
(*     let vp' = skipped_vp vp n in *)
(*       List.for_all (trans_bp ddd c vp') ns *)
(*   ) *)
(*   in *)
(*   let matcher = trans_cp cp (fun vp x ->  *)
(*     loc_list := valOf vp.last :: !loc_list; *)
(*     true) in *)
(*     if matcher init_vp n *)
(*     then Some (List.fold_left (fun acc_l e ->  *)
(*       if List.mem e acc_l *)
(*       then acc_l *)
(*       else e :: acc_l *)
(*     ) [] !loc_list) *)
(*     else None *)

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


let rec free_vars t =
  let no_dub_app l1 l2 = List.rev_append 
    (List.filter (fun x -> not(List.mem x l2)) l1)
    l2 
  in
    match view t with
      | A ("meta", mvar) -> [mvar]
      | C (_, ts) -> List.fold_left
    (fun fvs_acc t -> no_dub_app (free_vars t) fvs_acc)
      [] ts
      | _ -> []

let rec count_vars t =
  match view t with
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



let get_metas build_mode org_env t = 
  let rec loop env =
    match env with
      | [] when build_mode -> (
          debug_msg ("bind: " ^ string_of_gtree str_of_ctype str_of_catom t);
          debug_msg (">>>>>>>>>>> with size: " ^ string_of_int (gsize t));
          new_meta org_env t)
      | [] -> [], []
      | (m, t') :: env when t = t' ->
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
  match lists with(*{{{*)
    | [] -> (debug_msg "."; [[]])
    | lis :: lists -> (debug_msg ","; prefix_all lis (gen_perms lists))(*}}}*)



let renumber_metas t metas =
  match view t with
    | A ("meta", mvar) -> 
        (try 
          let v = List.assoc mvar metas in
          mkA ("meta", v), metas
         with _ -> 
          let nm = mkM_name() in
          mkA ("meta", nm), (mvar, nm) :: metas
        )
    | _ -> t, metas

let renumber_metas_pure t (metas, next_meta) =
  match view t with
    | A ("meta", x) -> 
        (try
          let v = List.assoc x metas 
          in mkA("meta", v), (metas, next_meta)
        with Not_found ->
          let nm = "X" ^ string_of_int next_meta 
          in mkA ("meta", nm), ((x,nm) :: metas, next_meta + 1)
        )
    | _ -> t, (metas, next_meta)

let renumber_metas_gtree gt_pattern =
  fst(
    fold_botup gt_pattern renumber_metas_pure ([],0)
  )

let renumber_metas_up up =
  reset_meta ();
  match up with
    | UP(lhs, rhs) -> 
        let lhs_re, lhs_env = fold_botup lhs renumber_metas [] in
        let rhs_re, rhs_env = fold_botup rhs renumber_metas lhs_env in
        (* assert(lhs_env = rhs_env);*)
        UP(lhs_re, rhs_re)
    | ID s -> let nm, new_env = renumber_metas s [] in ID nm
    | RM s -> let nm, new_env = renumber_metas s [] in RM nm
    | ADD s -> let nm, new_env = renumber_metas s [] in ADD nm
    | _ -> failwith "unhandled update type in 'renumber_metas_up'"

let rec abs_term_imp terms_changed is_fixed up =
  let cur_depth = ref !abs_depth in
  let should_abs t = 
     !cur_depth >= 0 
  in
  let rec loop build_mode env t = 
    match view t with
    | _ when !cur_depth <= 0 -> get_metas build_mode env t
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
          print_endline ("[Diff] not abstracting atom: " ^ string_of_gtree' t);
          [t], env)
    | C (ct, []) -> 
  (* this case has been reached we could have an empty file;
   * this can happen, you know! we return simply an atom
   *)
  [mkA(ct, "new file")], env
    | C("prg", _)
    | C("prg2", _)
    | C("def",_) 
    | C("comp{}", _) 
    | C("if", _) 
    | C("while", _)
    | C("dowhile", _)
    | C("for", _) 
    | C("switch", _) 
    | C("storage", _) -> [t], env
    (* | C (ct, ts) when !abs_subterms <= zsize t ->  *)
    (*   (fdebug_endline !Jconfig.print_abs ("[Diff] abs_subterms " ^ string_of_gtree' t); *)
    (*    [t], env) *)
    | C("call", f :: ts) ->
  cur_depth := !cur_depth - 1;
        (* generate abstract versions for each t ∈ ts *)
        let meta_lists, env_acc =
          List.fold_left (fun (acc_lists, env') t -> 
          let meta', env'' = loop build_mode env' t
          in (meta' :: acc_lists), env''
                         ) ([], env) ts in
          (* generate all permutations of the list of lists *)
        let meta_perm = gen_perms (List.rev meta_lists) in
          (* construct new term from lists *)
    cur_depth := !cur_depth + 1;
          t :: List.rev (List.fold_left (fun acc_meta meta_list ->
             mkC("call", f :: meta_list) :: acc_meta
                                        ) [] meta_perm), env_acc
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
              mkC(ct, args) :: acc_t) [] perms) 
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
      assert(not(abs_lhss = []));
      (* now we check that the only solution is not "X0" so that we will end
             * up transforming everything into whatever rhs
             *)
      let abs_lhss = (match abs_lhss with
        | [{node=A ("meta", _)}] -> 
      (debug_msg 
          ("contextless lhs: " ^ string_of_diff up); [lhs]
      )
        | _ -> abs_lhss)
        (* now use the environment to abstract the rhs term
        *) in
      let abs_rhss, rhs_env = loop false lhs_env rhs in
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
  fdebug_endline !Jconfig.print_abs ("[Diff] abstracting concrete update with size: " ^
        string_of_int (Difftype.fsize up) ^ "\n" ^
        string_of_diff up);
  (*let res, _ = abs_term_size terms_changed is_fixed should_abs up in *)
  let res, _ = abs_term_imp terms_changed is_fixed up in 
  let res_norm = List.map renumber_metas_up res in
    fdebug_endline !Jconfig.print_abs ("[Diff] resulting abstract updates: " ^ 
          string_of_int (List.length res));
    if !Jconfig.print_abs 
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

(* depth based abstraction pred: only abstract "shallow" terms -- i.e. terms
 * with depth less than threshold
 *)
let should_abs_depth t = gdepth t <= !abs_depth


let non_dub_cons x xs = if List.mem x xs then xs else x :: xs 
let (%%) a b = non_dub_cons a b
let non_dub_app ls1 ls2 = List.fold_left (fun acc l -> l %% acc) ls1 ls2
let (%) ls1 ls2 = non_dub_app ls1 ls2

(* construct all the possible sub-terms of a given term in the gtree format; the
 * resulting list does not have any order that one should rely on
 *)
let make_all_subterms t =
  let rec loop ts t =
    match view t with
      | C(_, ts_sub) -> List.fold_left loop (t %% ts) ts_sub
      | _ -> t %% ts in
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

let print_additions d =
  match d with
    | ADD d -> print_endline ("\n+ " ^ string_of_gtree' d)
    | RM d -> print_endline ("\n- " ^ string_of_gtree' d)
    | UP(s,t) -> 
  (print_endline (string_of_diff d);
   print_newline ())
    | ID d -> () (* print_endline ("\n= " ^ string_of_gtree' d)*)
    | _ -> ()

(*let apply_list gt1 ds = *)
(*let app_nonexec s d = try apply_noenv d s with omatch -> s in*)
(*List.fold_left app_nonexec s ds*)

let unabstracted_sol gt1 gt2 = 
  get_ctf_diffs_safe [] gt1 gt2

let make_subterms_update up =
  match up with
    | UP(lhs, rhs) -> (make_all_subterms lhs) % (make_all_subterms rhs)
    | RM t | ADD t | ID t -> make_all_subterms t
    | _ -> failwith "unhandled update type in 'make_subterms_update'"

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
    then e %% acc
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
  (* print_endline ("[Diff] no_occurs: " ^ string_of_int !no_occurs);  *)
  List.fold_left (fun acc l -> List.fold_left (fun acc e ->
    if inSome e ell
    then e %% acc
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
      fdebug_string !Jconfig.print_abs ("[Diff] making all subterms for :\n\t");
      fdebug_endline !Jconfig.print_abs (string_of_gtree' gtn);
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




(* depth first search *)
let dfs_iter xi' f g =
  let already = Hashtbl.create 101 in
  let rec aux_dfs xs = 
    xs +> List.iter (fun xi -> 
           if Hashtbl.mem already xi then ()
           else begin
       Hashtbl.add already xi true;
       if not(xi = xi')
       then f xi;
       let succ = g#successors xi in
         aux_dfs (succ#tolist +> List.map fst);
           end
        ) in
    aux_dfs [xi']

let seq_of_flow f = 
  let seq = ref [] in
  let start_idx = 0 in
  let add_node i = seq := f#nodes#find i :: !seq in
    dfs_iter start_idx add_node f;
    !seq 
    +> List.filter non_phony
    +> List.filter (fun x -> not (is_head_node x))
    +> List.rev


let dfs_diff f1 f2 = 
  let seq1 = seq_of_flow f1 in
  let seq2 = seq_of_flow f2 in
    patience_diff seq1 seq2
    +> normalize_diff


let tl = List.tl
let hd = List.hd

let rec get_marked_seq ss = match ss with
  | ID t :: ADD t' :: ss' | ADD t' :: ID t :: ss' -> ID t +++ get_marked_seq (tl ss)
  | RM t :: ss -> RM t +++ get_marked_seq ss
  | _ :: ss -> get_marked_seq ss
  | [] -> []

let print_diff_flow di =
        di
        +> List.iter (function m -> 
                match m with
                | ID t -> print_endline ("\t" ^ string_of_gtree' t)
                | ADD t -> print_endline ("+\t" ^ string_of_gtree' t)
                | RM t -> print_endline ("-\t" ^ string_of_gtree' t)
                | _ -> failwith "unhandled update type in 'print_diff_flow'"
                )

let flow_changes = ref []

let get_flow_changes flows1 flows2 =
  flows1 
  +> List.iter 
    (function f ->
       let fname = get_fun_name_gflow f in
   flows2 
   +> List.find_all (function f' -> get_fun_name_gflow f' = fname)
   +> List.iter (function f' -> 
       let diff = dfs_diff f f' in
         flow_changes := diff :: !flow_changes;
         if !verbose then print_diff_flow diff
          )
    )



(* this function takes a list of patches (diff list list) and looks for the
 * smallest size of any update; the size of an update is determined by the gsize
 * of the left-hand-side 
 *)
let gsize_diff d =
  match d with
    | ID l | RM l | ADD l | UP (l,_) -> Some (gsize l)
    | _ -> failwith "unhandled update type in 'gsize_diff'"
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
  List.filter (function bp -> 
     safe_part bp (gt1, gt2)
    (* if safe_part bp (gt1, gt2) *)
    (* then true *)
    (* else ( *)
    (*   print_string "[Diff] unsafe part:\n\t"; *)
    (*   print_endline (string_of_diff bp); *)
    (*   false *)
    (* ) *)
  ) parts

    
let rec abs_term_one env t t' =
  (* 
     env : string * term list -- maps metaname from first term to metavariables in new term
     t   : term
     t'  : term   -- terms from which to produce abstraction
  *)
  if t = t' 
  then t, env 
  else match view t, view t' with
    | C(ty1, ts1), C(ty2, ts2) when 
   ty1 = ty2 && List.length ts1 = List.length ts2 -> 
   let ts', env' = List.fold_left2 
     (fun (acc_ts, env) t1 t2 -> 
         let t1', env' = abs_term_one env t1 t2 in
         (t1' :: acc_ts, env')
      ) ([], env) ts1 ts2 in
    mkC(ty1, List.rev ts'), env'
    | _, _ -> try mkA("meta", rev_assoc t env), env with Not_found -> 
  let new_m = mkM () in
  let m_name = meta_name new_m in
    (* a limitation here is that we assume equal subterms to
       always be abstracted by equal metavariables
    *)
    new_m,  (m_name, t) :: env


let abs_term_list env t ts =
  let res = ts
    +> List.rev_map (function t' ->  reset_meta (); abs_term_one env t t') 
    +> List.filter (function p, env -> not(is_meta p))
    +> rm_dub in
    (* print_string ("abs_term_list " ^ string_of_gtree' t); *)
    (* print_endline (" on ts.length = " ^ ts +> List.length +> string_of_int); *)
    (* res +> List.iter (function (t,_) -> t +> string_of_gtree' +> print_endline); *)
    res


let abs_term_lists env t ts_lists =
  ts_lists
  +> List.rev_map (abs_term_list env t)

(* this function partitions elems in eq_classes according to the in_eq
   function given;
   basic assumption: **every element belongs to exactly ONE eq_class**
*)
let partition in_eq elems =
  let rec add eq_classes e = match eq_classes with
    | [] -> [[e]]
    | eq_cls :: eq_classes when in_eq e eq_cls -> (e :: eq_cls) :: eq_classes
    | eq_cls :: eq_classes -> eq_cls :: add eq_classes e
  in
  let n = List.length elems in
  let i = ref 0 in
    elems +> List.fold_left (fun acc elem -> begin
             ANSITerminal.save_cursor ();
             ANSITerminal.print_string 
         [ANSITerminal.on_default](
           !i +> string_of_int ^"/"^
             n +> string_of_int);
             ANSITerminal.restore_cursor();
             flush stdout;
             i := !i + 1;
             add acc elem
           end) []
  

let int_of_meta m = 
  let istring = String.sub m 1 (String.length m - 1) in
  int_of_string istring

(* return a new metavariable not in use in env *)  
let fresh_meta env = 
  let rec get_max max_x env = match env with
    | [] -> max_x
    | (m,_) :: env when int_of_meta m > max_x -> get_max (int_of_meta m) env
    | _ :: env -> get_max max_x env
  in
    "X" ^ string_of_int (get_max 0 env + 1)

let new_meta_term env = mkA("meta", fresh_meta env)
  
(* extend env_given with bindings from env_init such that
   ∀m->t,m'->t'∈env_res : m=m' iff t=t'
*)
let extend_env env_given env_init =
  let add_bind (acc_env, new_meta_env) (m,t) =
    if acc_env +> List.exists 
      (function (m',t') -> m=m' && not(t=t'))
    then 
      let nmeta= fresh_meta acc_env in
  ((nmeta, t) :: acc_env, (nmeta, mkA("meta", m)) :: new_meta_env)
    else 
      try 
  let (m', t') = acc_env +> List.find (function (m',t') -> not(m=m') && t=t') in
    (acc_env, (m', mkA("meta", m)) :: new_meta_env)
      with Not_found -> 
  ((m,t) +++ acc_env, new_meta_env)
  in
    env_init +> List.fold_left add_bind (env_given, [])


let pat_e_ht = TT.create 591

(* memoize the extension of a node-pattern *)
let node_pat_extension unique_subterms p =
  try
    TT.find pat_e_ht p
  with Not_found ->
    let res = unique_subterms +> List.filter (function t -> can_match p t)
    in 
      begin
        TT.replace pat_e_ht p res;
        res
      end

let node_pat_eq unique_subterms (p,env) (p',env') = 
  let p_ext = node_pat_extension unique_subterms p in
  let p_ext'= node_pat_extension unique_subterms p' in
    eq_lists p_ext p_ext'

let gsize_spattern sp = 
  sp +> List.fold_left (fun acc_s gt -> Gtree.zsize gt + acc_s) 0

let get_patterns subterms_lists unique_subterms env term =
  let pat_extension p = node_pat_extension unique_subterms p in
  let pat_eq pe pe' = node_pat_eq unique_subterms pe pe' in
  let in_eq p_env eq_cls = pat_eq p_env (List.hd eq_cls) in
  let pat_cmp (p1,env1) (p2,env2) = Gtree.zsize p2 - Gtree.zsize p1 in
  let sort_eq_cls eq_cls =
    List.sort pat_cmp eq_cls in
  let add_abs (p, env) =
    (* print_endline "[Diff] adding pattern:"; *)
    (* t +> string_of_gtree' +> print_endline;  *)
    try 
      let cnt = TT.find count_ht p in
  TT.replace count_ht p (cnt + 1)
    with Not_found ->
      TT.replace count_ht p 1 in
  let rec count term =
    abs_term_lists env term subterms_lists
    +> List.iter 
      (function abs_list ->
   abs_list 
   +> List.iter add_abs
      )
  in
    begin
      if !not_counted
      then begin
  print_string "[Diff] initial term abstraction...";
  let n = ref 0 in
  let m = List.length unique_subterms in
  let mod_m = if m / 100 = 0 then 1 else m / 100 in
    unique_subterms +> List.iter (function uniq_t -> begin
            if !n mod mod_m = 0
            then begin
              ANSITerminal.save_cursor ();
              ANSITerminal.print_string 
                [ANSITerminal.on_default](
            !n +> string_of_int ^"/"^
              m +> string_of_int);
              ANSITerminal.restore_cursor();
              flush stdout;
            end;
            n := !n + 1;
            count uniq_t
          end);
    print_newline ();
    print_endline ("[Diff] number of patterns: " ^ TT.length count_ht +> string_of_int);
    print_string "[Diff] pre-pruning...";
    flush stdout;
    TT.fold (fun pattern occurs acc -> 
         let real_occurs = subterms_lists +> List.fold_left 
           (fun acc_n fs -> 
        if fs +> List.exists (can_match pattern)
        then acc_n + 1
        else acc_n
           ) 0 in
         if real_occurs >= !no_occurs
         then 
           if acc +> List.exists
       (function (p,_) -> 
          pat_extension p 
          = pat_extension pattern
          && Gtree.zsize p > Gtree.zsize pattern)
           then 
       acc
           else
       (pattern, real_occurs) :: acc
         else (
           
           acc
         )
      ) count_ht []
    +> (function x -> print_string " partitioning";x)
    +> partition in_eq
    +> (function x -> print_endline " sorting";x)
    +> List.rev_map sort_eq_cls
    +> List.rev_map List.hd
    +> (function x -> print_endline " reconstructing table"; x)
    +> List.iter (function (p,n) -> 
        TT.replace prepruned_ht p n
           );
    print_endline ("done with " ^ TT.length count_ht - TT.length prepruned_ht 
       +> string_of_int  ^ " elements pruned");
    not_counted := false;
    if !Jconfig.print_abs
    then begin
      print_endline "[Diff] initial (after pre-pruning) abstracted patterns";
      print_endline ("[Diff] threshold: " ^ string_of_int !no_occurs);
      prepruned_ht +> TT.iter (fun p n -> 
           if n >= !no_occurs
           then
             print_endline (string_of_gtree' p ^
                  " : " ^ n +> string_of_int);
        )
    end
      end;
      let res = 
  TT.fold 
    (fun pattern occurs acc ->
       if occurs >= !no_occurs
       then
         try
     let env_p = match_term pattern term in
       if env = []
       then (pattern, env_p) :: acc
         else
           let env_new, new_meta_env = extend_env env env_p in
           let p_new = rev_sub new_meta_env pattern in
       (p_new, env_new) :: acc;
         with Nomatch ->
     acc
       else (
         acc)
    (* ) prepruned_ht [] *)
    ) prepruned_ht []
      in
  res
    (*
      begin
      partition in_eq res
      +> List.rev_map sort_eq_cls
      +> List.rev_map List.hd
      end
    *)
    end


let rec useless_abstraction p = is_meta p || 
  match view p with
    | C("dlist", inis) ->
        List.for_all useless_abstraction inis
    | C("stmt", [p']) 
    | C("exprstmt", [p']) 
    | C("exp", [p']) 
    | C("fulltype", [p']) 
        when useless_abstraction p' -> true
    | C("onedecl",[p_var;p_type;p_storage]) ->[p_var; p_type] +> List.for_all useless_abstraction 
    | A("stobis", _) | A("inline",_) -> true
    | C("storage", [p1;p2]) | C("itype", [p1;p2]) when is_meta p1 || is_meta p2 -> true
(*    | C("fulltype", _) (* | C("pointer", _) *) -> true *)
    | C("exp", [{Hashcons.node=A("ident", _)}]) -> true
    | C("exp", [{Hashcons.node=C("const", _)}]) -> true
    | _ -> false

let rec is_nested_meta gt = is_meta gt || match view gt with
  | C(_,es) -> List.for_all is_meta es (* is_nested_meta e *)
  | _ -> false

let rec contains_infeasible p = 
  match view p with
    | C("binary_arith", op :: _) 
    | C("binary_logi",  op :: _) when is_nested_meta op -> true
    | C("call", gt_fname :: _) -> is_nested_meta gt_fname 
    | C("return", _) -> false
    | C(_, ts) -> List.exists contains_infeasible ts
    | _ -> false

(* The following function is used to decide when an abstraction is infeasible.
 * Either because it simply a meta-variable X or if it is too abstract
 *)
let infeasible p = 
  if !Jconfig.useless_abs
  then false
  else useless_abstraction p || contains_infeasible p || is_nested_meta p

(* abstract term respecting bindings given in env;
   return all found abstractions of the term and the correspond env
*)

let abstract_term subterms_lists unique_terms env t =
  if !Jconfig.print_abs 
  then print_endline ("[Diff] abstract_term: " ^
       string_of_gtree' t);
    get_patterns subterms_lists unique_terms env t 
    +> List.fold_left 
    (fun acc_ps_envs (p, env_p) -> 
       (* p is an abstraction of t and
    env_p gives bindings from metavars to the
    subterms in t;
    extend env with env_p into env' such that:
    m->t ∈ env_p & m'->t ∈ env =>
    m'->t ∈ env'

    furthermore the pattern p to return uses metavariables from
    env_p, but it should use those from env'; thus, traverse p
    and for each subterm use rev_lookup to use a different metavar

       *)
       let p' = p (* rev_sub env_p t *) in
   if infeasible p'
   then begin
     if !Jconfig.print_abs then 
       print_endline ("[Diff] infeasible: " ^ p' +> string_of_gtree');
     acc_ps_envs
   end
   else begin
     if !Jconfig.print_abs
     then print_endline ("[Diff] node pattern: " ^ p' +> string_of_gtree');
     if List.exists (function p'',_ -> p' = p'') acc_ps_envs
     then acc_ps_envs
     else
       (* (p', env_p) :: acc_ps_envs *)
       (p, env_p) :: acc_ps_envs
   end
     
    ) []



let rm_dups_pred eq_f ls = 
  let (+++) x xs = if List.exists (function y -> eq_f x y) xs then xs else x :: xs in
    List.fold_left (fun acc_xs x -> x +++ acc_xs) [] ls


let abstract_all_terms subterms_lists unique_terms env =
  let res = unique_terms 
    +> List.rev_map (abstract_term subterms_lists unique_terms env)
    +> tail_flatten
    +> rm_dups_pred (fun (p1,_) (p2,_) -> p1 = p2)
  in
    res
    

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



(* The merge_patterns function tries to merge two patterns into one which match
 * both of the patterns, but which abstracts only those subterms which NEED to
 * be abstracted
 *)
let rec merge_patterns p1 p2 =
  let rec loop p1 p2 =
    match view p1, view p2 with
      | _, _ when p1 == p2 -> p1
      | _, A("meta", v2) -> p2
      | A("meta",_), _ -> p1
      | C(t1,ts1), C(t2,ts2) when 
            t1 = t2 && List.length ts1 = List.length ts2 -> 
          mkC (t1, List.fold_left2 (fun acc_ts t1 t2 ->
            loop t1 t2 :: acc_ts
          ) [] ts1 ts2)
      | _, _ -> let m = "X" ^ string_of_int (ref_meta()) in
      make_gmeta m
  in
    match view p1, view p2 with
      | _, _ when p1 == p2 -> Some p1
      | C(t1,ts1), C(t2,ts2) when
            t1 = t2 && List.length ts1 = List.length ts2 -> 
          Some (loop p1 p2)
      | _, _ -> None


(* based on the assumption that in a diff, we always group
 * removals/additions the following function splits a diff into chunks
 * each being of the form:
 * 
 * chunk ::= (+p)* (-p | p) (+p)*
 * 
 * that is: each chunk contains a context node (the -p,p) and some
 * additions.
 * 
 * BFW: One should take note that given a diff, there can be more than one way
 * to split a 'diff' according to the chunk-def given. 
 *)

let all_adds diff = List.for_all (function ADD _ -> true | _ -> false) diff

let chunks_of_diff_generic sel diff =
  let rec loop acc_chunks chunk diff = match diff with
    | [] -> List.rev ((List.rev chunk) :: acc_chunks)
    | i :: diff' -> (match i with
           | ADD t -> loop acc_chunks (i :: chunk) diff'
           | ID tt when (sel tt) == skip -> 
               loop ((List.rev chunk) :: acc_chunks) [] diff'
           | ID t | RM t -> _loop acc_chunks (i :: chunk) diff'
           | _ -> failwith "unhandled update type in 'chunks_of_diff_generic'"
        ) 
  and _loop acc_chunks chunk diff = match diff with
    | [] -> loop acc_chunks chunk []
    | i :: diff' -> (match i with
           | ADD _ -> _loop acc_chunks (i :: chunk) diff'
           | ID tt when (sel tt) == skip -> 
               loop ((List.rev chunk) :: acc_chunks) [] diff'
           | _ -> loop ((List.rev chunk) :: acc_chunks) [] diff
        ) in
    loop [] [] diff

let chunks_of_diff diff = chunks_of_diff_generic (fun (a,b) -> a) diff

(* given a set of patterns and a term that have been identified as
 * belonging to a change, we wish to find the patterns that match the
 * term
 *)
let get_change_matches spatterns term =
  v_print_endline "[Diff] getting patterns that relate to: ";
  v_print_endline (string_of_gtree' term);
  spatterns +> List.filter 
    (function spat ->
       (* recall that spat is a list of term-patterns *)
       spat 
       +> List.filter (function p -> match view p with 
       | C("CM",[p]) -> true 
       | _ -> false) 
       +> List.exists (function p -> can_match (extract_pat p) term)
    ) 

let is_id_chunk ch = match ch with
    | [ID _] | [ADD _] | [] -> true
    | _ -> false

let chunks_of_diff_spatterns spatterns diff =
  let print_chunk chunk =
    if !Jconfig.verbose
    then List.iter (function 
          | ID t -> print_endline ("  " ^ string_of_gtree' t)
          | RM t -> print_endline ("- " ^ string_of_gtree' t)
          | ADD t-> print_endline ("+ " ^ string_of_gtree' t)
          | _ -> failwith "unhandled update type in 'chunks_of_diff_spatterns'"
       ) (List.rev chunk) ;
  in
  let add_chunk chunk acc_chunks = 
    if List.mem chunk acc_chunks
    then acc_chunks
    else chunk :: acc_chunks
  in
    let rec loop acc_chunks chunk diff = 
      match diff with
      | [] -> v_print_endline ("[Diff] found " ^ string_of_int (List.length acc_chunks + 1) ^ " chunks so far");
              if is_id_chunk chunk
              then acc_chunks
              else begin
                print_chunk (List.rev chunk);
                add_chunk (List.rev chunk) acc_chunks
              end
      | i :: diff' -> (match i with
                      | ADD t -> loop acc_chunks (i :: chunk) diff'
                      | ID t ->
                           if get_change_matches spatterns t = []
                           then loop acc_chunks [] diff'
                           else let new_acc_chunks = _loop acc_chunks (i :: chunk) diff'
                                in loop new_acc_chunks [] diff'
                      | RM t -> 
                           if get_change_matches spatterns t = []
                           then loop acc_chunks chunk diff'
                           else let new_acc_chunks = _loop acc_chunks (i :: chunk) diff'
                                in loop new_acc_chunks [] diff'
                      | _ -> failwith "unhandled update type in 'chunks_of_diff_spatterns.loop'"
                      ) 
    and _loop acc_chunks chunk diff = match diff with
      | [] -> loop acc_chunks chunk []
      | i :: diff' -> (match i with
                      | ADD _ -> _loop acc_chunks (i :: chunk) diff'
                      | _ -> 
                          begin
                            v_print_endline "[Diff] adding chunk : ";
                            print_chunk (List.rev chunk);
                            add_chunk (List.rev chunk) acc_chunks
                          end 
                      ) 
    in
      loop [] [] diff
      +> List.filter (function chunk -> not(chunk = []))
      +> List.filter (fun c -> not(all_adds c))


(***
 * Given lists of subterms [subterms_lists] and a list of unique subterms
 * [unique_subters] this function produces a list of patterns (terms with
 * metavariable) such that for each pattern pat:
 *   length 
 *   [subterm_list | subterm_list ∈ subterms_lists,
 *                   ∃t∈subterm_list:p≼t] 
 *   >= threshold
 *)
let merge_abstract_terms subterms_lists unique_subterms =
  (* There should be no duplicate subterms in each subterms_list *)
  let non_dub_subterms_lists = List.rev_map rm_dub subterms_lists in
  let abs_count = ref 0 in
  let abs_total = ref 0 in
  (* Function to compute extension of node-pattern; uses Hashtable for
   * memoization *)
  let pat_extension p = 
    node_pat_extension unique_subterms p in

  (* Predicate to determine whether we will return a node-pattern. Takes the
   * current node-pattern plus the accumulated node-patterns. *)
  let interesting_post t acc_ts = 
    (* filter out obvious bad ones; e.g. too abstract ... *)
    not(infeasible t) && non_phony t && not(control_true = t) && not(is_head_node t) 
    (* also: *)
    && List.for_all (function t' -> t = t' || (
        let tsub = subset_list (pat_extension t) (pat_extension t') in
        let tsup = subset_list (pat_extension t') (pat_extension t) in
        if tsub 
        then (* ⟦t⟧ = ⟦t'⟧ or ⟦t⟧ ⊂ ⟦t'⟧ *)
          if tsup
          then (* t eq t' => only if t has larger concrete,meta size then include it *) 
            leq_pair_size t' t
          else (* t < t' : i.e. pattern matches strictly fewer terms, so it
          might be interesting *) 
            true
        else
          (* t' > t or t is unrelated to t'; we only want to include t if it
           * is unrelated to t' *)
          !Jconfig.include_larger || not(tsup)
        )) acc_ts
  in
  (* simple filter used under construction of potential set of node-patterns *)
  let interesting_t t acc_ts = 
    begin
      not(infeasible t)
      && non_phony t
      && not(control_true = t)
      && not(is_head_node t)
      && not(acc_ts +> List.exists (function t' -> t = t')) 
    end
  in
  let f ts_list acc_ts =
      match acc_ts with
      | None -> ts_list +> some
      | Some ts -> 
          begin
            ts +> List.fold_left 
              (fun acc_ts t_merged -> 
                    ts_list +> List.fold_left 
                      (fun acc_ts t ->
                        let t', env = Gtree_util.merge_terms t t_merged in
                        let p = renumber_metas_gtree t' in
                        if interesting_t p acc_ts
                        then p +++ acc_ts
                        else acc_ts
                      ) acc_ts
              ) (List.rev_append ts ts_list)
            +> some
          end
  in
  let concat ls1 ls2 = match ls1, ls2 with
    | None, _ -> ls2
    | _, None -> ls1
    | Some ps, _ -> f ps ls2
  in
    (pfold f non_dub_subterms_lists None concat)
    +> get_some
    +> (function x -> 
          begin
            print_string ("[Diff] found " ^ x +> List.length +> string_of_int ^ " patterns; fixing occurrences... ");
            abs_total := List.length x;
            x
          end
       )
    +> List.filter (
        function p ->
          ANSITerminal.save_cursor ();
          ANSITerminal.print_string [ANSITerminal.on_default] 
            (!abs_count +> string_of_int ^"/"^ !abs_total +> string_of_int);
          ANSITerminal.restore_cursor();
          flush stdout;
          abs_count := !abs_count + 1;
          let real_occurs = 
            non_dub_subterms_lists
            +> List.fold_left 
                (fun acc_n ts ->
                  if ts +> List.exists (can_match p)
                  then acc_n + 1
                  else acc_n
                ) 0 
          in
            real_occurs >= !no_occurs
       )
    +> function ps ->
      print_newline ();
      print_endline ("[Diff] computing interesting patterns from " 
                      ^ ps +> List.length +> string_of_int ^ " patterns");
      List.iter (function p -> print_endline (string_of_gtree' p)) ps;
      let ps = ps
        +> List.filter (function t -> not(infeasible t) && non_phony t && not(control_true = t) && not(is_head_node t))
        +> function ps' ->
              ps' +> List.fold_left 
                (fun acc t -> if interesting_post t ps'
                              then 
                                t +++ acc
                              else acc
                ) [] 
      in
        print_endline "... done";
        if !Jconfig.print_abs
        then 
          begin
            ps +> List.iter 
              (function p -> p +> string_of_gtree' +> print_endline);
            ps
          end
        else ps  



let rename_env_using env1 env2 =
  env1 +> List.fold_left 
    (fun acc_env_rename (x,pair1) ->
       try let (y,pair2) = List.find (function (y,pair2) ->
          pair1 = pair2
             ) env2 in
   (x, mkA("meta", y)) :: acc_env_rename
       with Not_found -> 
   let newMeta = "Y" ^ ref_meta () +> string_of_int in
     (x, mkA("meta", newMeta)) :: acc_env_rename
    ) 
    []



let merge_tus up1 up2 =
  match up1, up2 with
  | (UP (l1,r1)), (UP (l2,r2)) ->
            let l_pat, l_env = merge_terms l1 l2 in
            let r_pat, r_env = merge_terms r1 r2 in
            let rp_env = rename_env_using r_env l_env in
               UP (l_pat, sub rp_env r_pat) +> renumber_metas_up 
  | _ -> failwith "unhandled update types in 'merge_tus'"


let get_metas t =
  let rec loop acc_ms t = match view t with
    | A ("meta", _) -> t +++ acc_ms
    | C (_, ts) -> List.fold_left loop acc_ms ts
    | _ -> acc_ms
  in
    loop [] t

(* This function finds the/a set of term-updates safe relative to a
given changeset *)
let find_simple_updates_merge_changeset threshold changeset =
	let rec partly_safe tu = for_some threshold (safe_part tu) changeset
	(* function to decide if a given term-update is "interesting" enough
	to include in final result *)
  and interesting_tu up = match up with
    | UP(l,r) ->
       not(l = r)
			 && not(infeasible l)
			 && sublist (get_metas r) (get_metas l)
    | _ -> failwith "unhandled update type in 'find_simple_udpdates_merge_changeset.interesting_tu'"
	and add_tu tus tu_opt =
		match tu_opt with
		| None -> tus
		| Some tu -> if interesting_tu tu
										&& not (List.exists ((=) tu) tus)
										&& partly_safe tu
								 then tu :: tus
								 else tus
	and loop acc_merged_tus cur_tu_opt rem_tu_lists =
		match rem_tu_lists with
		| [] -> add_tu acc_merged_tus cur_tu_opt
		| tu_list :: lists ->
			 let new_acc = add_tu acc_merged_tus cur_tu_opt in
			 match cur_tu_opt with
			 | Some cur_tu ->
					List.fold_left
						(fun acc tu ->
						 let merged_tu = merge_tus cur_tu tu in
						 let new_tu = if interesting_tu merged_tu
													then Some merged_tu
													else cur_tu_opt in
						 loop acc new_tu lists
						) new_acc tu_list
			 | None ->
					let tu_list_results =
						List.fold_left
							(fun acc tu ->
							 if interesting_tu tu
							 then loop acc (Some tu) lists
							 else acc
							) new_acc tu_list in
					loop tu_list_results None lists
	in
	List.rev_map (get_tree_changes >> rm_dub) changeset
	|> loop [] None
	|> rm_dub


let find_simple_updates threshold changeset =
	let rec partly_safe tu = for_some threshold (safe_part tu) changeset
	(* function to decide if a given term-update is "interesting" enough
	to include in final result *)
  and interesting_tu up = match up with
    | UP(l,r) ->
       not(l = r)
			 && not(infeasible l)
			 && sublist (get_metas r) (get_metas l)
    | _ -> failwith "unhandled update type in 'find_simple_udpdates_merge_changeset.interesting_tu'"
	and add_tu tus tu_opt =
		match tu_opt with
		| None -> tus
		| Some tu -> if interesting_tu tu
										&& not (List.exists ((=) tu) tus)
										&& partly_safe tu
								 then tu :: tus
								 else tus
	and loop acc_merged_tus cur_tu_opt rem_tu_lists =
		match rem_tu_lists with
		| [] -> add_tu acc_merged_tus cur_tu_opt
		| tu_list :: lists ->
			 let new_acc = add_tu acc_merged_tus cur_tu_opt in
			 match cur_tu_opt with
			 | Some cur_tu ->
					List.fold_left
						(fun acc tu ->
						 let merged_tu = merge_tus cur_tu tu in
						 let new_tu = if interesting_tu merged_tu
													then Some merged_tu
													else cur_tu_opt in
						 loop acc new_tu lists
						) new_acc tu_list
			 | None ->
					let tu_list_results =
						List.fold_left
							(fun acc tu ->
							 if interesting_tu tu
							 then loop acc (Some tu) lists
							 else acc
							) new_acc tu_list in
					loop tu_list_results None lists
	in
	List.rev_map (get_tree_changes >> rm_dub) changeset
	|> loop [] None
	|> rm_dub
