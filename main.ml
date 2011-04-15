(*
 * Copyright 2005-2009, Ecole des Mines de Nantes, University of Copenhagen
 * Yoann Padioleau, Julia Lawall, Rene Rydhof Hansen, Henrik Stuart, Gilles Muller, 
 * Jesper Andersen

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
open Common


let do_dmine     = ref true
let malign       = ref true
let abs          = ref false
let spec         = ref false
let mfile        = ref "specfile"
let max_level    = ref 0
let depth        = ref 0
let strict       = ref false
let mvars        = ref false
let fixed        = ref false
let exceptions   = ref 0 
let threshold    = ref 0
let print_raw    = ref false
let print_uniq   = ref false 
let print_adding = ref false
let noncompact   = ref false
let prune        = ref false
let strip_eq     = ref false
let patterns     = ref false
let spatch       = ref false
let fun_common   = ref false
let default_abstractness = ref 2.0
let only_changes = ref false
let nesting_depth = ref 1
let filter_patterns = ref false
let filter_spatches = ref false
let print_support = ref false
let cache = ref false
let max_embedded_depth = ref 2 (* this allows us to find similarities in function signatures; higher values is very expensive *)
let tmp_flag = ref false
let show_support = ref false
let flow_support = ref 0
let print_chunks = ref false

(* the 'focus_function' allows us to specify a function name which any
   found pattern should match *)
let focus_function = ref ""

let speclist =
  Arg.align
    [
     "-focus_function",Arg.Set_string focus_function, "[STRING]  name of function to focus on";
     "-specfile",      Arg.Set_string mfile,    "[filename]  name of specification file (defaults to \"specfile\") ";
     "-threshold",     Arg.Set_int threshold,   "[num]   the minimum number of occurrences required";
     "-noif0_passing", Arg.Clear Flag_parsing_c.if0_passing, 
       "  also parse if0 blocks";
     "-print_abs",     Arg.Set Jconfig.print_abs,  "  print abstract updates for each term pair";
     "-relax_safe",    Arg.Set Diff.relax,      "  consider non-application safe [experimental]";  
     "-print_inline",  Arg.Set Diff.inline_type_print, "  print types of identifiers inline";
     "-print_raw",     Arg.Set print_raw,       "  print the raw list of generated simple updates";
     "-print_uniq",    Arg.Set print_uniq,      "  print the unique solutions before removing smaller ones";
     "-print_add",     Arg.Set print_adding,    "  print statement when adding a new solution";
     "-prune",         Arg.Set prune,           "  try to prune search space by various means";
     "-strip_eq",      Arg.Set strip_eq,        "  use eq_classes for initial atomic patches";
     "-patterns",      Arg.Set patterns,        "  look for common patterns in LHS files";
     "-spatch",        Arg.Set spatch,          "  find semantic patches (not generic)";
     "-only_changes",  Arg.Set only_changes,    "  only look for patterns in changed functions";
     "-verbose",       Arg.Set Jconfig.verbose,         "  print more intermediate results";
     "-filter_patterns", Arg.Set filter_patterns, "  only produce largest patterns";
     "-no_malign",     Arg.Clear malign,          "  *DON'T* use the edit-dist subpatch relation definition"; 
     "-filter_spatches", Arg.Set filter_spatches, "  filter non-largest spatches";
     "-macro_file",    Arg.Set_string Config.std_h, "[filename]  default macros";
     "-fun_common",    Arg.Set fun_common, "  infer one abstraction of all functions given";
     "-print_support", Arg.Set print_support, "  whether to also print the concrete matched functions for fun_common";
     "-cache",         Arg.Set cache,         "  only print the term pairs to stdout";
     "-read_generic",  Arg.Set Jconfig.read_generic, "  input is given in gtree-format";
     "-max_embedding", Arg.Set_int max_embedded_depth, "  how deep to look inside terms when discovering nested patterns";
     "-tmp",           Arg.Set tmp_flag,        "  find embedded PATCHES also";
     "-show_support",  Arg.Set show_support,    "  show the support of each sem. patch inferred";
     "-flow_support",  Arg.Set_int flow_support,"  threshold required of flow-patterns";
     "-useless_abs",   Arg.Set Jconfig.useless_abs,"  also include very abstract term-patterns";
     "-print_chunks",  Arg.Set print_chunks,    "  print the chunks used to grow semantic patches"
   ]
    
exception Impossible of int

let v_print s = if !Jconfig.verbose then (print_string s; flush stdout)
let v_print_string s = v_print s
let v_print_endline s = if !Jconfig.verbose then print_endline s
let v_print_newline () = v_print_endline ""

let ddd = Diff.ddd
let cmddd = mkC("CM", [Diff.ddd])

let (+>) o f = f o

(* tail recursive version of flatten; does *not* preserve order of elements in
 * the lists 
 *)
let tail_flatten lss =
  lss +> List.fold_left List.rev_append []

let (+++) x xs = if List.mem x xs then xs else x :: xs

let for_some n f ls = 
  let rec loop n ls =
(*    n = 0 || *)
    match ls with
    | x :: xs when f x -> loop (n - 1) xs
    | _ :: xs -> loop n xs
    | [] -> n <= 0 in
  loop n ls

let file_pairs = ref []



let changeset_from_pair fixf gt1 gt2 =
  Diff.unabstracted_sol gt1 gt2
    (*if !abs *)
    (*then Diff.make_sol fixf gt1 gt2*)
    (*else Diff.unabstracted_sol gt1 gt2*)

(*let changesets = ref []*)

(* this filter takes a list of patches and cleans out the updates in each
 * patch that is unsafe/unsound/incorrect with respect to every file
 *)
let soundness_filter dpairs patches =
  let safe_for_all_up up =
    if List.for_all (fun (gt1, gt2) -> (
      (*print_endline "considering:";*)
      (*print_endline (Diff.string_of_gtree' gt1);*)
      (*print_endline (Diff.string_of_gtree' gt2);*)
      Diff.safe_update gt1 gt2 up)) dpairs
    then (
      (*print_endline ("OK:" ^ Diff.string_of_diff up); *)
      true)
    else (
      (*print_endline ("NO:" ^ Diff.string_of_diff up); *)
      false)
  in
  let filter_patch patch =
    List.filter safe_for_all_up patch
  in
  List.map filter_patch patches

let print_patch_lists pl =
  List.iter
    (function ups -> 
      print_endline "patches ****";
      List.iter
        (function up ->
          print_endline (Diff.string_of_diff up);
          print_endline "||"
        )
        ups
    )
    pl

let get_best_itemset_old ndb =
  print_endline ("[Main] getting best itemset of " ^ 
                 string_of_int (Diff.DBD.sizeOf ndb) ^ " possible");
  let supp b = Diff.DBD.get_support_itemset ndb b in
  let f acc_itemset itemset =
    if acc_itemset = [] ||
    (supp itemset >= supp acc_itemset &&
     List.length itemset >= List.length acc_itemset)
    then itemset
    else acc_itemset in
  Diff.DBD.fold_itemset ndb f []

let get_best_itemset ndb =
  let items = Diff.DBD.getItems ndb in
  print_endline ("[Main] there are " ^ string_of_int (List.length items) ^ " unique items");
  Diff.DBD.fold_unique ndb (
  fun item freq () ->
    print_endline ("[Main db] " ^ 
		   Diff.string_of_diff item ^ ", " ^
		   string_of_int freq)
 ) ();
  items

let list_at_least n f ls =
  (List.fold_left (fun acc_n e -> 
    if f e
    then acc_n + 1
    else acc_n
		  ) 0 ls) >= n


let do_datamining abs_patches =
  (*let threshold = List.length abs_patches in*)
  print_endline ("[Main] Finding unit patches with minimum support at least: " ^
                 (*string_of_int (!threshold - !exceptions));*)
                 string_of_int !threshold);
  Diff.filter_some abs_patches


let bp_of_list ls = 
  let rec loop ls = match ls with
  | [] -> None
  | l :: ls -> match loop ls with
    | None -> Some l
    | Some bp -> Some (Difftype.SEQ (l, bp))
  in
  match loop ls with
  | None -> raise (Diff.Fail "None?")
  | Some bp -> bp

let list_of_bp bp = 
  let rec loop bp = match bp with
  | Difftype.SEQ (Difftype.UP (a, b), bps) -> (Difftype.UP (a,b)) :: loop bps
  | Difftype.UP _ -> [bp]
  | _ -> raise (Diff.Fail "list_of_bp format")
  in
  loop bp

let generate_sols_old chgset_orig simple_patches =
  let lcnt = ref 1 in
  print_string "[Main] generating solutions for ";
  print_string (string_of_int (List.length simple_patches));
  print_endline " simple patches";
  let (^^) a b = List.map (function bs -> a :: bs) b in
  let make_one a = [[a]] in
  let rec loop chgset bp =
    match Diff.get_applicable chgset bp simple_patches with
    | (_, []) -> make_one bp
    | (chgset', bps) -> 
        bp ^^
        List.flatten (List.map (function bp' -> loop chgset' bp') bps)
  in
  List.flatten (List.map (function bp -> 
    print_string "[Main] generating for ";
    print_string (string_of_int !lcnt);
    print_endline " simple patch";
    lcnt := !lcnt + 1;
    loop chgset_orig bp) simple_patches)

(* function to detect whether two solutions (a solution is a list of
   bp's) are really equal, but with different orderings of the bp's
 *)
let redundant_sol sol1 sol2 = 
  List.for_all (function bp1 -> List.mem bp1 sol2) sol1 &&
  List.for_all (function bp2 -> List.mem bp2 sol1) sol2

let rec filter_redundant solutions =
  match solutions with
  | [] -> []
  | s :: sols -> s :: List.filter (function s' ->
      not(redundant_sol (list_of_bp s) (list_of_bp s'))) 
		       (filter_redundant sols)

let implies b1 b2 = not(b1) || b2

let filter_more_abstract abs_terms =
  let keep_sol p =
    List.for_all (function p' -> 
      implies (Diff.can_match p p' || Diff.can_match p' p) (gsize p <= gsize p')
		 ) abs_terms in
  List.filter keep_sol abs_terms

let filter_smaller chgset solutions =
  let keep_sol bp = 
    List.for_all
      (function bp' -> bp = bp' || 
      if Diff.subpatch_changeset chgset bp bp' 
          && Diff.subpatch_changeset chgset bp' bp
      then 
        !noncompact || Difftype.csize bp' <= Difftype.csize bp
      else true
      )
      solutions
  in
  (*print_string "[Main] filter_small considering ";*)
  (*print_string (string_of_int (List.length solutions));*)
  (*print_endline " solutions";*)
  (*List.map list_of_bp *)
  (List.filter keep_sol solutions)

let remove_disj found_nxt bp =
  if List.exists (fun bp' -> Diff.disjoint_domains (bp,bp')) found_nxt
  then found_nxt
  else bp :: found_nxt

let generate_sols chgset_orig simple_patches =
  (*Diff.no_occurs := List.length chgset_orig - !exceptions;*)
  print_endline ("[Main] min sup = " ^ string_of_int !Diff.no_occurs);
  let unwrap bp = match bp with 
  | None -> raise (Diff.Fail "unable to unwrap")
  | Some bp -> bp in
  let extend_bp bp_old bp_new = 
    let rec loop bp_old bp_new =
      match bp_old with
      | Difftype.UP _ -> Difftype.SEQ(bp_old,bp_new)
      | Difftype.SEQ (a, b) -> Difftype.SEQ (a, loop b bp_new) 
      | _ -> raise (Diff.Fail "extend_bp format")
    in
    match bp_old with
    | None -> Some bp_new
    | Some bp_old -> Some (loop bp_old bp_new) in
  let app_pred cur_bp bp = 
    (
     let nbp = unwrap (extend_bp (Some cur_bp) bp) in
     if !Diff.relax 
     then (
       let chgset' = Diff.apply_changeset nbp chgset_orig in
       let chgset''= Diff.apply_changeset cur_bp chgset_orig in
       not(chgset' = chgset'')
      ) && Diff.safe_part_changeset nbp chgset_orig 
     else
       Diff.safe_part_changeset nbp chgset_orig 
    )
  in
  (*  let restrict_bps cur_bp bps =
      List.filter (function bp ->
      not(Diff.subpatch_changeset chgset_orig bp cur_bp)
      ) bps in
   *)
  let next_bps bps cur_bp = match cur_bp with
  | None -> List.filter (function bp ->
      Diff.safe_part_changeset bp chgset_orig
			) bps (*simple_patches*)
  | Some cur_bp -> (
      (*print_string "[Main] considering next w.r.t.\n\t";*)
      (*print_endline (Diff.string_of_diff cur_bp);*)
      let res = List.filter (function bp ->
        try app_pred cur_bp bp with Diff.Nomatch -> false) bps
      in
      res
     )
  in
  let add_sol cur_bp sol = 
    match cur_bp with 
    | None -> print_endline "[Main] no solutions?"; []
    | Some cur_bp -> (
        if !print_adding
        then (
          print_endline ("[Main] trying solution... (" ^
                         string_of_int (List.length sol) ^")");
          print_endline (Diff.string_of_diff cur_bp)
         );
        filter_smaller chgset_orig (cur_bp :: sol)
       ) in
  (*  let isComplete bp = Diff.complete_changeset 
      chgset_orig (list_of_bp bp) in
   *)
  let rec gen sol bps_pool cur_bp =
    (*if try isComplete (unwrap cur_bp) with _ -> false*)
    (*then add_sol cur_bp sol*)
    (*else*)
    (*let bps' = filter_smaller chgset_orig (next_bps bps cur_bp) in*)
    let bps' = next_bps bps_pool cur_bp in
    if bps' = []
    then add_sol cur_bp sol
    else (
      (*print_endline ("[Main] bps'.length " ^*)
      (*string_of_int (List.length bps'));*)
      List.fold_left (fun sol bp ->
	let nbp = extend_bp cur_bp bp in
	(* let nbps = restrict_bps (unwrap nbp) bps_pool in *)
	(* gen sol nbps nbp *)

	(* remove bp from the list of next bps to select since we know that
	 * the same bp can not be applied twice
	 *)
	if !prune
	then 
          if List.exists (function bp' -> 
            Diff.subpatch_changeset chgset_orig (unwrap nbp) bp'
			 ) sol
          then sol
          else 
            let bps_new_pool = List.filter (fun bp' -> not(bp = bp')) bps_pool in
            gen sol bps_new_pool nbp
	else 
          let bps_new_pool = List.filter (fun bp' -> not(bp = bp')) bps_pool in
      	  gen sol bps_new_pool nbp
		     ) sol bps'
     )
  in
  if simple_patches = []
  then (
    print_endline "[Main] no input to work with";
    [])
  else
    let res = gen [] simple_patches None in
    let res_final = 
      if !prune
      then
	res +> List.filter
	  (function bp -> res +> List.for_all
	      (function bp' ->
          	(* bp' <= bp || not(bp <= bp') *)
		(* Diff.subpatch_changeset chgset_orig bp' bp
		   || *) 
                if bp = bp' || not(Diff.subpatch_changeset chgset_orig bp bp')
                then true
                else begin
                  print_endline "[Main] final pruning : ";
                  print_endline (Diff.string_of_diff bp);
                  print_endline "[Main] because we found a larger patch:";
                  print_endline (Diff.string_of_diff bp');
                  false
                end
	      )
	  )
      else res 
    in
    print_endline ("[Main] found " ^ string_of_int (List.length res_final) ^ " solutions");
    List.map list_of_bp res_final


(* a solution is a list of TU patches, not a SEQ value *)
let print_sol sol =
  print_endline "{{{";
  List.iter (function bp -> 
    print_endline (Diff.string_of_diff bp);
	    ) sol;
  print_endline "}}}"

let print_sols sols =
  let cnt = ref 1 in
  List.iter (function sol ->
    print_string "[Main] solution #";
    print_endline (string_of_int !cnt);
    print_sol sol;
    cnt := !cnt + 1
	    ) sols

(* if we are relaxed get all the simple patches that are relaxed_safe for
 * the changeset and otherwise we can simply get all the ones that occur
 * everywhere
 *)
let get_all_safe changeset abs_patches =
  print_endline "[Main] filter_all";
  if not(!Diff.relax)
  then Diff.filter_all abs_patches
  else 
    List.fold_left
      (fun acc_bps bp_list ->
        Diff.non_dub_app
          (List.filter 
             (function bp -> Diff.safe_part_changeset bp changeset)
             bp_list)
          acc_bps
      )
      []
      abs_patches

(* we are given a big list of TUs and now we wish to produce SEQ-patches
 * (basically lists of TUs) so that we have one which is largest. We note that
 * each TU is derived such that it should actually be applied in parallel with
 * all others. Thus, there could be cases where two patches overlap without
 * being in a subpatch relationship. The question is now: is it always the case
 * that one could be applied before the other?
 *)


(* this function takes a list a atomic patches and partitions them into those
 * that are equivalent and those for which that information is unknown; finally
 * it returns the "unknown" and one from each of the equivalence classes
 *)
let strip term_pairs abs_patches =
  let in_eq atomp eq_class =
    match eq_class with
    | [] -> raise (Diff.Fail "in_eq empty")
    | atomp' :: _ -> 
        Diff.subpatch_changeset term_pairs atomp atomp' &&
        Diff.subpatch_changeset term_pairs atomp' atomp
  in
  let rec add_atom part atomp =
    match part with
    | [] -> [[atomp]]
    | eq_class :: part ->
        if in_eq atomp eq_class 
        then 
          if !noncompact
          then (atomp :: eq_class) :: part
          else filter_smaller term_pairs (atomp :: eq_class) :: part
        else eq_class :: add_atom part atomp
  in
  let pot_res = List.fold_left (fun part atomp ->
    add_atom part atomp
			       ) [] abs_patches in
  (*List.map (fun eq_class -> List.hd (filter_smaller term_pairs eq_class )) pot_res*)
  List.rev_map (fun eq_class -> List.hd eq_class) pot_res


let spec_main () =
  Diff.abs_depth     := !depth;
  Diff.abs_subterms  := !max_level;
  file_pairs := Reader.read_spec !mfile; (* gets names to process in file_pairs *)
  (* now make diff-pairs is a list of abs-term pairs *)
  let term_pairs = 
    List.fold_left (fun acc_pairs (lfile, rfile) ->
      try 
	Reader.read_filepair_defs lfile rfile @ acc_pairs
      with (Failure _) -> acc_pairs)
      [] !file_pairs
      +> List.filter 
      (function (l,r) -> not(!only_changes) || not(l = r))
  in
  (* assume that a threshold of 0 means the user did not set it
   * thus, set it to max instead 
   *)
  if !threshold = 0
  then threshold := List.length term_pairs;
  Diff.no_occurs := !threshold;
  print_endline ("[Main] Constructing all safe parts for " ^ 
		 string_of_int (List.length term_pairs) ^ " term pairs");

  let filtered_patches = 
    (* if !do_dmine *)
    (* then do_datamining abs_patches *)
    (* else get_all_safe term_pairs abs_patches *)
    Diff.find_simple_updates_merge_changeset term_pairs
      +> (function x ->
	begin
	  print_string "[Main] find_simple_updates_merge return this many updates: ";
	  x +> List.length +> string_of_int +> print_endline;
	  if !Jconfig.print_abs
	  then begin
	    x +> List.iter (function tu ->
	      tu 
		+> Diff.string_of_diff 
		+> print_endline);
	  end;
	  x
	end
	 )
      +> (function x ->
	print_endline "[Main] filtering all safe patches."; 
	x)
      +> List.filter (function tu -> 
	term_pairs +> 
	for_some !threshold
	  (Diff.safe_part tu)
		     )
      +> (function tus -> begin
	print_string "[Main] after filtering we have this many updates: ";
	tus +> List.length +> string_of_int +> print_endline;
	tus
      end
	 )
      +> List.rev_map Diff.renumber_metas_up
      +> Diff.rm_dub
  in
  let stripped_patches = 
    if !strip_eq
    then strip term_pairs filtered_patches 
    else filtered_patches
  in
  if !print_raw
  then (
    print_endline "Raw list of simple updates";
    print_endline "{{{";
    List.iter (fun d ->
      print_endline (Diff.string_of_diff d);
      print_endline " ++ ";
	      ) stripped_patches;
    print_endline "}}}"
   );
  print_endline ("[Main] generating solutions from " 
		 ^ string_of_int (List.length stripped_patches)
		 ^ " inputs");
  let solutions = generate_sols term_pairs stripped_patches in
  print_sols solutions


let spec_main_term_pairs term_pairs =
  Diff.abs_depth     := !depth;
  Diff.abs_subterms  := !max_level;
  (* assume that a threshold of 0 means the user did not set it
   * thus, set it to max instead 
   *)
  if !threshold = 0
  then threshold := List.length term_pairs;
  Diff.no_occurs := !threshold;
  print_endline ("[Main] Constructing all safe parts for " ^ 
		 string_of_int (List.length term_pairs) ^ " term pairs");

  let filtered_patches = 
    (* if !do_dmine *)
    (* then do_datamining abs_patches *)
    (* else get_all_safe term_pairs abs_patches *)
    Diff.find_simple_updates_merge_changeset term_pairs
      +> (function x ->
	begin
	  print_string "[Main] find_simple_updates_merge return this many updates: ";
	  x +> List.length +> string_of_int +> print_endline;
	  if !Jconfig.print_abs
	  then begin
	    x +> List.iter (function tu ->
	      tu 
		+> Diff.string_of_diff 
		+> print_endline);
	  end;
	  x
	end
	 )
      +> (function x ->
	print_endline "[Main] filtering all safe patches."; 
	x)
      +> List.filter (function tu -> 
	term_pairs +> 
	for_some !threshold
	  (Diff.safe_part tu)
		     )
      +> (function tus -> begin
	print_string "[Main] after filtering we have this many updates: ";
	tus +> List.length +> string_of_int +> print_endline;
	tus
      end
	 )
      +> List.rev_map Diff.renumber_metas_up
  in
  if !print_raw
  then (
    print_endline "Raw list of simple updates";
    print_endline "{{{";
    List.iter (fun d ->
      print_endline (Diff.string_of_diff d);
      print_endline " ++ ";
	      ) filtered_patches;
    print_endline "}}}"
   );
  print_endline "[Main] generating solutions...";
  let stripped_patches = 
    if !strip_eq
    then strip term_pairs filtered_patches 
    else filtered_patches
  in
  let solutions = generate_sols term_pairs stripped_patches in
  print_sols solutions



    
(* ---------------------------------------------------------- *
 * imported from graph.ml                                     *
 *                                                            *
 * In the end, this could do well with being put in its own   *
 * module.                                                    *
 * ---------------------------------------------------------- *)
let meta_counter = ref 0
let reset_meta () = meta_counter := 0
let inc_meta () = meta_counter := !meta_counter + 1
let new_meta_id () =
  let v = !meta_counter in (
  inc_meta();
  let mid = "X" ^ string_of_int v in
  mkA("meta", mid), mid
 )

let new_meta () = 
  let v = !meta_counter in (
  inc_meta();
  mkA("meta", "X" ^ string_of_int v)
 )

let nodes_of_graph g = 
  g#nodes#tolist +> List.rev_map fst

let nodes_of_graph2 g =
  g#nodes#tolist 
    +> List.filter (function (i,gt) -> Diff.non_phony gt && not(Diff.is_control_node gt))
    +> List.rev_map fst

let renumber_metas t metas =
  match view t with
  | A("meta", mvar) -> (try 
      let v = List.assoc mvar metas in
      mkA ("meta", v), metas
  with _ -> 
    let nm, mid = new_meta_id () in
    nm, (mvar, mid) :: metas)
  | _ -> t, metas

(* generic folding on gterms; produces new term and some accumulated result
 * which is useful when one wants to modify a gterm and return some env
 * computed as part of the transformation
 *)
let fold_botup term upfun initial_result =
  let rec loop t acc_result =
    match view t with
    | A _ -> upfun t acc_result
    | C (ct, ts) -> 
        let new_terms, new_acc_result = List.fold_left
            (fun (ts, acc_res) t ->
              let new_t, new_acc = loop t acc_res in
	      new_t :: ts, new_acc
            ) ([], acc_result) ts
        in
        upfun (mkC(ct, List.rev new_terms)) new_acc_result
  in
  loop term initial_result

let string_of_pattern p =
  let loc p = match view p with
  | C("CM", [t]) -> 
      if !Jconfig.verbose
      then Diff.verbose_string_of_gtree t
      else Diff.string_of_gtree' t
  | skip when skip == view ddd -> "..."
  | gt -> raise (Match_failure (Diff.string_of_gtree' p, 604,0)) in
  (*
    let meta_strings = List.rev_map Diff.collect_metas p +> tail_flatten in
    let head = "@@\n" ^ 
    String.concat "\n" meta_strings ^
    "\n@@\n"
    in
   *)
  (* head ^  *)
  String.concat "\n" (List.map loc p)

let renumber_metas_pattern pat =
  let old_meta = !meta_counter in
  reset_meta ();
  let loop (acc_pat, env) p  =
    match view p with
    | C("CM", [p]) -> 
        let p', env' = fold_botup p renumber_metas env in
        (mkC("CM", [p'])) :: acc_pat, env'
    | skip when skip == view ddd -> ddd :: acc_pat, env
    | _ -> raise (Match_failure (string_of_pattern [p], 613,0))
  in
  let (rev_pat, env) = List.fold_left loop ([], []) pat in
  (meta_counter := old_meta; List.rev rev_pat)

let renumber_fresh_metas_pattern patterns =
  let rec rename_pat p =
    match view p with
    | A("meta",_) -> new_meta () 
    | C(ty,ts) -> mkC(ty, List.rev_map rename_pat ts +> List.rev)
    | skip when skip == view ddd -> ddd 
    | _ -> p in
  List.rev_map rename_pat patterns


let renumber_metas_gtree gt = 
  let old_meta = !meta_counter in
  reset_meta ();
  let gt', env = fold_botup gt renumber_metas [] in
  meta_counter := old_meta; gt'

let renumber_metas_gtree_env env gt = 
  let old_meta = !meta_counter in
  reset_meta ();
  let gt', env = fold_botup gt renumber_metas env in
  meta_counter := old_meta; 
  List.iter (function (m1,m2) -> print_string (" ;" ^ m1 ^ "->" ^ m2)) env;
  print_newline ();
  gt

let rev_assoc e a_list =
  mkA("meta", fst (List.find (function (k,v) -> v == e) a_list))

(* given element "a" and lists, prefix all lists with "a" *)
let prefix a lists =
  List.rev_map (function l -> a :: l) lists +> List.rev

(* tail recursive append that preserves ordering *)
let (@@@) l1 l2 = List.rev l1 +> List.fold_left 
    (fun acc_l e1 -> e1 :: acc_l) l2

(* given list "l" and lists "ls" prefix each element of list "l" to each list in
 * "ls"; 
 *)
let prefix_all l ls =
  l +> List.fold_left (fun acc_prefix e -> 
    prefix e ls @@@ acc_prefix
		      ) []

(* given a list of lists, produce all permutations where one
 * takes one element from each list in the order given
 *)
let rec gen_perms lists =
  match lists with
  | [] -> [[]]
  | l :: ls -> prefix_all l (gen_perms ls)

let is_meta m = match view m with 
| A("meta", _) -> true
| _ -> false

let is_match m = match view m with
| C("CM", [p]) -> true
| _ -> false


let get_metas_single p = 
  let rec loop acc_metas p =
    if is_meta p then p +++ acc_metas
    else match view p with
    | A _ -> acc_metas
    | C (_,ts) -> List.fold_left (fun acc_metas p -> loop acc_metas p) acc_metas ts
  in
  loop [] p

let get_metas_pattern ps =
  List.fold_left (fun acc_metas p -> 
    List.fold_left (fun acc_metas m -> m +++ acc_metas) acc_metas (get_metas_single p)
		 ) [] ps

let intersect_lists l1 l2 =
  List.filter (function e1 -> List.mem e1 l2) l1

let rec is_subset_list eq_f l1 l2 =
  l1 = [] ||
  match l1, l2 with
  | x :: xs, y :: ys when eq_f x y -> is_subset_list eq_f xs ys
  | _, _ -> false

let num_metas p =
  List.length (get_metas_single p)

let rec num_subterms p =
  match view p with
  | A _ -> 1
  | C (_, ts) -> List.fold_left (fun acc_sum p -> num_subterms p + acc_sum) 1 ts


(* a higher value allows a term means the term is more abstract and a
   lower means it is less abstract; "number of meta per subterm"
   f(X) = 1/3
   f(sizeof(X)) = 1/5
   thus, the latter is less abstract than the former
 *)

let abstractness p =
  let mv = num_metas p in
  let st = num_subterms p in
  float mv /. float st

let infeasible p = Diff.infeasible p

let (=>) = Diff.(=>)
let cont_match = Diff.cont_match_new
(* let cont_match = Diff.cont_match *)


let exists_cont_match g p = nodes_of_graph g +> List.exists (cont_match g p) 
let (|-) g p = exists_cont_match g p

(*
  let g_glob = ref (None : (Diff.gflow * 'a) option )
 *)
let get_indices t g =
  g#nodes#tolist +> List.fold_left (fun acc_i (i,t') -> if t' == t then i :: acc_i else acc_i) []

let abs_ht = Diff.TT.create 591
let misses = ref 0
let common_num = ref 0 
let common_calls = ref 0



let rec abstract_term_hashed depth t =
  try
    Diff.TT.find abs_ht t
  with Not_found -> (
    let res = abstract_term depth [] t in
    misses := !misses + 1;
    Diff.TT.replace abs_ht t res;
    res
   )
and abstract_term depth env t =
  let rec rm_dups xs = List.fold_left (fun acc_xs x -> x +++ acc_xs) [] xs in
(*
  let follow_abs t_sub = 
  match !g_glob with
  | None -> false
  | Some (g, pa) -> 
  let idxs = pa +> List.fold_left (fun acc_i t' -> 
  if Diff.can_match t t'
  then get_indices t' g +>
  List.fold_left (fun acc_i i -> i +++ acc_i) acc_i
  else acc_i) [] in 
  (* among the nodes, where the top-level term t occurs is there some
   * location where in all the following paths eventually the subterm
   * occurs?
   *)
  List.exists (function i -> Diff.find_embedded_succ g i t_sub) idxs 
  (*    if List.exists (function i -> Diff.find_embedded_succ g i t_sub) idxs
	then (print_endline ("[Main] follow_abs: " ^ (Diff.string_of_gtree' t_sub)); true) else false  *)
  in
 *)
  let rec loop depth env t =
    try [rev_assoc t env], env
    with Not_found ->
      let meta, id = new_meta_id ()
      in
      if depth = 0 (* || follow_abs t *)
      then [meta], (id, t) => env
      else 
        if is_meta t
        then [t],env 
        else  
          (match view t with
          | A _ -> (* always abstract atoms *)
	      [meta], (id, t) => env
          | C("storage", _) -> [t], env
          | C("call", f :: ts) ->
	      (* generate abstract versions for each t ∈ ts *)
	      let meta_lists, env_acc =
                List.fold_left (fun (acc_lists, env') t -> 
		  let meta', env'' = loop (depth - 1) env' t
		  in (meta' :: acc_lists), env''
			       ) ([], env) ts in
	      (* generate all permutations of the list of lists *)
	      let meta_perm = gen_perms (List.rev meta_lists) in
	      (* construct new term from lists *)
	      t :: List.rev (List.fold_left (fun acc_meta meta_list ->
		mkC("call", f :: meta_list) :: acc_meta
					    ) [] meta_perm), env_acc
		(* | C _ when !max_level <= gsize t -> [t], env *)
          | C(ty, ts) ->
	      (* generate abstract versions for each t ∈ ts *)
	      let meta_lists, env_acc =
                List.fold_left (fun (acc_lists, env') t -> 
		  let meta', env'' = loop (depth - 1) env' t
		  in (meta' :: acc_lists), env''
			       ) ([], env) ts in
	      (* generate all permutations of the list of lists *)
	      let meta_perm = gen_perms (List.rev meta_lists) in
	      (* construct new term from lists *)
	      t :: List.rev (List.fold_left (fun acc_meta meta_list ->
		mkC(ty, meta_list) :: acc_meta
					    ) [] meta_perm), env_acc
                (*
		  | _ -> [meta;t], (id, t) => env
                 *)
          )
  in
  let metas, env = loop depth env t in
  List.filter (function p -> not(infeasible p)) (rm_dups metas), env 

let print_patterns gss ps =
  List.iter (function p -> 
    print_endline "[[[";
    print_endline (string_of_pattern p);
    print_endline "]]]";
    (* show supporting functions *)
    List.iter (
    function [f] -> 
      if exists_cont_match f p
      then 
        print_string (" " ^ Diff.get_fun_name_gflow f)
   ) gss;
    print_newline ();
	    ) ps

(* let non_phony p = match view p with *)
(* | A("phony", _)  *)
(* | C("phony", _)  *)
(* | A(_, "N/H")  *)
(* | A(_, "N/A") -> false *)
(* | _ -> true *)

let concrete_of_graph g =
  let nodes = g#nodes#tolist in
  let ns = nodes +> List.filter (function (i,t) -> Diff.non_phony t) in
  let ns' = ns +> List.filter (function (i,t) -> 
    (g#successors i)#length <= 1
			      ) in
  ns' +> List.rev_map snd 

let concrete_of_graph_indicies g =
  let nodes = g#nodes#tolist in
  let ns = nodes +> List.filter (function (i,t) -> Diff.non_phony t 
      && not(Diff.is_control_node t)) in
  ns +> List.rev_map fst 

    
let concrete_nodes_of_graph g =
  let nodes = g#nodes#tolist in
  let ns = nodes +> List.filter (function (i,t) -> Diff.non_phony t) in
  let ns' = ns +> List.filter (function (i,t) -> 
    (g#successors i)#length <= 1
			      ) in
  ns' 
    
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

let extract_pat p = Diff.extract_pat p

let follows_p p g pa =
  let succ_nodes = ref [] in
  let idxs = pa +> List.fold_left (fun acc_i t' -> 
    if Diff.can_match_nested p t'
    then get_indices t' g +>
      List.fold_left (fun acc_i i -> i +++ acc_i) acc_i
    else acc_i) [] in
  let add_node i' = 
    succ_nodes := i' +++ !succ_nodes in
  idxs +> List.iter (function i -> dfs_iter i add_node g);
  !succ_nodes +> List.fold_left (fun acc_pa i -> 
    g#nodes#find i +++ acc_pa
				) [] +> List.filter (function t -> List.mem t pa)

let rm_dups xs = List.fold_left (fun acc_xs x -> x +++ acc_xs) [] xs


let follows_sp sp g pa =
  if sp = []
  then pa
  else 
    let p_last = extract_pat (List.nth sp (List.length sp - 1)) in
    rm_dups (follows_p p_last g pa)

(* find x in xs and return the list after the first occurrence of x *)
let rec chop x xs = match xs with
| [] -> raise Not_found
| x' :: xs' when x = x' -> xs'
| _  :: xs' -> chop x xs'

(* subsequence *)
let rec (<++) p p' = p = [] || match p, p' with
| x :: xs, y :: ys when x = y -> xs <++ ys
| x :: xs, ys -> let ys' = try Some (chop x ys) with Not_found -> None in
  (match ys' with
  | None -> false
  | Some ys' -> xs <++ ys')
| _, _ -> false 

let flush_string s = (print_string s; flush stdout)

let standalone_term t = match view t with
| C("return", [m]) -> false
| C("storage", _) -> false
      (* | C("call", _) -> false *)
| _ -> true

let get_nested_subterms t = 
  let rec loop depth acc_ts t =
    if depth = 0
    then acc_ts
    else 
      let acc_ts' = if standalone_term t then t +++ acc_ts else acc_ts in
      match view t with
      | A _ -> acc_ts'
      | C (_, ts) -> let l = loop (depth - 1) in
        List.fold_left l acc_ts' ts in
  loop !nesting_depth [] t

(* function that finds the traces of a pattern wrt to a graph
 *)
let get_pattern_traces g sp =
  g#nodes#tolist 
    +> List.fold_left (fun acc_trs (i,gt) -> 
      match Diff.get_traces g sp i with
      | None -> acc_trs
      | Some trs -> trs :: acc_trs
		      ) []

(* function that finds the traces of a pattern wrt to a graph but only
   considering "silly" nodes in the graph in order to reduce the
   running time
 *)
let get_pattern_traces_real g sp =
  g#nodes#tolist 
    +> List.filter 
    (function (i,gt) -> 
      Diff.non_phony gt
	&& not(Diff.is_control_node gt)
	&& not(Diff.is_head_node gt)
    )		      
    +> List.fold_left (fun acc_trs (i,gt) -> 
      match Diff.get_traces g sp i with
      | None -> acc_trs
      | Some trs -> trs :: acc_trs
		      ) []


(* a pattern sp is a subpattern of another sp' if all the traces of sp
   are contained within the traces of sp *)
let embedded_trace g tr1 tr2 = 
  tr1 +> List.for_all (function t_list -> 
    tr2 +> List.exists (function t_list' -> 
      t_list <++ t_list'
		       )
		      )
let print_trace tr =
  v_print_string ("[Main] " ^ string_of_int (List.length tr) ^ ": ");
  tr +> List.iter 
    (function i_list -> 
      v_print_string ("<" ^ List.length i_list +> string_of_int ^ ">");
      v_print_string "[[ ";
      i_list 
	+> List.map string_of_int
	+> String.concat " > "
	+> v_print_string;
      v_print_string " ]] "
    );
  v_print_newline ()

let subpattern g sp1 sp2 =
  let trcs1 = get_pattern_traces g sp1 in
  let trcs2 = get_pattern_traces g sp2 in
  let subseq = sp1 <++ sp2 in
  let embed  = trcs1 +> List.for_all 
      (function trace1 ->
	trcs2 +> List.exists (function trace2 -> 
	  embedded_trace g trace1 trace2
			     )) in
  if  embed
      && not(trcs1 = [])
      && not(trcs2 = [])
      (* &&
	 subseq *)
  then 
    (v_print_endline "[Main] subsumed pattern:";
     v_print_endline (string_of_pattern sp1);
     v_print_endline "[Main] with traces";
     trcs1 +> List.iter print_trace;
     v_print_endline "[Main] by: ";
     v_print_endline (string_of_pattern sp2);
     v_print_endline "[Main] with traces";
     trcs2 +> List.iter print_trace;
     v_print_endline ("[Main] embed,subseq: " ^ string_of_bool embed ^ "," ^ string_of_bool subseq);
     true)
      (*  true *)
  else
    false


(* we are given a set of sets of flows and wish to verify that sp1 is
   a subpattern for sp2 in some graph for SOME of the sets of flows
 *)
let subpattern_some gss sp1 sp2 =
  gss +> for_some !threshold 
    (function flows ->
      flows +> List.exists (function f -> 
	subpattern f sp1 sp2
			   )
    )




let filter_shorter g pss =
  (* only keep around the largest according to subpattern relation*)
  let (<@@) p1 p2 = subpattern g p1 p2 in
  let keep_fun sp = not(pss +> List.exists (function sp' -> (sp <@@ sp') && not(sp = sp'))) in
  List.filter keep_fun pss

let embedded_pattern sp1 sp2 =
  let (!!) x = match view x with
  | C("CM", [t]) -> t
  | _ when x == ddd -> x
  | _ -> raise (Diff.Fail (
		"!! applied to non-pattern:" ^ 
		Diff.string_of_gtree' x
	       )) in
  let rec chop x xs = match xs with
  | [] -> raise Not_found
  | x' :: xs' when 
      Diff.can_match !!x !!x'  
	&& abstractness x <= abstractness x' -> xs'
  | x' :: xs' when Diff.find_match !!x !!x' -> xs' 
  | x' :: xs' -> chop x xs' in
  let rec (<++) p p' = p = [] || match p, p' with
  | x :: xs, ys -> 
      let ys' = 
	try Some (chop x ys) with Not_found -> None 
      in
      (match ys' with
      | None -> false
      | Some ys' -> xs <++ ys')
  | _, _ -> false in
  sp1 <++ sp2

let filter_shorter_sub_old gss sub_pat pss =
  let (<++) = embedded_pattern in
  let (<@@) p1 p2 = sub_pat p1 p2 in
  let (===) sp1 sp2 = sp1 <@@ sp2 && sp2 <@@ sp1 in
  let add_eq acc_eq_clss sp = 
    let rec loop eq_clss =
      match eq_clss with
      | [] -> [[sp]]
      | eq_cls :: eq_clss when eq_cls +> List.for_all ((===) sp) -> (sp +++ eq_cls) :: eq_clss
      | x :: eq_clss -> x :: loop eq_clss in
    loop acc_eq_clss in
  (* partition list into eq-classes *)
  let eq_clss = pss +> List.fold_left add_eq [] in
  eq_clss 
    +> List.rev_map (function eq_cls -> eq_cls +> List.filter (
      function sp -> not(eq_cls +> List.exists (function sp' -> sp <++ sp' && not(sp = sp')))
     ))
    +> tail_flatten

let gsize_spattern sp = Diff.gsize_spattern sp

let filter_shorter_sub_unsafe gss sub_pat pss =
  print_endline "[Main] patterns BEFORE filtering";  
  pss +> print_patterns gss;
  pss
    +> List.fold_left 
    (fun acc_patterns sp -> 
      if pss +>
	List.for_all (function sp' -> 
	  not(sub_pat sp sp')
	|| sub_pat sp' sp && gsize_spattern sp' <= gsize_spattern sp
		     )
      then 
	sp :: acc_patterns
      else begin
	print_endline "[Main] not including:";
	print_patterns gss [sp] ;
	acc_patterns;
      end
    ) []


let filter_shorter_sub gss sub_pat pss =
  print_endline "[Main] patterns BEFORE filtering";  
  pss +> print_patterns gss;
  pss
    +> List.fold_left 
    (fun acc_patterns sp -> 
      if pss +>
	List.for_all (function sp' -> 
	  not(sub_pat sp sp' && sub_pat sp' sp)
	|| gsize_spattern sp' <= gsize_spattern sp
		     )
      then 
	sp :: acc_patterns
      else
	acc_patterns
    ) []



(* let keep_fun sp =  *)
(*   pss +> List.for_all (function sp' ->  *)
(*     implies (sp <@@ sp') (sp' <@@ sp && sp' <++ sp) *)
(*   ) *)
(* in *)
(*   List.filter keep_fun pss *)

let equal_pattern_term gt1 gt2 =
  let ngt1 = renumber_metas_gtree gt1 in
  let ngt2 = renumber_metas_gtree gt2 in
  if ngt1 = ngt2
  then (
    v_print_endline ("[Main] equal patterns:\n\t" ^
		     Diff.string_of_gtree' gt1 ^
		     "\n\t=\n\t" ^
		     Diff.string_of_gtree' gt2);
    true)
  else (
    v_print_endline ("[Main] NOT equal patterns:\n\t" ^
		     Diff.string_of_gtree' ngt1 ^
		     "\n\t!=\n\t" ^
		     Diff.string_of_gtree' ngt2);
    false)


let find_seq_patterns is_frequent_sp is_common g =
  []
    (*
      print_endline "WRONG FUNCTION ******************";
      reset_meta();
      let pa = (concrete_of_graph g) +> List.filter 
      (function t -> is_common t) in
      if !verbose 
      then ( 
      print_endline "[Main] pa = ";
      pa +> List.iter (function t -> print_endline (Diff.string_of_gtree' t));
      );
      let nodes = nodes_of_graph g in
      let (<==) p ps = ps +> (* List.exists (function p' -> p <++ p') *)
      List.exists (subpattern g p) 
      in
      let (|-) g p = List.exists (cont_match g p) nodes in
      let (+++) x xs = if List.mem x xs then xs else (
      if !print_adding then (
      print_string "[Main] attempting to add ";
      print_endline (string_of_pattern x);
      );
      filter_shorter g (x :: xs)
      (* x :: xs *)
      ) in
      let (++) ps p = p +++ ps
      in
      let valid p' =
      let rec loop p =
      match p with 
      | [] -> true
      | p :: seq when loop seq && is_match p -> not(List.exists (function p' -> 
      equal_pattern_term p p') seq) &&
      (match get_metas_single p with
      | [] -> true
      | p_metas -> 
      (match get_metas_pattern seq with
      | [] -> true
      | seq_metas -> not(intersect_lists p_metas seq_metas = []))
      )
      | skip :: seq when skip == ddd -> loop seq
      | _ -> false
      in
      match p' with
      | skip :: _ when skip == ddd -> false
      | _ -> loop p'
      in
      let rec grow' ext p ps (p', env') =
      (* flush_string "."; *)
      let pp' = renumber_metas_pattern (ext p p') in
      if !verbose then ( 
      print_string ("[Main] testing : " ^ List.map Diff.string_of_gtree' pp' +> String.concat " ");
      );
      if (* g |- pp' &&  -- this test is already performed in grow below*)
      valid pp'
      && (v_print " valid "; is_frequent_sp pp')
      && (v_print "is_freq "; not(pp' <== ps))
      then (
      (*
	print_string "adding ";
	print_endline (string_of_pattern pp');  *)
      v_print_endline "not_subseq";
      let ps' = ps ++ pp' in
      grow ps' (ext p p', env')
      )
      else (
      v_print_endline "";
      ps)
      and grow ps (p, env) =
      (* flush_string "#"; *)
      let ext1 p1 p2 = if p1 = [] then [mkC("CM",[p2])] else p1 @ [mkC("CM", [p2])] in
      let ext2 p1 p2 = if p1 = [] then [mkC("CM",[p2])] else p1 @ (ddd :: [mkC("CM", [p2])]) in
      (* produce (meta list * env) list *)
      let pa_f = follows_sp p g pa in
      let pa_f = tail_flatten (List.rev_map get_nested_subterms pa_f) in
      g_glob := Some (g, pa_f);
      let abs_P_env = List.rev_map (function t -> 
      let metas, env = abstract_term !depth env t in
      metas, env
      ) pa_f in
      g_glob := None;
      (* 
	 print_string "[Main] number of abstractions to consider : ";
	 let ms = ref 0 in
	 List.iter (function (ps, _) -> ms := List.length ps + !ms) abs_P_env;
	 print_endline (string_of_int !ms);
       *)            
      (*
	print_endline "[Main] abstractions to consider";
	abs_P_env +> List.iter (function (ps, env) -> 
	ps +> List.iter (function p -> print_endline (Diff.string_of_gtree' p));
	print_endline "[Main] under environment";
	Diff.print_environment env;
	); 
       *)
      let nextP1 = abs_P_env +> 
      List.fold_left (fun acc_p_env (ps, env) -> 
      let valid_ps = List.filter (function p' -> g |- (ext1 p p')) ps 
      in
      if valid_ps = []
      then acc_p_env
      else List.rev_map (function p -> (p, env)) valid_ps 
      :: acc_p_env
      ) [] 
      +> tail_flatten in
      let abs_P_env' = abs_P_env +> List.fold_left (fun acc_ps_env (ps, env) -> 
      let ps' = ps +> List.filter (function p' ->
      not(nextP1 +> List.exists (function (p'', env') -> p' = p''))
      ) in
      (ps', env) :: acc_ps_env
      ) [] in
      let nextP2 = abs_P_env' +> List.fold_left (fun acc_p_env (ps, env) -> 
      let valid_ps = List.filter (function p' -> g |- (ext2 p p')) ps 
      in
      if valid_ps = []
      then acc_p_env
      else List.rev_map (function p -> (p, env)) valid_ps 
      :: acc_p_env
      ) [] 
      +> tail_flatten in
      let ps' = 
      List.fold_left (fun acc_ps pair -> grow' ext1 p acc_ps pair) ps nextP1 in
      List.fold_left (fun acc_ps pair -> grow' ext2 p acc_ps pair) ps' nextP2
      in
      grow [] ([], [])
      (*
	let pairs = List.fold_left (fun acc_p_env (ps, env) -> 
	List.map (function p -> ([mkC("CM", [p])], env)) ps
	:: acc_p_env) 
	[] (List.map (reset_meta(); abstract_term depth []) pa) in
	List.fold_left (fun acc_ps next_pairs -> 
	print_endline ("Trying from fresh patterns.");
	next_pairs +> List.iter (function (ps,env) -> 
	string_of_pattern ps +> print_endline);
	List.fold_left grow acc_ps next_pairs) 
	[] pairs
       *)
     *) 

let missed = ref 0

(* this function checks (relative to a given graph) whether a
   node-pattern (np1) can precede another (np2)
 *)
exception Found_it

let precede_node_patterns g np1 np2 =
  let found = ref false in
  let f xo xi = 
    if not(xo = xi)
    then
      let t = Diff.get_val xi g in
      if Diff.can_match np2 t then
	(found := true; raise Found_it)
  in
  let node_ids = concrete_nodes_of_graph g 
      +> List.filter (function (i,t) -> Diff.can_match np1 t)
      +> List.rev_map fst
  in
  try begin
    node_ids +> List.iter (function i -> dfs_iter i (f i) g);
    !found;
  end
  with Found_it -> true


let precede_node_patterns_gss gss np1 np2 =
  gss +> for_some !threshold (function 
    | [f] -> precede_node_patterns f np1 np2
    | _ -> raise (Impossible 142))

(* Sort patterns according to precedence relationship such that p2 is
   put before p1 if p1 precedes p2.  Then, later because get_next
   preserves ordering we will try to extend the current pattern with
   p1 before trying with p2; together with pruning this should ensure
   we do a sensible longest contiguous first search
 *)
let sort_pa_env gss pa_env =
  let compare (p1,env) (p2,env) =
    if precede_node_patterns_gss gss p1 p2
    then 1
    else -1 in
  List.sort compare pa_env

let find_seq_patterns_new unique_subterms sub_pat is_frequent_sp orig_gss get_pa  =
  print_endline "[Main] growing patterns from functions: ";
  orig_gss +> List.iter (function [f] -> begin
    print_string "\t";
    f +> Diff.get_fun_name_gflow +> print_endline;
  end
    | _ -> raise (Diff.Fail "impossible match! in find_seq_patterns")
			);
  reset_meta();
  let mk_pat p = [mkC("CM",[p])] in
  let (<==) sp ps gss = ps +> List.exists (function sp' -> 
    sub_pat gss sp sp'
      && embedded_pattern sp sp'

      (*
	if sub_pat gss sp sp' 
	then 
	(print_endline "sub-pattern found :";
	print_patterns [sp];
	print_endline "is less than :";
	print_patterns [sp'];
	true)
	else
	false
       *)
					  ) in
  (*   let (||-) gss sp = is_frequent_sp gss sp in *)
  let (+++) x xs = 
    if List.mem x xs then xs else (
    if !print_adding then (
      print_endline "[Main] adding pattern ";
      print_endline (string_of_pattern x);
     );
    (*
      if !filter_patterns
      then filter_shorter_sub gss sub_pat (x :: xs)
      else x :: xs
     *)
    x :: xs
   ) in
  let (++) ps p = p +++ ps
  in
  let valid p' =
    let rec loop p =
      match p with 
      | [] -> true
      | p :: seq when 
	  loop seq 
	    && is_match p -> 
	      not(
	      List.exists (function p' -> 
		equal_pattern_term p p') seq
	     )
		&& (match get_metas_single p with
		| [] -> true
		| p_metas -> 
		    (match get_metas_pattern seq with
		    | [] -> true
		    | seq_metas -> not(intersect_lists p_metas seq_metas = []))
		   ) 
      | skip :: seq when skip == ddd -> loop seq
      | _ -> false
    in
    match p' with
    | skip :: _ when skip == ddd -> false
    | _ -> loop p' in
  let get_next abs_P_env ext p gss =
    if p = [] 
    then List.rev_map (function (p,e) -> (p,e,gss)) abs_P_env
    else
      begin
        v_print_string "[Main] get_next ... ";
      	let res = abs_P_env 
            +> List.fold_left 
            (fun acc_abs_P_env (pat, env) -> 
              
	      let gss' = gss +> List.filter 
		  (function 
              	    | [f] -> f |- (mk_pat pat) && f |- (ext p pat)
              	    | _ -> raise (Impossible 117)) in
      	      if List.length gss' < !threshold 
      	      then begin
            	if !Jconfig.print_abs
            	then begin
            	  print_string "[Main] not including pattern with threshold: ";
            	  gss' +> List.length +> string_of_int +> print_endline;
            	  print_endline "[Main] env: ";
            	  env +> List.iter (function (m, t) -> 
		    print_endline (m ^ " ⇾ " ^
				   Diff.string_of_gtree' t);
				   );
                  print_patterns gss' [(ext p pat)];
		end;
		acc_abs_P_env
	      end
	      else (pat,env, gss') :: acc_abs_P_env
	    ) [] in
	v_print_endline "done";
	res
      end 
  in
  (* ext1 = p1 p2  -- p2 is immediate successor *)
  let ext1 p1 p2 = 
    if p1 = [] 
    then [mkC("CM",[p2])] 
    else p1 @ [mkC("CM", [p2])] in
  (* ext2 = p1 ... p2 -- p2 is all-paths successor *)
  let ext2 p1 p2 = 
    if p1 = [] 
    then [mkC("CM",[p2])] 
    else p1 @ (ddd :: [mkC("CM", [p2])]) in
  let rec grow' ext p ps (p', env', gss) =
    (* flush_string "."; *)
    let ext_p = ext p p' in
    let pp' = ext_p (* renumber_metas_pattern ext_p *) in
    if !Jconfig.verbose then ( 
      print_string ("[Main] testing : " ^ 
		    List.map Diff.string_of_gtree' pp'
		      +> String.concat " ");
     );
    if
      valid pp'
        && (v_print " valid "; is_frequent_sp gss pp')
        && (v_print "is_freq "; 
	    if !prune then not((pp' <== ps) gss) else true)
    then (
      v_print_endline "not_subseq";
      let ps' = ps ++ pp' in
      let last_p =  pp' +> List.rev +> List.hd in
      if Diff.matches_exit last_p
      then
	(* if the last pattern matches an exit-node, there is no
	   need to grow the pattern any more *)
	ps'
      else
	grow ps' (ext_p, env', gss)
     )
    else (
      v_print_endline "";
      ps)
  and grow ps (p, env, gss) =
    v_print_string "[Main] getting common cterms after pattern: ";
    v_print_endline (string_of_pattern p);
    let abs_P_env = 
      get_pa p (* env *)
	(*      
		+> sort_pa_env gss
		+> List.filter 
		(function (pat,env) ->
		p = [] 
		|| gss
		+> for_some !threshold
		(function flows ->
		flows
		+> List.exists
		(function f ->
		f |- mk_pat pat
		)
		)
		)
	 *)
    in
    v_print_endline ("done (" ^ string_of_int (List.length abs_P_env) ^ ")");
    let nextP2 = get_next abs_P_env ext2 p gss in
    (* there is no need to look for matches of "p...p'" in case
       there were no matches of "p p'" because 
       |- p p' => |- p...p'

       thus, if we can determine that |- p...p' is not the case
       then we know that |- p p' can also NOT be the case 
     *)
    let abs_P_env' = abs_P_env
	(*
	  +> List.filter
	  (fun (pat, env) -> 
	  nextP2 +> List.exists 
	  (function (p'', env', gss') -> 
	  if Diff.node_pat_eq unique_subterms (pat, env) (p'', env')
	  then (
	  (* print_endline "pat eq:";
	     pat +> Diff.string_of_gtree' +> print_endline;
	     p'' +> Diff.string_of_gtree' +> print_endline;
	   *)
	  true
	  )
	  else
	  false
	  )
	  ) 
	 *) 
    in
    let nextP1 = get_next abs_P_env' ext1 p gss in
    v_print_endline ("[Main] from pattern :\n" ^ string_of_pattern p);
    v_print_endline ("[Main] potential new patterns : " ^ string_of_int (
							  List.length nextP1 + List.length nextP2));
    v_print_newline ();
    let ps' = 
      List.fold_left (fun acc_ps p_e_gss -> grow' ext2 p acc_ps p_e_gss) ps nextP2 in
    List.fold_left (fun acc_ps p_e_gss -> grow' ext1 p acc_ps p_e_gss) ps' nextP1
  in
  grow [] ([], [], orig_gss)


let contained_in p1 p2 = 
  let rec loop rp1 rp2 =
    rp1 = rp2 
  || (is_meta rp2)
  || (match view rp1, view rp2 with
    | C(ty1, ts1), C(ty2, ts2) ->
        ty1 = ty2 
	  && List.length ts1 = List.length ts2
          && List.for_all2 loop ts1 ts2
    | _ -> false
     ) in
  p1 = p2
|| match view p1, view p2 with
  | C("CM",[rp1]), C("CM",[rp2]) -> loop rp1 rp2 && gsize rp1 < gsize rp2
  | _, _ when p1 = ddd || p2 = ddd -> false
  | _ -> false
	(* 
	   begin
	   print_newline();
	   print_endline (Diff.verbose_string_of_gtree p1);
	   print_endline (Diff.verbose_string_of_gtree p2);
	   raise (Impossible 1000)
	   end
	 *)


exception True_found

let contained_subseq seq1 seq2 =
  let rec loop seq1 seq2 =
    match seq1, seq2 with
    | [], _ -> raise True_found
    | (x::xs), (y::ys) ->
        if contained_in x y
        then loop xs ys || loop seq1 ys
        else loop seq1 ys
    | _ -> false in
  try loop seq1 seq2 
  with True_found -> true


let find_seq_patterns_newest 
    singleton_patterns
    valid = 
  if not(!flow_support = 0)
  then begin
    print_endline ("[Main] setting new threshold : " 
		   ^ string_of_int !flow_support);
    threshold := !flow_support;
    Diff.no_occurs := !threshold;
  end;

  let grow_counter = ref 0 in
  let grow_total = List.length singleton_patterns in
  meta_counter := 0;
  let sub_pat semp1 semp2 = contained_subseq semp1 semp2 in
  let (++) pat pats = pat :: pats in
  let (@@@) sem_pat node_pat =  sem_pat @ (ddd :: [node_pat]) (* +> renumber_metas_pattern *) in
  let (<<=) sem_pat patterns =
    patterns +> List.exists
      (function sem_pat' ->
        sub_pat sem_pat sem_pat'
      ) in
  let rec grow acc cur =
    v_print_endline ".";
    let next = singleton_patterns +> List.fold_left
	(fun acc_next p -> 
          if List.mem p cur
          then acc_next
          else 
            let new_cur = cur @@@ p in
	    v_print_endline "?";
	    v_print_endline ("[Main] testing validity of\n" ^ string_of_pattern new_cur);
            if valid new_cur 
            then (v_print_endline "[Main] OK"; new_cur :: acc_next)
            else 
	      begin
		v_print_endline "!";
                v_print_endline "[Main] invalid";
		if !Jconfig.verbose then
		  begin 
		    List.iter (function t -> 
		      print_string (Diff.string_of_gtree' t);
		      print_string " "
			      ) new_cur;
		    print_newline ();
		  end;
                acc_next
	      end
	) [] in 
    if next = []
    then begin
      v_print_endline "empty";
      if !print_adding
      then begin
	print_endline "[Main] adding pattern:";
	string_of_pattern cur +> print_endline;
      end;
      cur ++ acc
    end
    else next +> List.fold_left
        (fun acc new_cur ->
          if new_cur <<= acc
          then acc
          else grow acc new_cur
        ) acc 
  in
  singleton_patterns 
    +> List.fold_left (fun acc p -> 
      begin
	Jconfig.counter_tick !grow_counter grow_total;
	grow_counter := !grow_counter + 1;
	grow acc [p]
      end) []

let unique_subterms sub_pat is_frequent_sp orig_gss get_pa  =
  print_endline "[Main] growing patterns from functions: ";
  orig_gss +> List.iter (function [f] -> begin
    print_string "\t";
    f +> Diff.get_fun_name_gflow +> print_endline;
  end
    | _ -> raise (Diff.Fail "impossible match! in find_seq_patterns")
			);
  reset_meta();
  let mk_pat p = [mkC("CM",[p])] in
  let (<==) sp ps gss = ps +> List.exists (function sp' -> 
    sub_pat gss sp sp'
      && embedded_pattern sp sp'

      (*
	if sub_pat gss sp sp' 
	then 
	(print_endline "sub-pattern found :";
	print_patterns [sp];
	print_endline "is less than :";
	print_patterns [sp'];
	true)
	else
	false
       *)
					  ) in
  (*   let (||-) gss sp = is_frequent_sp gss sp in *)
  let (+++) x xs = 
    if List.mem x xs then xs else (
    if !print_adding then (
      print_endline "[Main] adding pattern ";
      print_endline (string_of_pattern x);
     );
    (*
      if !filter_patterns
      then filter_shorter_sub gss sub_pat (x :: xs)
      else x :: xs
     *)
    x :: xs
   ) in
  let (++) ps p = p +++ ps
  in
  let valid p' =
    let rec loop p =
      match p with 
      | [] -> true
      | p :: seq when 
	  loop seq 
	    && is_match p -> 
	      not(
	      List.exists (function p' -> 
		equal_pattern_term p p') seq
	     )
		&& (match get_metas_single p with
		| [] -> true
		| p_metas -> 
		    (match get_metas_pattern seq with
		    | [] -> true
		    | seq_metas -> not(intersect_lists p_metas seq_metas = []))
		   ) 
      | skip :: seq when skip == ddd -> loop seq
      | _ -> false
    in
    match p' with
    | skip :: _ when skip == ddd -> false
    | _ -> loop p' in
  let get_next abs_P_env ext p gss =
    if p = [] 
    then List.rev_map (function (p,e) -> (p,e,gss)) abs_P_env
    else
      begin
        v_print_string "[Main] get_next ... ";
      	let res = abs_P_env 
            +> List.fold_left 
            (fun acc_abs_P_env (pat, env) -> 
              
	      let gss' = gss +> List.filter 
		  (function 
              	    | [f] -> f |- (mk_pat pat) && f |- (ext p pat)
              	    | _ -> raise (Impossible 117)) in
      	      if List.length gss' < !threshold 
      	      then begin
            	if !Jconfig.print_abs
            	then begin
            	  print_string "[Main] not including pattern with threshold: ";
            	  gss' +> List.length +> string_of_int +> print_endline;
            	  print_endline "[Main] env: ";
            	  env +> List.iter (function (m, t) -> 
		    print_endline (m ^ " ⇾ " ^
				   Diff.string_of_gtree' t);
				   );
                  print_patterns gss' [(ext p pat)];
		end;
		acc_abs_P_env
	      end
	      else (pat,env, gss') :: acc_abs_P_env
	    ) [] in
	v_print_endline "done";
	res
      end 
  in
  (* ext1 = p1 p2  -- p2 is immediate successor *)
  let ext1 p1 p2 = 
    if p1 = [] 
    then [mkC("CM",[p2])] 
    else p1 @ [mkC("CM", [p2])] in
  (* ext2 = p1 ... p2 -- p2 is all-paths successor *)
  let ext2 p1 p2 = 
    if p1 = [] 
    then [mkC("CM",[p2])] 
    else p1 @ (ddd :: [mkC("CM", [p2])]) in
  let rec grow' ext p ps (p', env', gss) =
    (* flush_string "."; *)
    let ext_p = ext p p' in
    let pp' = ext_p (* renumber_metas_pattern ext_p *) in
    if !Jconfig.verbose then ( 
      print_string ("[Main] testing : " ^ 
		    List.map Diff.string_of_gtree' pp'
		      +> String.concat " ");
     );
    if
      valid pp'
        && (v_print " valid "; is_frequent_sp gss pp')
        && (v_print "is_freq "; 
	    if !prune then not((pp' <== ps) gss) else true)
    then (
      v_print_endline "not_subseq";
      let ps' = ps ++ pp' in
      let last_p =  pp' +> List.rev +> List.hd in
      if Diff.matches_exit last_p
      then
	(* if the last pattern matches an exit-node, there is no
	   need to grow the pattern any more *)
	ps'
      else
	grow ps' (ext_p, env', gss)
     )
    else (
      v_print_endline "";
      ps)
  and grow ps (p, env, gss) =
    v_print_string "[Main] getting common cterms after pattern: ";
    v_print_endline (string_of_pattern p);
    let abs_P_env = 
      get_pa p (* env *)
	(*      
		+> sort_pa_env gss
		+> List.filter 
		(function (pat,env) ->
		p = [] 
		|| gss
		+> for_some !threshold
		(function flows ->
		flows
		+> List.exists
		(function f ->
		f |- mk_pat pat
		)
		)
		)
	 *)
    in
    v_print_endline ("done (" ^ string_of_int (List.length abs_P_env) ^ ")");
    let nextP2 = get_next abs_P_env ext2 p gss in
    (* there is no need to look for matches of "p...p'" in case
       there were no matches of "p p'" because 
       |- p p' => |- p...p'

       thus, if we can determine that |- p...p' is not the case
       then we know that |- p p' can also NOT be the case 
     *)
    let abs_P_env' = abs_P_env
	(*
	  +> List.filter
	  (fun (pat, env) -> 
	  nextP2 +> List.exists 
	  (function (p'', env', gss') -> 
	  if Diff.node_pat_eq unique_subterms (pat, env) (p'', env')
	  then (
	  (* print_endline "pat eq:";
	     pat +> Diff.string_of_gtree' +> print_endline;
	     p'' +> Diff.string_of_gtree' +> print_endline;
	   *)
	  true
	  )
	  else
	  false
	  )
	  ) 
	 *) 
    in
    let nextP1 = get_next abs_P_env' ext1 p gss in
    v_print_endline ("[Main] from pattern :\n" ^ string_of_pattern p);
    v_print_endline ("[Main] potential new patterns : " ^ string_of_int (
							  List.length nextP1 + List.length nextP2));
    v_print_newline ();
    let ps' = 
      List.fold_left (fun acc_ps p_e_gss -> grow' ext2 p acc_ps p_e_gss) ps nextP2 in
    List.fold_left (fun acc_ps p_e_gss -> grow' ext1 p acc_ps p_e_gss) ps' nextP1
  in
  grow [] ([], [], orig_gss)


let patterns_of_graph is_frequent_sp common_np g =
  if !Jconfig.verbose then print_endline ("[Main] considering graph with [" ^ 
					  string_of_int (List.length (concrete_of_graph g)) ^ 
					  "] cnodes");
  (*
    let pa = concrete_of_graph g in
   *)
  let ps = find_seq_patterns is_frequent_sp common_np g in
  if !Jconfig.verbose
  then (
    print_endline "[Main] found patterns:";    
    print_patterns [] ps);
  ps


(* append two lists without duplicates *)
let (@@) l1 l2 = List.fold_left (fun acc_l e -> e +++ acc_l) (List.rev l1) l2

(* given a list of patterns, find the sublist of patterns that match somewhere
 * in the graph 
 *)
let filter_common_np_graph common_np g =
  common_np +> List.filter (function p -> exists_cont_match g p)

(* find all patterns p in gss such that p occurs in threshold number
   of flows
 *)


let rm_dups_pred eq_f ls = Diff.rm_dups_pred eq_f ls 

(* get_common_node_patterns : 
   (flow list list) -> env ->
   (term list * env) list
 *)
let get_common_node_patterns gss env =
  v_print_endline "[Main] finding common cterms";
  let concrete_terms = 
    gss 
      +> List.rev_map 
      (function flows ->
	flows 
	  +> List.rev_map 
	  (function f -> 
	    concrete_of_graph f 
	      +> List.rev_map get_nested_subterms
	      +> tail_flatten
	  )
	  +> tail_flatten
	  +> rm_dups
      )
  in 
  v_print_string ("[Main] abstracting cterms (ct = " ^
		  string_of_int (List.length concrete_terms) ^")") ;
  let (|-) g sp = List.exists (cont_match g sp) (nodes_of_graph g) in
  let (!-) sp = gss +> for_some !threshold (function fs -> 
    fs +> List.exists (function f -> f |- sp)
					   ) in     
  let mk_pat p = [mkC("CM",[p])] in
  let is_common sp = !- (mk_pat sp) in
  let abs_P_env = concrete_terms
      +> List.rev_map (function cts -> 
	cts 
	  +> List.rev_map (function gt ->
	    let (ps,env) = abstract_term !depth env gt in
	    List.filter is_common ps, env
			  )
		      ) +> tail_flatten
      +> List.filter (function (ps, env) -> not(ps = []))
  in
  v_print_endline " done";
  v_print_endline ("[Main] common abstract terms : " ^ string_of_int (List.length abs_P_env));
  if !Jconfig.verbose then 
    abs_P_env +> List.iter (function (gts,env) -> 
      gts +> List.iter (function gt -> print_endline (Diff.string_of_gtree' gt)));
  abs_P_env


let rec infer map ps ts = 
  match ps, ts with
  | [], [] -> map
  | (skip :: ps), ts when skip = ddd -> 
      infer map ps ts
  | (p::ps), (t :: ts) -> 
      let sigma = Diff.match_term (extract_pat p) t in
      let map' = List.fold_left
	  (fun map_acc (x, term) ->
	    (try
	      let xs = List.assoc term map_acc in
	      (term, x :: xs) :: (List.remove_assoc term map_acc)
	    with Not_found -> (term, [x]) :: map_acc
	    )
	  ) map sigma in
      infer map' ps ts
  | _ -> raise (Diff.Fail "infer impossible error?")
	
let infer_all spattern occ = 
  occ 
    +> List.fold_left (
  fun map ts -> infer map spattern ts
 ) []

let infer_strongest spattern occ = 
  infer_all spattern occ
    +> List.fold_left (
  fun rb (t, xs) ->
    match xs with
    | []
    | [_] -> rb
    | _ -> xs :: rb
 ) []

let unify sigma1 sigma2 = 
  if sigma1 = []
  then sigma2
  else
    sigma1 
      +> List.fold_left (
    fun acc_rb s1 ->
      sigma2
	+> List.fold_left (
      fun acc_rb s2 ->
	let s' = intersect_lists s1 s2 in
	match s' with
	| []
	| [_] -> acc_rb
	| _ -> s' :: acc_rb
     ) acc_rb
   ) []

let infer_bindings spattern graphs =
  let occ = 
    graphs
      +> List.filter (function g -> 
	nodes_of_graph2 g
	  +> List.exists (cont_match g spattern))
      +> List.rev_map 
      (fun g -> 
	get_pattern_traces_real g spattern
	  +> List.rev_map
	  (function ilistlist ->
            ilistlist 
              +> List.rev_map
              (function ilist ->
		List.map (function n -> g#nodes#find n) ilist
              ))) 
      +> tail_flatten in
  List.fold_left (fun sigma occ_i ->
    infer_strongest spattern occ_i
      +> unify sigma 
		 ) [] occ

let instantiate sigma p = 
  let rec loop p = match view p with
  | A("meta", x) -> 
      (try 
	let xs = List.find (function xs -> List.mem x xs) sigma in
	mkA("meta", List.hd xs)
      with Not_found -> p)
  | C(ty,ps) ->
      mkC(ty, List.map loop ps)
  | _ -> p
  in
  loop p
    
let construct_pattern sigma pattern = 
  List.map (function p ->
    instantiate sigma p
	   ) pattern


let infer_meta_variables graphs sem_patterns =
  let meta_count = ref 0 in
  let meta_total = List.length sem_patterns in
  print_string "[Main] infering strongest meta-var bindings ";
  sem_patterns 
    +> List.fold_left (
  fun acc_patterns spattern ->
    ANSITerminal.save_cursor ();
    ANSITerminal.print_string 
      [ANSITerminal.on_default] (
    !meta_count +> string_of_int ^"/"^ meta_total +> string_of_int
   );
    ANSITerminal.restore_cursor();
    flush stdout;
    meta_count := !meta_count + 1;
    
    let sigma = infer_bindings spattern graphs in
    let new_pattern = (construct_pattern sigma spattern) in
    if for_some !threshold (fun g -> exists_cont_match g new_pattern) graphs
    then new_pattern :: acc_patterns
    else acc_patterns
 ) []
    
    
let get_fun_name_gflow f =
  let head_node = 
    f#nodes#tolist 
      +> List.find (function (i,n) -> match view n with
      | C("head:def", [{Hashcons.node=C("def",_)}]) -> true
      | _ -> false) in
  match view (snd head_node) with
  | C("head:def",[{Hashcons.node=C("def",name::_)}]) -> 
      (match view name with
      | A("fname",name_str) -> name_str
      | _ -> raise (Diff.Fail "impossible match get_fun_name_gflow")
      )
  | _ -> raise (Diff.Fail "get_fun_name?")
	

(* we have a focus_fun iff !focus_function != "" *)
let haveFocusFun () = String.compare !focus_function "" != 0

let sameName other_fun =
  if String.compare !focus_function other_fun = 0
  then begin
    v_print_endline ("ff: " ^ !focus_function ^ " == " ^ other_fun);
    true
  end
  else begin
    v_print_endline ("ff: " ^ !focus_function ^ " != " ^ other_fun);
    false
  end    

let get_focus_function gss =
  List.hd (
  List.find (function 
    | [g] -> get_fun_name_gflow g = !focus_function
    | _ -> raise (Impossible 120)
	    ) gss
 )

let common_patterns_graphs gss =
  let matches_focus_function = ref false in
  (* detect whether a threshold was given *)
  if !threshold = 0
  then threshold := List.length gss;
  print_endline ("[Main] threshold is " 
                 ^ string_of_int !threshold ^ " of " 
                 ^ gss +> List.length +> string_of_int);
  Diff.no_occurs := !threshold;
  print_endline "[Main] finding lists of subterms";
  let subterms_lists =
    gss
      +> List.rev_map (function 
        | [f] -> concrete_of_graph f +> List.filter 
              (function n -> not(Diff.is_head_node n) && Diff.non_phony n)
        | _ -> raise (Impossible 1))
  in
  print_endline "[Main] finding list of unique subterms";
  let unique_subterms = subterms_lists 
      +> tail_flatten 
      +> Diff.rm_dub in
  let (|-) g sp = 
    (* pre-test whether the nodes of the pattern are at all in the graph *)
    let nodes2 = nodes_of_graph2 g in
    sp +> List.for_all 
      (function p_gt ->
	p_gt = ddd || nodes2 +> List.exists (function i -> 
	  Diff.can_match (extract_pat p_gt) (g#nodes#find i))
      ) &&
    (List.exists (function i ->
      if cont_match g sp i
      then 
        (* the pattern matched the graph, also check if was the focus_fun *)
	let g_name = get_fun_name_gflow g
	in begin
          if(haveFocusFun () && sameName g_name)
          then matches_focus_function := true;
          true
        end
      else ((* print_endline "NONSAT"; *) false)) 
       nodes2) in
  (* define the function ||- to check whether a pattern matches a set of sets of
   * functions
   *)
  let (||-) gss sp = 
    matches_focus_function := false;
    (* if we have a focus_function, first check if the pattern matches the
     * focus_function
     *)
    (not(haveFocusFun()) ||
    get_focus_function gss |- sp
    )
      &&
    (* check whether the pattern matches at least threshold graphs *)
    gss +> for_some !threshold 
      (function fs -> fs +> List.exists 
	  (function f -> 
	    (*flush_string ("." ^ Diff.get_fun_name_gflow f );*)
	    (*"no. nodes: " +> print_endline;*)
	    (*f +> nodes_of_graph2 +> List.length +> string_of_int +> print_endline;*)
	    let r = f |- sp in
            (*flush_string ";";*)
	    r)) 
      (* also: if ff != "" then we must have matched the ff *)
      && ((not (haveFocusFun ())) || !matches_focus_function) in
  let rec check_no_duplicates ls = match ls with
  | [] -> ((* print_endline "no dups"; *) true)
  | x :: xs when x == ddd -> check_no_duplicates xs
  | x :: xs -> not(List.mem x xs) && check_no_duplicates xs in
  (* function that defines when a pattern is frequent wrt. a set of graphs *)
  let is_frequent_sp_some gss sp = 
    (* the pattern must not contain duplicate single-line patterns *)
    check_no_duplicates sp 
      (* the pattern must match threshold graphs at least *)
      && gss ||- sp in
  let is_subpattern gss sp1 sp2 = subpattern_some gss sp1 sp2 in
  print_endline "[Main] finding list of common patterns";
  let node_patterns_pool_initial = Diff.merge_abstract_terms subterms_lists unique_subterms in
  let node_patterns_pool = 
    (* filter out the node-patterns do not match in the focus function (if
     * one is selected) *)
    if haveFocusFun ()
    then begin
      print_endline ("[Main] refining node_patterns_pool according to focus function");
      let subterms_focus_fun =
        try 
          let [focus_fun] = 
            List.find (function 
              | [g] -> get_fun_name_gflow g = !focus_function
              | _ -> raise (Impossible 120)
                      ) gss
          in
          concrete_of_graph focus_fun 
            +> List.filter (function n -> not(Diff.is_head_node n) && Diff.non_phony n)
        with 
        | Not_found -> []
        | Match_failure _ -> raise (Impossible 119)
      in
      (* get subterms from focus_function *)
      List.filter 
        (function npat -> List.exists 
            (function term -> Diff.can_match npat term)
            subterms_focus_fun
        )
        node_patterns_pool_initial
    end
    else node_patterns_pool_initial 
  in
  print_string "[Main] finding semantic patterns ";
  find_seq_patterns_newest (* simulates _ wildcards with all fresh metavariables *)
    (* singleton_patterns: all node patterns with 'fresh' metas' *) 
    (node_patterns_pool 
       +> List.fold_left 
       (fun acc p ->
	 if not(infeasible p) && Diff.non_phony p && not(Diff.control_true = p) && not(Diff.is_head_node p)
	 then mkC("CM",[p]) :: acc
	 else acc
       ) []
       +> renumber_fresh_metas_pattern)
    (* valid: check that sempat is frequent *)
    (is_frequent_sp_some gss)
    +> infer_meta_variables (tail_flatten gss)
    +> function ps -> begin
      print_newline ();
      print_endline "[Main] now removing duplicates";
      ps
    end
	+> rm_dups
	+> (function pss -> 
	  if !filter_patterns
	  then begin
	    print_endline "[Main] finding largest patterns";
	    filter_shorter_sub gss (is_subpattern gss) pss 
	  end
	  else pss)
	

let get_arcs g i =
  (g#successors i)#tolist

let equal_arcs arcs1 arcs2 =
  is_subset_list (=) arcs1 arcs2 &&
  is_subset_list (=) arcs2 arcs1

(* equality of flows *)
let equal_flows f1 f2 =
  let eq_f (i1,n1) (i2,n2) = Diff.edit_cost n1 n2 = 0 in
  let ns1 = f1#nodes#tolist in
  let ns2 = f2#nodes#tolist in
  (* all nodes must have same index and value *)
  is_subset_list eq_f ns1 ns2 &&
  is_subset_list eq_f ns2 ns1 
    (* arcs should also be equal, we ignore predecessors  *)
    && 
  ns1 +> List.for_all (function (i,n) -> equal_arcs (get_arcs f1 i) (get_arcs f2 i)
		      ) &&
  ns2 +> List.for_all (function (i,n) -> equal_arcs (get_arcs f1 i) (get_arcs f2 i)
		      ) 


(* given a set of patterns and a set of terms that have been identified as
 * belonging to a change, we wish to find the patterns that match any of the
 * terms
 *)
let get_change_matches_terms spatterns terms =
  v_print_endline "[Main] filtering patterns that are related to changed terms";
  let changes = terms 
      +> List.rev_map (Diff.get_change_matches spatterns) in
  let tmp = tail_flatten changes in
  let tmp1 = rm_dups tmp in
  tmp1


(* filter_changed uses the "flow-changes" information to extract a list of terms
 * that it thinks have changed or are related to a change to filter out patterns
 * match at least one of those terms
 *)
let filter_changed (* gss *) gpats = 
  if !only_changes 
  then (
    print_endline "[Main] looking for changed patterns";
    v_print_endline "[Main] the following are the terms that have been detected as changed";
    let c_terms = !Diff.flow_changes +> 
      List.fold_left (fun acc_changed_terms diff -> 
	diff 
	  +> Diff.get_marked_seq 
	  +> List.fold_left (fun acc_changed_terms di ->
	    match di with
	    | Difftype.ID t 
	    | Difftype.RM t -> t +++ acc_changed_terms
	    | _ -> raise (Impossible 2)
			    ) acc_changed_terms
		     ) [] in
    c_terms +> List.iter (fun ct -> v_print_endline (Diff.string_of_gtree' ct));
    get_change_matches_terms gpats c_terms
      (*
	gpats +> List.filter (function sp -> 
	gss +> List.exists (function flows ->
        flows +> List.for_all 
        (function f -> not(f |- sp))
	))
       *)
   )
  else gpats


(* Look through all relevant nodes and find out which one have
   changed; a node have changed if it does not occur in the RHS graph
   [or if it's succ/pred have changed -- not implemented yet]
   let find_changed_nodes g1 g2 =
   let nodes1 = concrete_of_graph g1 in
   let nodes2 = concrete_of_graph g2 in
   nodes1 +> List.filter (function n -> not(List.mem n nodes2))
 *)


let lhs_flows_of_term_pairs term_pairs =
  print_endline "[Main] getting lhs flows";
  term_pairs 
    +> List.fold_left 
    (fun  acc ((gt,flow), (gt',flow')) -> 
      if !only_changes 
      then
	let f_name = 
	  try get_fun_name_gflow flow 
	  with Not_found ->
	    raise (Diff.Fail ("no function found in LHS")) 
	in 
	(* if not(equal_flows flow flow')
	 *)
	let edit_cost = Diff.edit_cost gt gt' in
	if not(edit_cost = 0)
	then (
	  print_endline ("[Main] function " ^ f_name ^ " changed (" ^
			 string_of_int edit_cost
			 ^ ")" );
	  [flow] :: acc
	 )
	else
	  acc
      else
	[flow] :: acc
    ) []




(* at this point we have a set/list of spatterns that we know to match
   on some term that is believed to have been involved in a change; the
   function is_freq determines whether a node-term is frequent in the RHS
   graphs *)
let rec get_context_point chunk =
  match chunk with
  | [] -> raise (Diff.Fail "no context point?")
  | Difftype.ADD _ :: chunk -> get_context_point chunk
  | c :: _ -> c



let construct_spatches_new chunks safe_part_loc patterns =
  let pending_or_add tp = match tp with
  | Difftype.PENDING_RM _ 
  | Difftype.PENDING_ID _ 
  | Difftype.ADD _ -> true
  | _ -> false in

  let rec get_ctx_trans chunk = match chunk with
  | [] -> raise (Impossible 190)
  | (Difftype.ID p | Difftype.RM p) as ch :: _  -> ch
  | _ :: chunk -> get_ctx_trans chunk in

  let try_match tp ctx =
    match tp, ctx with
    | (Difftype.ID p | Difftype.RM p) , (Difftype.ID t | Difftype.RM t) -> 
	(try Some (Diff.match_term (extract_pat p) t) with _ -> None)
    | _ -> begin
	print_endline "[Main] try_match: tp = ";
	tp +> Diff.string_of_diff +> print_endline;
	raise (Impossible 4)  
    end in

  let rev_sub_diff env dt = match dt with
  | Difftype.ADD p -> Difftype.ADD (Diff.rev_sub env p)
  | Difftype.ID p -> Difftype.ID (Diff.rev_sub env p)
  | Difftype.RM p -> Difftype.ID (Diff.rev_sub env p)
  | _ -> raise (Impossible 90) in

  let rec get_before chunk =
    match chunk with
    | [] -> []
    | (Difftype.ID _ | Difftype.RM _ | Difftype.PENDING_ID _ | Difftype.PENDING_RM _) :: _ -> []
    | a :: chunk -> a :: get_before chunk in
  
  let rec get_after chunk =
    match chunk with
    | [] -> []
    | Difftype.ADD _ :: chunk -> get_after chunk
    | (Difftype.ID _ | Difftype.RM _ | Difftype.PENDING_ID _ | Difftype.PENDING_RM _) :: chunk ->  chunk
    | _ -> raise (Impossible 102) in


  let apply_chunk env chunk i p = 
    let rec apply_chunk_loop i p = match p with
    | [] -> raise (Impossible 113)
    | tp :: p_rest ->
	if i = 0
	then
	  let before = chunk 
	      +> get_before
	      +> List.map (rev_sub_diff env) in
	  let after  = chunk
	      +> get_after
	      +> List.map (rev_sub_diff env) in
	  let tp = match List.nth p i with
	  | Difftype.RM t
	  | Difftype.ID t -> t
	  | _ -> raise (Impossible 90) in
	  let ctx    = match get_ctx_trans chunk with
	  | Difftype.RM _ -> Difftype.PENDING_RM tp
	  | Difftype.ID _ -> Difftype.PENDING_ID tp
	  | _ -> raise (Impossible 109) in
	  let insert_pending = before @ ctx :: after in
	  insert_pending @ p_rest
	else 
	  tp :: apply_chunk_loop (i-1) p_rest in
    apply_chunk_loop i p 
  in

  let rec handle_p acc orig_p =
    let rec loop_p (wq, out) (i, p) = 

      match p with
      | [] -> (wq, out)
      | tp :: p_rest ->
	  if pending_or_add tp
	      (* we skip term patterns which have already been paired
		 with a chunk *)
	  then loop_p (wq, out) (i+1, p_rest)
	  else begin
	    let new_wq, new_out = chunks +> List.fold_left 
		(fun (wq, out) ch ->

		  match try_match tp (get_ctx_trans ch) with
		  | None -> (wq, out)
		  | Some env' ->

		      let spa = apply_chunk env' ch i orig_p in

		      if (* safe_part_loc spa && *) 
			not(List.mem spa out)
		      then begin

			(spa +++ wq,
			 (spa 
			    +> List.map 
			    (function p -> match p with
			    | Difftype.PENDING_RM tp -> Difftype.RM tp
			    | Difftype.PENDING_ID tp -> Difftype.ID tp
			    | _ -> p
			    )) +++ out)
		      end
		      else begin

			(wq, out)
		      end
		) (wq, out) 
	    in 
	    loop_p (new_wq, new_out) (i+1, p_rest)
	  end
    in
    loop_p acc (0, orig_p)

  and construct_loop (wq, out) =
    match wq with
    | [] -> out
    | p :: ps ->
	p
	  +> handle_p (ps, out)
	  +> construct_loop in 
  let rec init_pattern p = match p with
  | [] -> []
  | p :: p_tail -> Difftype.ID p :: init_pattern p_tail
  in
  construct_loop (List.rev_map init_pattern patterns, [])

let get_rhs_flows term_pairs =
  term_pairs
    +> List.rev_map (function (gtf,gtf') -> (gtf',gtf))
    +> lhs_flows_of_term_pairs
    (*
      term_pairs +>
      List.rev_map (fun ((gt,flows), (gt',flows')) -> flows'
      )
     *)

(* this function returns the subterm of the given term
   corresponding to the function definition "sname" *)
let get_fun_in_term sname term = 
  let rec loop ts = match ts with
  | [] -> None
  | t :: ts -> match find t with
    | Some f -> Some f
    | None -> loop ts
  and find t = match view t with
  | C("def", ({Hashcons.node=A("fname",name)}  :: _)) when name = sname -> Some t
  | C(_,ts) -> loop ts
  | _ -> None
  in match find term with
  | None -> raise (Diff.Fail ("function " ^ sname  ^ " not found"))
  | Some f -> f

let is_exit_node t = match view t with
| C("head:dowhiletail", _)
| A("head:seqend",_) -> true
| _ -> false

(* this 'get_path' function takes a CFG for a function def and a nodei
   within that flow and returns a path from the root to the node (both
   nodes included); a path is a list of node-indices excluding "phony"
   nodes and "exit-nodes"*)

let get_path g n = 
  let path = ref [] in
  let f xi path' = 
    if xi = n then path := xi :: path' in
  Ograph_extended.dfs_iter_with_path 0 f g;
  !path 
    +> List.filter 
    (function xi -> 
      let t = g#nodes#find xi in
      Diff.non_phony t && not(is_exit_node t)
    )
    +> List.rev

type ('a, 'b) annotated = NOAN of 'a | ANNO of 'a * 'b
let empty_annotation = []

let add_annotation ann a = a :: ann
let add_annotation_iop iop a = match iop with
| Difftype.ID (p, ann) -> Difftype.ID(p, add_annotation ann a)
| Difftype.RM (p, ann) -> Difftype.RM(p, add_annotation ann a)
| Difftype.ADD(p, ann) -> Difftype.ADD(p, add_annotation ann a)
| _ -> raise (Impossible 7)

let annotate_spatch spatch trace =
  let map2 skipf f ls1 ls2 = 
    let rec loop ls1 ls2 = match ls1, ls2 with
    | [], [] -> []
    | e1 :: ls1', _ when skipf e1 -> e1 :: loop ls1' ls2
    | e1 :: ls1, e2 :: ls2 -> f e1 e2 :: loop ls1 ls2 
    | _, _ -> raise (Invalid_argument "annotate_spatch")
    in
    loop ls1 ls2 in
  let skip_add p = match p with
    Difftype.ADD _ -> true | _ -> false in
  let anno_seq sp node_seq = 
    try 
      map2 skip_add add_annotation_iop sp node_seq 
    with Invalid_argument e -> 
      print_endline ("annotate_seq sp.len: " ^ 
		     List.length sp +> string_of_int ^ " node_seq.len " ^
		     List.length node_seq +> string_of_int);
      sp +> List.iter (function iop -> (match iop with
      | Difftype.ID (p, ann) 
      | Difftype.RM (p, ann)
      | Difftype.ADD(p, ann) -> Diff.string_of_gtree' p +> print_endline
      | _ -> raise (Impossible 8))
		      );
      raise (Invalid_argument e)
  in
  List.fold_left anno_seq spatch trace

exception LocateSubterm 
exception Next of int list 
exception Break of int list

let at_breaking_handler = ref false


let rec is_looping t = match view t with
| C("for", _)
| C("dowhile", _)
| C("while", _)
| C("switch", _) -> true
| C("stmt", [s]) -> is_looping s
| _ -> false

let corresponds st t next_node_val path =
  let same_path s_st_f = match s_st_f with
  | None -> None
  | Some (st, f) -> Some (st,f,path) 
  in
  match view st with
  | C("def",[rname;rtype;body]) -> 
      (match view t with
      | C("head:def", [def]) -> 
	  (match view def with 
	  | C("def",[hname;htype;_]) when rname = hname && rtype = htype
	    -> Some ([body],
		     function 
		       | [newbody] -> 
			   mkC("def",[rname;rtype;newbody])
		       | _ -> raise (Impossible 9)
		    ) +> same_path
	  | _ -> raise (Diff.Fail "def-fail"))
      | _ -> None
      )

  | C("stmt", [st]) ->
      let s_func st = mkC("stmt", [st]) in
      (match view st, view t with
      | C("macroit",      [{Hashcons.node=C(t_name, [
					    {Hashcons.node=C("macroargs", args)} as margs
					      ;st
					  ])}]), 
	C("head:macroit", [{Hashcons.node=C(g_name, args_node)}]) 
	when t_name = g_name && args = args_node ->
	  at_breaking_handler := true;
	  (match next_node_val with
	  | None -> raise (Diff.Fail "no next control node val: InLoop could have been expected")
	  | Some control_node ->
	      if control_node = Diff.control_inloop
	      then
		Some([st], 
		     (function 
		       | [st'] -> 
			   mkC("macroit",[mkC(t_name, [margs;st'])]) +> s_func
		       | _ -> raise (Impossible 10))
		       ,
		     List.tl path
		    )
	      else raise (Next path)
	  )
      | C("comp{}", sts), A("head:seqstart", _) ->
	  Some (sts, function sts' ->
	    mkC("comp{}", sts') +> s_func) +> same_path
      | A("comp{}", "NOP"), A("head:seqstart", _) -> 
	  Some([], function ts -> s_func st) +> same_path
      | C("if",[b;t;f]), C("head:if",[c]) when b = c -> 
	  (match next_node_val with
	  | None -> raise (Diff.Fail "no next control node val!")
	  | Some control_node ->
	      if control_node = Diff.control_else
	      then (* select false branch and consume control_node from path *)
		Some([f],(function 
		  | [f] -> mkC("if", [b;t;f]) +> s_func
		  | _ -> raise (Impossible 11)), List.tl path)
	      else (* select true branch and consume control_node node from path *)
		if control_node = Diff.control_true
		then
		  Some([t],(function 
		    | [t] -> mkC("if", [b;t;f]) +> s_func
		    | _ -> raise (Impossible 12)), List.tl path)
		else begin
		  (* we were not supposed to enter the if-statement but skip it *)
		  raise (Next path)
		end
	  )
      | C("switch",[e;s]), C("head:switch", [e']) when e = e' ->
	  begin
	    (* setup break handler *)
	    at_breaking_handler := true;
	    Some ([s], function s' ->
	      mkC("switch", e :: s') +> s_func) +> same_path
	  end
      | C("while",[e;s]), C("head:while", _) ->
	  at_breaking_handler := true;
	  (match next_node_val with
	  | None -> raise (Diff.Fail "no next control node in while")
	  | Some control_node ->
	      if control_node = Diff.control_inloop
	      then
		Some ([s],(function s' ->
		  mkC("while", e :: s') +> s_func),
		      List.tl path)
	      else raise (Next path)
	  )
      | C("dowhile", [s;e]), C("head:do", [e']) when e = e' 
	    (* TODO: we also need to verify the statement s
	       with the graph *) ->
		 at_breaking_handler := true;
		 Some ([s], (function s' ->
		   mkC("dowhile", s' @ [e]) +> s_func)) +> same_path
      | C("for", [e1;e2;e3;st]), C("head:for", _) ->
	  at_breaking_handler := true;
	  (match next_node_val with
	  | None -> raise (Diff.Fail "no next control node in for")
	  | Some control_node ->
	      if control_node = Diff.control_inloop
	      then 
		Some ([st], (function st' ->
		  mkC("for", e1 :: e2 ::e3 :: st') +> s_func),
		      List.tl path)
	      else raise (Next path)
	  )
      | C("case", [e;st]), C("head:case",[lab_e]) when e = lab_e ->
	  Some ([st], function st' ->
	    mkC("case", e :: st') +> s_func) +> same_path
      | C("caseRange", [e1;e2;st]), C("head:caserange", [from_e;to_e])
	when e1 = from_e && e2 = to_e ->
	  Some ([st], function st' ->
	    mkC("caseRange", e1 :: e2 :: st') +> s_func) +> same_path
      | C("default", [st]), A("head:default", _) ->
	  Some ([st], function 
	    | [st'] ->
		mkC("default", [st']) +> s_func
	    | _ -> raise (Impossible 13)) +> same_path
      | C("caseRange",[e1;e2;st]), A("head:case", _) -> 
	  Some ([st], function st' ->
	    mkC("caseRange", e1 :: e2 :: st') +> s_func) +> same_path
      | C("labeled", [{Hashcons.node=A("lname", s_lab)} as l; st]), 
	  A("head:label", lab) -> 
	    Some ([st], function 
	      | [st] -> mkC("labeled", [l; st]) +> s_func
	      | _ -> raise (Impossible 14)) 
	      +> same_path
      | _ -> None
      )
  | _ -> None
	
let rec ( *>) (t_list : gtree list) func def_arg =
  match t_list with
  | [] -> (* raise LocateSubterm *)
      raise (Next def_arg)
  | t :: t_list -> (try 
      let t' = func t def_arg in
      t' :: t_list
  with
    | LocateSubterm -> t :: ((t_list *> func) def_arg) 
    | Next arg -> t :: ((t_list *> func) arg) 
		   )

exception Label_not_found of string
exception Goto of string * int list

let rec iterate_lab t_list loop locate_label (lab, path) =
  let rec cont t_list = 
    match t_list with
    | [] -> 
	raise (Label_not_found lab)
    | t :: t_list -> (try 
	let t' = locate_label (lab, path) t in
	t' :: t_list
    with
      | LocateSubterm -> t :: ((t_list *> loop) path) 
      | Next new_path -> t :: ((t_list *> loop) new_path) 
      | Label_not_found _ -> t :: cont t_list
		     )
  in
  cont t_list

let rec is_break t = match view t with
| C("stmt", [t]) -> is_break t
| A("jump", "break") 
| A("jump", "continue") -> true
| _ -> false

let locate_subterm g orig_subterm orig_path f =
  at_breaking_handler := false;
  let extract_label t = 
    match view t with 
    | C("stmt", [{Hashcons.node=A("goto", lab)}]) -> Some lab
    | _ -> None
  in
  let pathht = Hashtbl.create 101 in
  let get_val n = 
    try 
      Hashtbl.find pathht n
    with Not_found ->
      let res = Diff.get_val n g 
      in
      (Hashtbl.add pathht n res; res) 
  in
  v_print_string "[Main] looking in ";
  v_print_endline (Diff.verbose_string_of_gtree orig_subterm);
  v_print_string "[Main] path ";
  v_print_endline (orig_path +> List.map string_of_int +> String.concat " ");
  if not(List.length orig_path = 0) 
  then begin
    let last = List.nth orig_path (List.length orig_path - 1) 
    in
    v_print_string "[Main] looking for:";
    v_print_endline (get_val last +> Diff.verbose_string_of_gtree);
  end;
  let is_typed e = 
    match view e with
    | C("TYPEDEXP", _) -> true
    | _ -> false in
  let rec (===) t1 t2 = 
    match view t1, view t2 with
    | C("pending", ot :: _ ), _ -> ot === t2
    | C("stmt",[s]), (C("dlist", _) | C("mdecl", _)) ->  s === t2
    | C("exp",[te;e]), C("exp", [e']) when is_typed te -> e === e'
    | C(ty1,ts1), C(ty2,ts2) when ty1 = ty2 ->
	(try 
	  List.for_all2 (===) ts1 ts2
	with Invalid_argument e -> 
          (print_endline "ts1";
	   ts1 +> List.map Diff.verbose_string_of_gtree +> List.iter print_endline;
	   print_endline "ts2";
	   ts2 +> List.map Diff.verbose_string_of_gtree +> List.iter print_endline;
	   raise (Invalid_argument e))
	)
    | _ -> t1 = t2 in
  (* this function is used to check whether we are at a context point *)
  let is_at_context node_term pending_subterm = 
    match view pending_subterm with
    | C("pending", orig_cp :: chunk_op) -> orig_cp === node_term
    | _ -> pending_subterm === node_term in
  let get_next_node_val path = 
    match path with
    | [] -> None
    | n :: _ -> Some (get_val n) in
  let rec loop subterm path =
    match path with
    | [] -> begin
        (* we should actually *NEVER* reach this point because of
         * the next pattern-match *)
	print_endline ("[Main] reached end of path at subterm: "
		       ^ subterm +> Diff.string_of_gtree');
	print_string ("Orig path: \t ");
	orig_path +> List.iter 
          (function i -> print_string (" " ^ string_of_int i););
	print_newline ();
	print_endline ("Last node value " ^ orig_path +> 
					    List.rev +> List.hd +> get_val +> 
					    Diff.string_of_gtree');  
	print_endline ("In function: " ^ g +> get_fun_name_gflow);
	raise (Diff.Fail "At end of path!")
    end
    | [n] -> 
	let node_term = get_val n 
        in
	if is_at_context node_term subterm
	then f subterm
            (* subterm/node_term -- can the subterm have more
               info than the node-term ? they should be
               identical! *)
	else 
	  begin
            (*
	      print_endline ("Node term:\t" ^ 
              node_term +> Diff.string_of_gtree');
	      print_endline ("Subterm:\t" ^ subterm +> Diff.string_of_gtree');
	      print_string ("Orig path: \t");
              orig_path +> List.iter (function i -> 
	      print_string (string_of_int i ^ " ");
	      );
	      print_newline ();
	      print_string ("Current path:\t");
	      path +> List.iter (function i -> 
	      print_string (string_of_int i ^ " ");
	      );
	      print_newline ();
	      print_endline ("In function:\t" ^
	      get_fun_name_gflow g);
             *)
            (* Should we bail out at this place or raise
               "LocateSubterm" to indicate that the search should
               continue but that we did not find the node term at
               this point?  *)
	    raise LocateSubterm
	      (* raise (Diff.Fail "unable to locate subterm") *)
	  end
    | n' :: path -> 
	let t = get_val n' 
	in
	if subterm === t
	then 
	  (match extract_label t with
	  | Some lab -> raise (Goto (lab, path))
	  | None     -> begin
	      if is_break subterm
	      then
		raise (Break path)
	      else
		raise (Next path)
	  end
	  )
	else
	  (
	   match corresponds subterm t (get_next_node_val path) path  with
	   | None -> raise LocateSubterm
	   | Some (ts, ins_f, new_path) ->
	       if !at_breaking_handler
	       then begin
		 at_breaking_handler := false;
		 try begin
		   (ts *> loop) new_path 
		     +> ins_f;
		 end
		 with Break new_path -> raise (Next new_path)
	       end
	       else
		 (ts *> loop) new_path +> ins_f
	  ) 
  and locate_label (lab, path) t =
    match view t with 
    | C("stmt", [
	{Hashcons.node=C("labeled", [
			 {Hashcons.node=A("lname",lab') }; _])}
      ]) 
      when lab = lab' -> loop t path
    | C("exp", _)
    | C("exprstmt", _)
    | C("stmtexp", _) -> raise (Label_not_found lab)
    | C(ty, ts) -> 
	(* if t is a looping construct, we need to setup a break/continue handler *)
	if is_looping t
	then 
	  try
	    let ts' = iterate_lab ts loop locate_label (lab, path)
	    in mkC(ty,ts')
	  with Break new_path -> raise (Next new_path)
	else 
	  let ts' = iterate_lab ts loop locate_label (lab, path)
	  in mkC(ty,ts')
    | _ -> raise (Label_not_found lab) 
  in
  let rec search_label (lab, path) =
    try locate_label (lab, path) orig_subterm
    with
      Goto (lab', path') -> search_label (lab', path')
  in
  if orig_path = []
  then begin
    print_endline "[Main] calling locate_subterm with empty path";
    orig_subterm
  end
  else
    try loop orig_subterm orig_path 
    with
    | Goto (lab, path) -> 
	try
	  begin
	    search_label (lab, path);
	  end
	with Break path -> begin
	  print_string ("[Main] caught break after GOTO " ^ lab  ^ " in function ");
	  g +> get_fun_name_gflow +> print_endline;
	  print_string "[Main] at path: ";
	  path +> List.map string_of_int +> String.concat " "
	    +> print_endline;
	  raise (Break path)
	end


(* this function takes a chunk and a subterm and uses the subterm to
   create a pending-chunk/term to insert instead of the subterm given;
   it is generally done by creating a new C-node with a copy of the
   old subterm for future reference and an embedding of the chunk in
   the gtree datatype
 *)
let gtree_of_ann_iop iop = match iop with
| Difftype.ID(p,_) -> mkC("=",[p])
| Difftype.RM(p,_) -> mkC("-",[p])
| Difftype.ADD(p,_)-> mkC("+",[p])
| _ -> raise (Impossible 15)

let pending_of_chunk chunk subterm = 
  let embedded_chunk = 
    chunk +> List.map gtree_of_ann_iop in 
  mkC("pending", subterm :: embedded_chunk)


(* this function takes a term with embedded pending transformation
   info and a chunk and locates the chunk in the term and inserts the
   chunk as an embedded pending transformation...  

   the chunk is annoted with the nodeS (<- plural) in which the
   context-point matched; we can then use 'locate_subterm' to find the
   subterms in pending_term that corresponds to that node;
   
   - get_context_point from chunk
   - transform the chunk into a pending transformation
   - locate the subterm in pending_term
   - if the subterm has already been subject to a pending transformation
   => check if the chunk pending-transformation is compatible with the already pending transformation
   => if it is compatible, insert it
   => else raise an error (or skip the transformation entirely?)
   - if no pending trans, just insert the chunk pending-transformation
 *)

let insert_chunk flow pending_term chunk = 
  (* all the nodes where the 'context' of the chunk matched in the CFG *)
  let ctx_point_nodes = 
    match get_context_point chunk with
    | Difftype.ID(p,is) | Difftype.RM(p,is) -> is
    | _ -> raise (Diff.Fail "insert_chunk get_context_point") in
  (* the 'f' function is responsible for checking chunk compatibility *)
  let f t = 
    match view t with
    | C("pending", _) -> t
    | _ -> pending_of_chunk chunk t in
  List.rev_map (get_path flow) ctx_point_nodes
    +> List.fold_left 
    (fun acc_t path -> 
      try locate_subterm flow pending_term path f 
      with LocateSubterm -> acc_t) 
    pending_term

let is_empty_labeled stmt = 
  match view stmt with
  | C("stmt", [
      {Hashcons.node=C("labeled", [{Hashcons.node=A("lname",lab') }])}
    ]) -> true
  | _ -> false

let inline_stmt_label s1 s2 =
  match view s1 with
  | C("stmt", [
      {Hashcons.node=C("labeled", [{Hashcons.node=A("lname",lab') }])}
    ]) -> 
      mkC("stmt", [mkC("labeled", [mkA("lname", lab'); s2])])
  | _ -> raise (Impossible 8192)


let rec fix_empty_labeled = function
  | [] -> []
  | s1 :: s2 :: rest when is_empty_labeled s1 -> inline_stmt_label s1 s2 :: fix_empty_labeled rest
  | x :: xs -> x :: fix_empty_labeled xs
 
let perform_pending pending_term = 
  let get_env orig_cp emb =
    let ctx = 
      match List.find 
          (function p -> 
            match view p with 
	    | C("=",[ctx])  
	    | C("-",[ctx]) -> true
	    | _ -> false) emb +> view 
      with
      | C("=",[p]) | C("-",[p])-> p
      | _ -> raise (Impossible 16)
    in
    try Diff.match_term (extract_pat ctx) orig_cp 
    with Diff.Nomatch -> 
      begin
	print_endline "[Main] Nomatch between:";
	Diff.string_of_gtree' orig_cp +> print_endline;
	Diff.string_of_gtree' ctx +> print_endline;
	print_endline "[Main] emb...";
	emb +> List.iter 
	  (function gt -> gt +> Diff.string_of_gtree' +> print_endline);
	raise Diff.Nomatch
      end
  in
  let unfold_embedded orig embs = 
    let env = get_env orig embs 
    in
    List.fold_right (fun emiop res_ts -> 
      match view emiop with
      | C("=", [p]) -> (orig :: res_ts) (* should be able to assert(Diff.rev_sub env p = orig *)
      | C("-", [p]) -> (res_ts) (* should be able to assert(Diff.rev_sub env p = orig *)
      | C("+", [p]) -> (let interm = Diff.sub env p 
      in interm :: res_ts)
      | _ -> raise (Impossible 17)
		    ) embs []
  in
  let rec loop t = 
    match view t with
    | C("pending", orig_cp :: embedded) -> unfold_embedded orig_cp embedded
    | C(ty, ts) -> 
        let ts' = ts +> List.rev_map loop 
	    +> List.rev
	    +> List.flatten in 
	[mkC(ty, fix_empty_labeled ts')]
    | _ -> [t] in
  match loop pending_term with
  | [t'] -> t'
  | _ -> raise (Diff.Fail "perform pending error")
	

(* this function applies a semantic patch to a term given a flow
   representing the term; the idea is to do the following

   - extract the pattern from the spatch
   - match the pattern with the flow and collect the traces

   - use the traces to annotate the spatch (notice there can be
   several annotated spatches when the pattern matches starting from
   more than one node; however, notice by the shortest-paths semantics
   of ... that the same pattern can not have overlapping matches (with
   the same environment)

   - for each anno_spatch: split in chunks
   - for each set of chunks (corresponding to one anno_spatch)
   => for each chunk
   o  locate the chunk in the lhs_term
   o  insert application information from chunk
   
   - once all chunks in all chunk-set have been handled, perform
   transformations mentioned in the inserted chunks
 *)
	
let apply_spatch_fixed spatch (term, flow) =
  let get_pattern_env_traces g sp =
    g#nodes#tolist 
      +> List.filter (function (i,gt) -> Diff.non_phony gt && not(Diff.is_control_node gt))
      +> List.fold_left (fun acc_trs (i,gt) ->
	match Diff.get_env_traces g sp i with
        | None -> ((*print_endline "nothing";*) acc_trs)
	| Some trs -> trs :: acc_trs) [] 
  in
  (* use env to replace metavars with the corresponding subterms *)
  let instantiate spatch env = 
    let f spatch = match spatch with
    | Difftype.ID  (t, ann) -> Difftype.ID  (Diff.sub env t, ann)
    | Difftype.RM  (t, ann) -> Difftype.RM  (Diff.sub env t, ann)
    | Difftype.ADD (t, ann) -> Difftype.ADD (Diff.sub env t, ann)
    | _ -> raise (Impossible 1990) in
    List.map f spatch in
  (* annotate elements of spatch with the nodei matched *)
  let annotate_spatch_seq sp node_seq = 
    let map2 skipf f ls1 ls2 = 
      let rec loop ls1 ls2 = 
        match ls1, ls2 with
        | [], [] -> []
        | e1 :: ls1', _ when skipf e1 -> e1 :: loop ls1' ls2
        | e1 :: ls1, e2 :: ls2 -> f e1 e2 :: loop ls1 ls2 
        | _, _ -> raise (Invalid_argument "annotate_spatch_seq")
      in
      loop ls1 ls2 in
    let skip_add = 
      function
	| Difftype.ADD _ -> true 
	| Difftype.ID (t,_) -> t == ddd
	| _ -> false in
    map2 skip_add add_annotation_iop sp node_seq in
  let pattern = List.fold_right 
      (fun iop acc_pattern -> 
        match iop with
        | Difftype.ID p | Difftype.RM p -> p :: acc_pattern
        | Difftype.ADD _ -> acc_pattern
        | _ -> raise (Impossible 1042)
      ) spatch [] 
  in
  let stripped_spatch = spatch +> List.filter 
      (function iop -> 
        match iop with
        | Difftype.ID p when p ==  ddd -> false
        | _ -> true) 
  in
  (* put empty operation annotations on all elements of spatch *)
  let init_annotated = spatch +> List.map 
      (function iop -> 
        match iop with
        | Difftype.ID p -> Difftype.ID (p, empty_annotation)
        | Difftype.RM p -> Difftype.RM (p, empty_annotation)
        | Difftype.ADD p -> Difftype.ADD (p, empty_annotation)
        | _ -> raise (Impossible 17)) 
  in
  (* An env_trace is list of entries each containin a path (list of
     nodes) in the CFG plus bindings for metavariables used on the
     path to make the pattern match. An env_trace is a witness for how
     a pattern matched a graph. 
     
     Thus, 'env_traceS' is a list of _all_ the ways a pattern could
     match a graph. The pattern may match starting from several
     different nodes of the graph
     
   *)
  let env_traces = get_pattern_env_traces flow pattern in
  (* We first fold over each env_trace of the pattern: for each
     env_trace we construct a new annotated tree
   *)
  List.fold_left 
  (fun acc_pending_term env_trace ->
    (* for each env_trace fold over each list 
       of (int list, env) in the env_trace
     *)
    List.fold_left 
      (fun acc_pending_term (seq, env) ->
	let sp' = instantiate init_annotated env in 
	(* annotate each element of sp' with the node matched *)
	let spa = annotate_spatch_seq sp' seq in
	(* turn the annotated spa into a list of chunks *)
	let chunks = Diff.chunks_of_diff spa in
	(* for each chunk, insert a 'pending transformation 
	   subtree' at the context-point of the chunk *)
	List.fold_left (insert_chunk flow) acc_pending_term chunks
      )
      acc_pending_term env_trace
  ) term env_traces
  +> perform_pending
    



(* this function tries to determine if the spatch is safe for some
   function; this is done by first trying to match the spatch with all
   flows and if the spatch matches that flow (function), we find the
   subterm representing the function in the lhs_term and rhs_term;
   using the matching information, we modify the lhs_term to obtain
   mhs_term and then we simply need to check that 

   safe_part lhs_term mhs_term rhs_term 
 *)

let is_spatch_safe_one (lhs_term, rhs_term, flows) spatch = 
  (* find a matching flow 
     - extract pattern from spatch
     - use exists_cont_match, |- to try all nodes in the flow for a match
   *)

  (* fold_right is ok to use here as patterns are most likely never
     much longer than 5 node-patterns/items *)
  let pattern = List.fold_right (fun iop acc_pattern -> match iop with
  | Difftype.ID p | Difftype.RM p ->
      p :: acc_pattern
  | Difftype.ADD _ -> acc_pattern
  | _ -> raise (Impossible 18)
				) spatch [] in
  let matched_flows = flows +> List.filter (function flow ->
    flow |- pattern
					   ) in
  (* find corresponding function in lhs & rhs 
     - get name of function corresponding to flow
     - get subterm in lhs which is that function
     - do for rhs term
   *)
  let fun_names = matched_flows +> List.map 
      (function flow -> (get_fun_name_gflow flow, flow)) in
  let funs = fun_names +> List.map (function (fname,flow) ->
    (fname, 
     flow, 
     get_fun_in_term fname lhs_term, 
     get_fun_in_term fname rhs_term
    )) in
  (* patch all lhs' (there can be more because our pattern might
     match more than one function), but for each function there is
     only one lhs' because we assume that spatch-application is
     deterministic; cf. no overlapping semantic patterns in each
     function flow *)
  let patched_lhss = funs +> List.map 
      (fun (fname, flow, lhs_def_term, rhs_def_term) ->
	(lhs_def_term, 
	 apply_spatch_fixed spatch (lhs_def_term, flow), 
	 rhs_def_term)
      ) in
  (* check safety of result *)
  (*print_string "safety check for: ";*)
  (*spatch +> List.map Diff.string_of_diff +> String.concat " " +> print_endline;*)
  if matched_flows = []
  then None (* no match means, the patch is safe also: EXPERIMENTAL *)
  else Some ( 
    List.exists (function (left,middle,right) -> 
      (*print_endline ("t1\t" ^ Diff.string_of_gtree' left);*)
      (*print_endline ("t2\t" ^ Diff.string_of_gtree' middle);*)
      (*print_endline ("t3\t" ^ Diff.string_of_gtree' right);*)
      if Diff.part_of_edit_dist left middle right
	  (* if Diff.msa_cost left middle right *)
      then ((*print_endline "ok";*) true)
      else ((*print_endline "unsafe";*) false)
		) patched_lhss
   )

(* decide whether sp1 <= ttf_list *)
let is_spatch_safe_ttf_list sp ttf_list =
  let nogoodfunctions = ref [] in
  v_print_endline "[Main] considering safety of:";
  let count = ref 0 in
  begin
    sp +>
    List.iter (function p -> 
      Diff.string_of_diff p +> v_print_endline);
    (*
      let count = ref 0 in
      let max_ttf = List.length ttf_list in
     *)
    List.iter
      (* using for_all is related to the above EXPERIMENTAL change *)
      (function ttf -> 
        match is_spatch_safe_one ttf sp with
        | None -> ()
        | Some t -> 
            begin
              if t
              then count := !count + 1
              else begin
                match ttf with 
                | l,_,_ -> nogoodfunctions := Reader.get_fname_ast l :: !nogoodfunctions
              end
            end
      ) ttf_list ;
    if not (!count >= !threshold)
    then begin
      (*print_endline "non-safe patch: ";*)
      (*print_endline (String.concat "\n" (List.map Diff.string_of_spdiff sp));*)
      (*print_endline ("sp only safe for " ^ string_of_int !count ^ " functions");*)
      (*print_endline ("functions: " ^ String.concat " " !nogoodfunctions);*)
      false
    end
    else true 
  end

let apply_spatch_ttf spatch (lhs_term, rhs_term, flows) =
  (* find a matching flow 
     - extract pattern from spatch
     - use exists_cont_match, |- to try all nodes in the flow for a match
   *)

  (* fold_right is ok to use here as patterns are most likely never
     much longer than 5 node-patterns/items *)
  let pattern = List.fold_right (fun iop acc_pattern -> match iop with
  | Difftype.ID p | Difftype.RM p -> p :: acc_pattern
  | Difftype.ADD _ -> acc_pattern
  | _ -> raise (Impossible 19)
				) spatch [] in
  let matched_flows = flows +> List.filter (function flow ->
    flow |- pattern
					   ) in
  (* find corresponding function in lhs & rhs 
     - get name of function corresponding to flow
     - get subterm in lhs which is that function
     - do for rhs term
   *)
  let fun_names = matched_flows +> List.map 
      (function flow -> (get_fun_name_gflow flow, flow)) in
  let funs = fun_names +> List.map (function (fname,flow) ->
    (fname, 
     flow, 
     get_fun_in_term fname lhs_term, 
     get_fun_in_term fname rhs_term
    )) in
  (* patch all lhs' (there can be more because our pattern might
     match more than one function), but for each function there is
     only one lhs' because we assume that spatch-application is
     deterministic; cf. no overlapping semantic patterns in each
     function flow *)
  let patched_lhss = funs +> List.map (function (fname, flow, lhs_def_term, rhs_def_term) ->
    (lhs_def_term, 
     apply_spatch_fixed spatch (lhs_def_term, flow), 
     rhs_def_term)
				      ) in
  patched_lhss


let implies a b = not(a) || b

let iff a b = (implies a b) && (implies b a)

let strip_patch sp = 
  let rec f rev_sp sp = match sp with
  | [] -> List.rev rev_sp
  | Difftype.ID  t :: sp when t == ddd -> f rev_sp sp
  | (Difftype.ID  t 
  | Difftype.RM  t 
  | Difftype.ADD t 
  | Difftype.PENDING_RM t 
  | Difftype.PENDING_ID t) as hd :: sp -> f (hd :: rev_sp) sp
  | _ -> raise (Impossible 1992)
  in
  f [] sp

let rec subseq s1 s2 = 
  s1 = [] || match s1, s2 with
  | x :: xs, y :: ys ->
      (x = y && subseq xs ys) 
    || subseq s1 ys
    | _ -> false


(* decide whether sp1 <= sp2 relative to ttf_list *)
let get_largest_spatchs ttf_list spatches =
  (* - for spatch
     -- for each triple (lhs,rhs,flows) produce 
     [ (f_lhs, f_mhs) | f_lhs ∈ lhs, [[spatch]](f_lhs) = f_mhs ]
     - we can produce a list indexed by spatches:
     [ (spatch, [(lhs, [(f_lhs, f_mhs) | f_lhs ∈ lhs, [[spatch]](f_lhs)=f_mhs] ) | (lhs,rhs,flows) ∈ ttf_list]
     we denote this list "applied_spatches"
     - recall that sp1 ≼ sp2 (relative to t1,t2,t3) iff
     δ(t1,t2) + δ(t2,t3) = δ(t1,t3)
     and we have [[sp2]](t1)=t3, [[sp1]](t1)=t2

     - thus given applied_spatches : (sp * (term * (term * term) list)) list 
     to decide whether sp1 ≼ sp2 given two entries from the list we must
     have 
     (sp1,[(lhs1, fm_list11), ..., (lhsn1, fm_listn1)]), 
     (sp2,[(lhs1, fm_list12), ..., (lhsn2, fm_listn2)]), 
     
     let ∀_x denote "for_some !threshold"
     
     sp1≼sp2 <=>
     ∀_x(lhsi, fmlisti) ∈ applied_spatches(sp1)
     ∀_x(lhsj, fmlistj) ∈ applied_spatches(sp2)

     lhsi=lhsj => 
     ∀(f1,m1) ∈ fmlisti, 
     ∀(f2,m2) ∈ fmlistj => 
     f1 = f2 => 
     δ(f1,m1) + δ(m1,m2) = δ(f2,m2)

   *)
  print_string "[Main] applying spatches ";
  let a_counter = ref 0 in
  let a_total = List.length spatches in
  let applied_spatches = spatches
      +> List.rev_map 
      (function sp -> begin
	Jconfig.counter_tick !a_counter a_total;
	a_counter := !a_counter + 1;
	sp,
	ttf_list +> 
	List.fold_left
	  (fun acc (lhs,rhs,flows)  ->
	    let a_ttf = apply_spatch_ttf sp (lhs,rhs,flows) in
	    if a_ttf = []
	    then acc
	    else (lhs, a_ttf) :: acc
	  ) []
      end 
      )
  in
  let is_sub lhss_fmlists1 lhss_fmlists2 = (* lhss_fmlists1 : (orig_lhs_gt, (f_src, f_mod, f_dst) list ) list *)
    lhss_fmlists2 +> for_some !threshold 
      (function (lhs2, fm_lists2) ->
	try
	  let (_, fm_lists1) = List.find (function (lhs1, _) -> lhs1 = lhs2) lhss_fmlists1 in
	  fm_lists2 +> List.for_all
	    (function (f2,m2,_) ->
	      try
		let (_, m1, _) = List.find (function (f1,m1,r1) -> f1 = f2) fm_lists1 in
		if Diff.part_of_edit_dist f2 m1 m2
		then (print_endline "part_of"; true)
		else (print_endline "NOT part_of";false)
		    (* Diff.msa_cost f2 m1 m2 *)
	      with Not_found -> 
		(print_endline  ("Not finding: " ^ Diff.string_of_gtree' f2);
		 raise Not_found)
	    )
	with Not_found -> false (*  (raise Not_found) *)
      )
  in
  (* the largest spatches are those for which all others are either smaller or not-comparable *)
  print_string "[Main] filtering largest ";
  a_counter := 0;
  applied_spatches 
    +> List.rev_map
    (function (sp, lhs_fmlists) ->
      Jconfig.counter_tick !a_counter a_total;
      a_counter := !a_counter + 1;
      print_endline "[Main] checking maximality of:";
      print_endline (sp
		       +> List.map Diff.string_of_spdiff
		       +> String.concat "\n");
      
      if applied_spatches +> List.for_all 
	  (function (sp', lhs_fmlists') ->
	    print_endline "[Main] against : ";
	    print_endline (sp'
			     +> List.map Diff.string_of_spdiff
			     +> String.concat "\n");
	    if (
	      sp = sp'
	    || (
	      let b1 = is_sub lhs_fmlists' lhs_fmlists in
	      if b1 then print_endline "b1";
	      let b2 = is_sub lhs_fmlists lhs_fmlists' in
	      if b2 then print_endline "b2";
	      if b1
	      then 
		if b2
		then (
		  print_endline "[Main] subseq?";
		  if subseq (strip_patch sp') (strip_patch sp)
		  then (print_endline "true"; true)
		  else false
		 )
		else true
	      else not b2 (* sp strictly larger or unrelated!*)
		  (*
		    if b1
		    then not b2
		    || contained_subseq 
		    (strip_patch sp') 
		    (strip_patch sp)
		    else not b2
		   *)
	     )
	  )
	    then
	      (print_endline "local ok"; true)
	    else
	      (print_endline "local counter example"; false)
	  )
      then
	(
	 print_endline "[Main] including as largest: ";
	 Some sp 
	)
      else (
	print_endline "[Main] not largest";
	None
       )
    )
    +> List.fold_left (fun acc opt -> match opt with Some sp -> 
      sp :: acc | _ -> acc) []
    +> rm_dups


let get_chunks patterns =
  let use_chunk chunk = 
    (* appends e to all lists in res: [ res' | ls <- res, res' <- res
       @ [e] ] *)
    let suffix_all res e =
      if res = [] 
      then [[e]]
      else
        res +> List.fold_left (fun res ls -> 
	  (ls @ [e])
	  :: res
			      ) []
    in
    (* results is a list of chunks to include/use/apply *)
    let rec loop chunk results =
      match chunk with
      | [] -> results
      | (Difftype.ID _) as m :: chunk -> loop chunk (suffix_all results m)
      | (Difftype.RM _) as m :: chunk -> loop chunk (suffix_all results m)
      | m :: chunk -> 
          let results' = 
            suffix_all results m
              +> List.rev_append results in 
          loop chunk results'
    in
    loop chunk [] in
  let init_count = ref 0 in
  let total_count = List.length !Diff.flow_changes in
  print_endline ("[Main] getting initial chunks |flow_changes| = " ^ 
		 !Diff.flow_changes +> List.length +> string_of_int);
  let chunks =
    !Diff.flow_changes +>
    List.fold_left (fun acc_chunks_lists diff ->
      List.rev_append 
	(Jconfig.counter_tick !init_count total_count;
	 init_count := !init_count + 1;
	 Diff.chunks_of_diff_spatterns patterns diff)
	acc_chunks_lists) [] in
  print_endline ("[Main] extracting the good chunks (initial: "^chunks +> List.length +> string_of_int^")");
  let good_chunks = chunks 
      +> List.filter (function diff -> match diff with 
      | [Difftype.ID _] -> false
      | _ -> true)
      +> List.filter (function diff -> match get_context_point diff with
      | Difftype.ID context_point 
      | Difftype.RM context_point -> 
	  (* does the context-point match anything in at least some pattern *)
	  not(Diff.get_change_matches patterns context_point = [])
      | _ -> raise (Impossible 6)
		     )
      +> rm_dups in

  print_endline ("[Main] good chunks ("^ good_chunks +> List.length +> string_of_int^")");
  good_chunks  
    +> List.iter (function diff -> 
      print_endline "[Chunk]";
      print_endline (diff 
		       +> List.map Diff.string_of_diff
		       +> String.concat "\n");
      print_endline "[End]"
                 ); 

  print_endline "[Main] exploding the chunks";
  let returned_chunks = good_chunks 
      +> List.rev_map use_chunk
      +> tail_flatten
      +> rm_dups
  in
  (*
    List.iter (function diff -> 
    print_endline "[RetChunk]";
    print_endline (diff 
    +> List.map Diff.string_of_diff
    +> String.concat "\n");
    print_endline "[End]"
    ) returned_chunks;
   *)
  begin
    if !print_chunks
    then
      returned_chunks
        +> List.iter (function diff -> 
          print_endline "[Chunk]";
          print_endline (diff 
			   +> List.map Diff.string_of_diff
			   +> String.concat "\n");
          print_endline "[End]"
                     );
    returned_chunks
  end

(* function to find more abstractins in RHS of spatches *)
let get_missed_rhs cand_spatches gss =
  let gs = tail_flatten gss in
  (* find graphs where sp matches *)
  (* for each node that makes sp match: *)
  (* - collect matching env 
     - map find_rhs spatch
   *)
  let f x subterm acc_term =
    let rec loop current_subterm = 
(*
  print_endline "comparing current subterm :";
  print_endline (Diff.string_of_gtree' current_subterm);
  print_endline "to env-bound subterm :";
  print_endline (Diff.string_of_gtree' subterm);
 *)
      if current_subterm = subterm
      then (
(*	print_endline ("inserting " ^ x); *)
	mkA("meta", x)
       )
      else match view current_subterm with
      | C(ty, ts) -> mkC(ty, List.rev (List.rev_map loop ts))
      | _ -> current_subterm
    in
    loop acc_term in
  let find_rhs_one env patch_term = match patch_term with
  | Difftype.ADD t -> Difftype.ADD (Hashtbl.fold f env t)
  | _ -> patch_term in
  let find_rhs_sp env spatch =
    List.map (find_rhs_one env) spatch
  in
  (* for each spatch *)
  List.fold_left 
    (fun acc_spatches sp -> 
      let s_pattern = List.fold_right
	  (fun po acc_pat -> match po with
	  | (Difftype.ID t | Difftype.RM t) -> t :: acc_pat
	  | _ -> acc_pat) sp [] 
      in
      (* for each graph *)
      List.fold_left (fun acc_spatches f ->
	let envs = 
	  List.fold_left 
	    (fun acc_envs n ->
	      match Diff.get_merged_env f s_pattern n with
	      | None -> acc_envs
	      | Some e -> e :: acc_envs
	    )
	    []
	    (nodes_of_graph2 f) 
	in
	(* for each env found *)
	List.fold_left 
	  (fun acc_spatches env ->
	    find_rhs_sp env sp +++ acc_spatches
	  ) acc_spatches envs
		     ) acc_spatches gs
	
    ) [] cand_spatches


let get_cfg_changeset () =
  List.rev (
  List.fold_left (fun acc_pairs (lfile, rfile) ->
    Reader.read_filepair_cfg lfile rfile @ acc_pairs
		 ) [] !file_pairs)
    +> List.filter (function ((gt_lhs,f_lhs), (gt_rhs, f_rhs)) -> 
      not(!only_changes) 
    || not(gt_lhs = gt_rhs)
		   ) 

let find_common_patterns () =
  (*  malign := true; *)
  Diff.malign_mode := !malign; (* maling might be very slow *)
  file_pairs := Reader.read_spec !mfile; (* gets names to process in file_pairs *)
  (* term_pairs is the changeset used as input *)
  let term_pairs = get_cfg_changeset () 
  in
  print_endline ("[Main] read " ^ string_of_int (List.length term_pairs) ^ " files");
  let gss = lhs_flows_of_term_pairs term_pairs in
  let gpats'' = common_patterns_graphs gss in
  let gpats' = filter_changed gpats'' +> rm_dups in
  if List.length gpats' = 0
  then print_endline "[Main] *NO* common patterns found"
  else begin
    print_endline "[Main] *Common* patterns found:";
    print_patterns gss gpats';
  end;
  if not(!patterns)
  then begin
    print_endline ("[Main] finding chunks based on " ^ string_of_int(List.length(gpats')) ^ " patterns");
    let chunks = get_chunks gpats' in
    print_endline "[Main] constructing s.patches";
    let ttf_list = term_pairs +> List.rev_map (function ((lhs_gt, lhs_flow),(rhs_gt,_)) -> 
      (lhs_gt, rhs_gt, [lhs_flow])
					      ) in
    let ttf_focus_fun = 
      if haveFocusFun ()
      then 
        try 
          Some (List.find 
		  (function lhs_gt, rhs_gt, [lhs_flow] -> 
		    Reader.get_fname_ast lhs_gt +> sameName) ttf_list)
        with Not_found -> None
      else None
    in
    let is_transformation_sp sp = 
      sp +> List.exists (function p ->
	match p with
	| Difftype.ID _ -> false
	| _ -> true) in
    let safe_for_ff sp =
      match ttf_focus_fun with
      | None -> true
      | Some ttf -> (match is_spatch_safe_one ttf sp with
        | None -> true
        | Some b -> b
		    ) in
    let is_safe_part sp =
      let spa = List.map 
	  (function p -> 
            match p with
            | Difftype.PENDING_RM p' -> Difftype.RM p'
            | Difftype.PENDING_ID p' -> Difftype.ID p'
            | _ -> p
	  ) sp in
      not(is_transformation_sp spa)
    || (
      (match ttf_focus_fun with
      | None -> true
      | Some ttf -> 
          (match is_spatch_safe_one ttf spa with
          | None -> true
          | Some b -> b
          )
      )
        && is_spatch_safe_ttf_list spa ttf_list 
   ) in
    
    let sp_candidates = construct_spatches_new chunks is_safe_part gpats'  in
    let trans_patches' = sp_candidates +> List.filter is_transformation_sp in
    if !print_raw
    then begin
      print_endline "[Main] candidate semantic patches...";
      trans_patches' +>
      List.iter (function sp -> 
	print_endline "[spatch:]";
	print_endline (sp
			 +> List.map Diff.string_of_spdiff
			 +> String.concat "\n");
		)
    end;
    print_endline ("[Main] getting missed RHS bindings");
    let trans_patches = get_missed_rhs trans_patches' gss in
    if !print_raw
    then begin
      print_endline "[Main] after missed-analysis we have semantic patches...";
      trans_patches +>
      List.iter (function sp -> 
	print_endline "[spatch:]";
	print_endline (sp
			 +> List.map Diff.string_of_spdiff
			 +> String.concat "\n");
		)
    end;
    print_string ("[Main] filtering safe semantic patches ("^ trans_patches +> 
	    						      List.length +> 
							      string_of_int ^") ... ");
    let res_count = ref 0 in
    let res_total = List.length trans_patches in
    let res_spatches = 
      trans_patches
	+> List.fold_left 
	(fun acc_sps sp -> begin
	  ANSITerminal.save_cursor ();
	  ANSITerminal.print_string 
	    [ANSITerminal.on_default](
	  !res_count +> string_of_int ^"/"^
	  res_total +> string_of_int);
	  ANSITerminal.restore_cursor();
	  flush stdout;
	  res_count := !res_count + 1;
	  if safe_for_ff sp && is_spatch_safe_ttf_list sp ttf_list
	  then sp :: acc_sps
	  else begin
	    if !Jconfig.print_abs
	    then 
	      begin
		print_endline "[Main] not safe...";
		print_endline (String.concat "\n" (List.map Diff.string_of_spdiff sp));
	      end;
	    acc_sps
	  end
	end) []
	+> rm_dups
    in
    print_newline ();
    if !Jconfig.print_abs
    then begin
      List.iter (function sp -> 
	print_endline "[spatch:]";
	print_endline (sp
			 +> List.map Diff.string_of_spdiff
			 +> String.concat "\n");
		) res_spatches
    end;
    print_endline ("[Main] filtering largest semantic patches ("^
		   res_spatches +> List.length +> string_of_int
		   ^")");
    let largest_spatches =
      res_spatches 
	+> (function spatches -> 
	  if !filter_spatches then get_largest_spatchs ttf_list spatches
	  else spatches)
	+> rm_dups
    in
    print_endline ("[Main] *REAL* semantic patches inferred: " ^
		   List.length largest_spatches +> string_of_int);
    largest_spatches
      +> List.iter (function diff ->
	print_endline "[spatch:]";
	print_endline (diff
			 +> (* List.map Diff.string_of_spdiff*)
		       Diff.string_of_spdiff_full
			 (*+> String.concat "\n"*)
		      );
	if !show_support
	then begin
	  let sup = ttf_list +> List.filter 
	      (function (gt_l,gt_t,flows) as ttf ->
		match is_spatch_safe_one ttf diff with
		| None -> false
		| Some t -> t
	      ) 
	  in
	  print_endline ("supporting functions (" 
			 ^ sup +> List.length +> string_of_int 
			 ^ "/" ^ ttf_list +> List.length +> string_of_int 
			 ^ ")");
	  print_string "< ";
	  sup +> List.iter 
	    (function (l,r,fs) -> 
	      l +> Reader.get_fname_ast +> print_string;
	      print_string " ";
	    );
	  print_endline " >";
	  print_newline ();
	end
		   )
  end		  





let embedded p t =
  let return env = Some env in
  let zero = None in
  let add_bind env (x,t) =
    try 
      let t' = List.assoc x env 
      in
      if t = t' then return env
      else zero
    with Not_found -> return ((x,t) :: env) in
  let rec embedded_lists env ps ts =
    match ps with
    | [] -> return env
    | p :: ps -> 
	(match ts with
	| [] -> zero
	| t :: ts ->
	    (match loop env p t with
	    | None -> embedded_lists env (p::ps) ts
	    | Some env' ->
		(match embedded_lists env' ps ts with
		| None -> embedded_lists env (p::ps) ts
		| Some env -> return env
		)
	    )
	)
  and loop env p t = 
    if p = t
    then return env 
    else match view p, view t with
    | (A ("meta", x)) , t -> add_bind env (x,t)
    | (C (c,ps)), (C (c',ts)) when 
	c = c' && List.length ps <= List.length ts -> 
	  embedded_lists env ps ts
    | _ -> zero
  in
  loop [] p t

let is_embedded p t = match embedded p t with
| None -> false
| Some _ -> begin
    v_print_endline "[Main] is_embedded";
    p +> Diff.string_of_gtree' +> v_print_endline;
    v_print_endline "IN";
    t +> Diff.string_of_gtree' +> v_print_endline;
    v_print_endline "#";
    true
end


let add_csize (l1,r1) (l2,r2) = (l1+l2,r1+r2)

let csize p = 
  let rec loop acc p =
    match view p with
    | A("meta", _) -> acc
    | A(_,_) -> add_csize acc (1,0)
    | C(_,ps) -> List.fold_left loop (add_csize acc (1,0)) ps
  in
  loop (0,0) p



let find_embedded t1 t2 =
  let current_embedded_depth = ref 0 in
  let add_bind env pair =
    try 
      let 
	  (m,_) = List.find (function (m,pair') -> pair = pair') env 
      in
      mkA("meta",m), env
    with Not_found ->
      let meta_term, meta = new_meta_id () in
      meta_term, (meta,pair) :: env in
(*
  let csize_list ts = List.fold_left 
  (fun acc t -> (add_csize (csize t) acc)) (0,0) ts in
  let is_up_or_id op = match op with 
  | Difftype.UP _ 
  | Difftype.ID _ -> true 
  | _ -> false 
  in
 *)
  let rec loop_lists env ts1 ts2 = match ts1, ts2 with
  | [], _ -> [], env
  | _, [] -> [], env
  | (t1 :: tail1), (t2 :: tail2) when t1 = t2 ->
      let ts, env' = loop_lists env tail1 tail2 in
      (t1 :: ts, env')
  | (t1 :: tail1), (t2 :: tail2) ->


      Diff.patience_diff ts1 ts2
	+> List.rev
	+> List.fold_left 
	(fun (acc_ts, acc_env) up -> match up with
	| Difftype.UP(l,r) ->
(*
  (loop acc_env l r +> fst :: acc_ts, acc_env)
 *)
	    let t', env' = loop acc_env l r in
	    (t' :: acc_ts, env')

	| Difftype.ID t' -> (t' :: acc_ts, acc_env)
	| Difftype.ADD _
	| Difftype.RM _ -> (acc_ts, acc_env)
	| _ -> raise (Diff.Fail "unhandled case in find_embedded")
	) ([], env)

(*
  
  let tsa, enva = loop_lists env tail1 ts2 in
  let sizea     = csize_list tsa in
  let tsb, envb = loop_lists env ts1 tail2 in
  let sizeb     = csize_list tsb in
  let t', env'  = loop env t1 t2 in
  let tsc, envc = loop_lists env' tail1 tail2 in
  let sizec'    = csize_list tsc in
  let sizec     = add_csize (csize t') sizec' in
  if sizec >= sizea 
  && sizec >= sizeb
  then (t' :: tsc), envc
  else if sizea >= sizeb
  then tsa, enva
  else tsb, envb
 *)

  and loop env t1 t2 = match view t1, view t2 with
  | _, _ when t1 = t2 -> t1, env
(*
  | _, _ when !current_embedded_depth > !max_embedded_depth -> 
  add_bind env (t1, t2)	  
 *)
  | C(ty1,ts1), C(ty2,ts2) when ty1 = ty2 ->
      let old = !current_embedded_depth in
      begin
	current_embedded_depth := !current_embedded_depth + 1;
	let ts3, env' = loop_lists env ts1 ts2 in
	begin
	  current_embedded_depth := old;
	  mkC(ty1, ts3), env'
	end
      end
  | _, _ -> add_bind env (t1,t2)
  in 
  loop [] t1 t2


let some = Diff.some
let get_some = Diff.get_some 



let find_merged_from_sets terms_lists = 
  let interesting p acc_patterns =
    not(no_leaves p)
      && not(List.mem p acc_patterns)
  in
  terms_lists 
    +> List.fold_left
    (fun acc_patterns_opt terms ->
      match acc_patterns_opt with
      | None -> terms +> some
      | Some acc_patterns ->
	  acc_patterns
	    +> List.fold_left 
	    (fun acc_patterns' p_merged ->
	      terms 
		+> List.fold_left
		(fun acc_patterns'' t ->
		  (* let p' = find_embedded p_merged t *)
		  let p' = Diff.merge_terms p_merged t 
		      +> fst +> renumber_metas_gtree in
		  if interesting p' acc_patterns''
		  then p' :: acc_patterns''
		  else begin
		    acc_patterns''
		  end
		) acc_patterns'
	    ) (List.rev_append acc_patterns terms)
	    +> some
    ) None
    +> get_some
    +> (function ps -> begin
      print_string "[Main] before filtering : ";
      ps +> List.length +> string_of_int +> print_string;
      print_endline " number of pattern(s)";
      ps
    end
       )


    +> List.filter 
    (function p -> 
      terms_lists 
	+> for_some !threshold 
	(function terms -> 
	  terms
	    +> List.exists 
	    (function t ->
	      if !Jconfig.verbose 
	      then (
		print_endline "[Main] testing embedded:";
		p+>Diff.string_of_gtree'+>print_endline;
		print_endline "IN";
		t+>Diff.string_of_gtree'+>print_endline;
	       );
	      Diff.can_match p t 
	    )
	)
    )


(* find atoms in t1 and t2 that are equal *)
let find_equal_atoms t1 t2 =
  let rec get_atoms acc_atoms t = match view t with
  | A _ -> t :: acc_atoms
  | C (_,ts) -> List.fold_left get_atoms acc_atoms ts
  in
  let atoms1 = get_atoms [] t1 in
  let atoms2 = get_atoms [] t2 in
  atoms1 +> List.filter (function atom1 -> List.mem atom1 atoms2)


let get_matched_terms terms_lists pat =
  terms_lists +> List.fold_left
    (fun acc_terms_lists terms -> 
      terms +> List.filter
	(function t -> Diff.can_match pat t)
      :: acc_terms_lists
    ) []


let find_embedded_from_sets patterns terms_lists = 
  let interesting p acc_patterns =
    not(no_leaves p)
      && not(List.mem p acc_patterns)
      && acc_patterns +> List.for_all 
      (function p' -> 
	not(is_embedded p p') ||
	(not(is_embedded p' p) || csize p' <= csize p)
      )

  in
  (* for each pattern:
     1) restrict terms_list to the matching terms
     2) find common embeddings relative to the restricted terms-lists
   *)
  patterns
    +> List.rev_map
    (function p ->
      begin
	print_endline "[Main] finding *embedded* patterns in: ";
	p+>Diff.string_of_gtree'+>print_endline;
	let terms_lists_restricted = get_matched_terms terms_lists p 
	in

	terms_lists_restricted
	  +> List.fold_left
	  (fun acc_patterns_opt terms ->
	    match acc_patterns_opt with
	    | None -> terms +> some
	    | Some acc_patterns ->
		acc_patterns
		  +> List.fold_left 
		  (fun acc_patterns' p_merged ->
		    terms 
		      +> List.fold_left
		      (fun acc_patterns'' t ->
			let p' = find_embedded p_merged t 
			    +> fst +> renumber_metas_gtree in
			if interesting p' acc_patterns''
			then p' :: acc_patterns''
			else begin
			  acc_patterns''
			end
		      ) acc_patterns'
		  ) (List.rev_append acc_patterns terms)
		  +> some
	  ) None
	  +> get_some
	  +> (function ps -> begin
	    print_endline "[Main] for pattern ";
	    p+>Diff.string_of_gtree'+>print_endline;
	    print_string "[Main] we found ";
	    ps +> List.length +> string_of_int +> print_string;
	    print_endline " number of pattern(s)";
	    ps
	  end
	     )
	  +> List.filter 
	  (function p_embedded ->
	    terms_lists_restricted
	      +> for_some !threshold 
	      (function terms ->
		terms
		  +> List.exists 
		  (function t ->
		    is_embedded p_embedded t
		  )
	      )
	  )
      end)
    +> tail_flatten

let implies b1 b2 = not(b1) || b2
let (===>) b1 b2 = implies b1 b2

let embedded_subpattern_term p1 p2 term =
  (* p1 is an embedded subpattern of p2 relative to term iff
     p2 <= term & p1 <= term & p1 <= p2
   *)
  is_embedded p2 term
    && is_embedded p1 term
    && is_embedded p1 p2

let embedded_subpattern_terms p1 p2 terms =
  terms 
    +> List.for_all
    (function term ->
      implies 
	(is_embedded p2 term) 
	(is_embedded p1 term 
	   && is_embedded p1 p2)	 
    )

let embedded_subpattern_terms_lists p1 p2 terms_lists =
  terms_lists 
    +> for_some !threshold 
    (function terms ->
      embedded_subpattern_terms p1 p2 terms
    )



let find_embedded_common () =
  Diff.abs_depth     := !depth;
  Diff.abs_subterms  := !max_level;
  file_pairs := Reader.read_spec !mfile; (* gets names to process in file_pairs *)
  (* now make diff-pairs is a list of abs-term pairs *)
  let term_pairs = 
    List.fold_left (fun acc_pairs (lfile, rfile) ->
      Reader.read_filepair_top lfile rfile :: acc_pairs
		   ) [] !file_pairs
  in
  if !threshold = 0
  then 
    threshold := List.length term_pairs;
  Diff.no_occurs := !threshold;
  let relevant_terms = 
    term_pairs 
      +> List.rev_map (function pairs -> List.fold_left
	  (fun acc_terms (l,r) ->
	    if !only_changes
	    then 
	      if l = r 
	      then acc_terms
	      else l :: acc_terms
	    else
	      l :: acc_terms
	  ) 
	  []
	  pairs)
  in
  print_endline ("[Main] #no of terms to consider " ^ 
		 relevant_terms 
		   +> List.length
		   +> string_of_int);
  let merged = 
    find_merged_from_sets relevant_terms
      +> (function x ->
	print_endline "[Main] merged terms, now filtering embeddings";
	x
	 )
      +> rm_dups
(*
  +> function ps -> 
  ps +> List.filter 
  (function p -> 
  ps +> List.for_all
  (function p' ->
  implies 
  (embedded_subpattern_terms_lists p p' relevant_terms)
  (csize p' <= csize p)
  )
  )
 *)
  in
  begin
    print_endline ("[Main] " ^ 
		   merged
		     +> List.length
		     +> string_of_int ^ " common pattern(s) follow...");
    merged +> List.iter (function p -> 
      p
	+> Diff.string_of_gtree'
	+> print_endline 
			);
    print_endline "[Main] looking for common structure in patterns";
    let embeddings = 
      find_embedded_from_sets merged relevant_terms 
	+> rm_dups
	+> function ps -> 
	  ps +> List.filter 
	    (function p -> 
	      not(no_leaves p) &&
	      ps +> List.for_all
		(function p' ->
		  not(is_embedded p p') ||
		  csize p' <= csize p
		)
	    )	 
    in
    print_endline ("[Main] " ^ 
		   embeddings
		     +> List.length
		     +> string_of_int ^ " common embeddings(s) follow...");
    embeddings +> List.iter (function p -> 
      p
	+> Diff.string_of_gtree'
	+> print_endline 
			    );


    if !tmp_flag
    then  
      begin
	print_endline "[Main] looking for matched terms that changed";
	let flat_term_pairs = tail_flatten term_pairs in
	let pattern_term_pairs = 
	  embeddings 
	    +> List.fold_left 
	    (fun acc_pattern_term_pairs p ->
	      let term_pairs = flat_term_pairs 
		  +> List.filter
		  (function (l,r) -> 
		    not(l = r)
		      && is_embedded p l
		  )
	      in 
	      (p, term_pairs) :: acc_pattern_term_pairs
	    ) [] in
	print_endline "[Main] performing gpi for each embedded pattern";
	pattern_term_pairs 
	  +> List.iter (function (p, term_pairs) -> 
	    if term_pairs = []
	    then begin
	      print_endline "[Main] skipping pattern:";
	      p+>Diff.string_of_gtree'+>print_endline;
	    end
	    else begin
	      print_endline "[Main] ###################";
	      print_endline "[Main] relative to pattern:";
	      p+>Diff.string_of_gtree'+>print_endline;
	      print_endline "[Main] ###################";
	      spec_main_term_pairs term_pairs;
	    end
		       )
      end
  end

    

let find_fun_common () =
  Diff.abs_depth     := !depth;
  Diff.abs_subterms  := !max_level;
  file_pairs := Reader.read_spec !mfile; (* gets names to process in file_pairs *)
  (* now make diff-pairs is a list of abs-term pairs *)
  let term_pairs = 
    List.fold_left (fun acc_pairs (lfile, rfile) ->
      Reader.read_filepair_defs lfile rfile @ acc_pairs
		   ) [] !file_pairs
      +> List.filter (function (l,r) ->
    	not(!only_changes) || not(l = r)
    		     )
  in
  if !threshold = 0
  then 
    threshold := List.length term_pairs;
  Diff.no_occurs := !threshold;
  let subterms_lists = 
    List.rev_map (function f,_ -> [f]) term_pairs  in
  let unique_subterms = subterms_lists
      +> tail_flatten
      +> Diff.rm_dub in
  let p_env_list = Diff.abstract_all_terms 
      subterms_lists 
      unique_subterms
      [] in
  let get_frequency p = 
    Diff.TT.find Diff.prepruned_ht p 
      
      (* unique_subterms +> List.fold_left *)
      (* 	(fun acc_n t -> if Diff.can_match p t *)
      (* then acc_n + 1 else acc_n) 0 *)
  in
  begin
    print_endline "[Main] resulting frequent abstractions...";
    p_env_list 
      +> (function x -> print_endline "[Main] removing useless patterns"; x)
      +> List.filter 
      (function (p,env) -> 
	match view p with
	| C("def", [name;funtype;gt_body]) -> 
	    not(Diff.useless_abstraction gt_body)
	| _ -> false
      )
      +> (function x -> print_endline "[Main] sorting according to increasing order of frequency"; x)
      +> List.sort (fun (p,_) (p',_) -> 
	get_frequency  p 
	  - get_frequency  p'
		   )
      +> List.iter (function (p,env) -> 
	begin
	  let sup = get_frequency p
	      (* subterms_lists  *)
	      (* +> List.fold_left  *)
	      (* (fun *)
	      (*    acc_s [def] ->  *)
	      (* 	 if Diff.can_match p def *)
	      (* 	 then acc_s + 1 *)
	      (* 	 else acc_s *)
	      (* ) 0  *)
	  in
	  print_endline (">>> freq: " ^ string_of_int sup ^ "\n" ^
			 p +> Diff.string_of_gtree');
	  if !print_support
	  then begin
	    (* print supporting set also *)
	    print_endline "[Main] support-set for pattern:";
	    let count = ref 0 in
	    subterms_lists
	      +> List.iter (function
		| [def] ->
		    if Diff.can_match p def
		    then begin
		      count := !count + 1;
		      def +> Diff.string_of_gtree' +> print_endline;
		    end
		| _ -> raise (Impossible 116)
			   );
	    if !count < !threshold
	    then print_endline "[Main] the supperting set seems smaller than threshold?";
	    print_newline();
	  end
	end
		   )
  end

let print_term_pairs () =
  file_pairs := Reader.read_spec !mfile; (* gets names to process in file_pairs *)
  (* now make diff-pairs is a list of abs-term pairs *)
  let term_pairs = 
    List.fold_left (fun acc_pairs (lfile, rfile) ->
      Reader.read_filepair_defs lfile rfile @ acc_pairs
		   ) [] !file_pairs
      +> List.filter (function (l,r) ->
    	not(!only_changes) || not(l = r)
    		     )
  in
  term_pairs +> List.iter (function (t,t') ->
    t +> Diff.verbose_string_of_gtree +> print_string;
    print_string " ";
    t' +> Diff.verbose_string_of_gtree +> print_endline;
			  )
    
let main () =
  (* decide which mode to operate in *)
  Arg.parse speclist (function _ -> ()) "Usage: ";
  Diff.be_strict     := !strict;
  Diff.use_mvars     := !mvars;
  Diff.be_fixed      := !fixed;
  Diff.no_exceptions := !exceptions;
  Diff.verbose       := !Jconfig.verbose;
  Diff.nesting_depth := !nesting_depth;
(*  malign             := true; *)
  Diff.malign_mode   := !malign;
  Diff.patterns      := !patterns;
  Diff.abs_subterms  := !max_level;

  print_endline "[Main] experimental version using 'exists' semantics for \"...\"";
  if(!focus_function != "")
  then print_endline ("[Main] focus function : '" ^ !focus_function  ^ "'");

  if !Config.std_h <> "" then
    (print_endline ("[Main] have std.h file: " ^ !Config.std_h);
     Parse_c.init_defs !Config.std_h
    );
  if !threshold = 0 then do_dmine := false;
  if !mfile = ""
  then raise (Diff.Fail "No specfile given")
  else if !cache
  then print_term_pairs ()
  else if !spatch || !patterns
  then find_common_patterns ()
  else if !fun_common
      (* then find_fun_common ()   *)
  then find_embedded_common ()
  else spec_main ()


let _ = main()

