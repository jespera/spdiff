open Gtree
open Common


let do_dmine     = ref true
let malign       = ref false
let abs          = ref false
let spec         = ref false
let mfile        = ref ""
let max_level    = ref 10
let depth        = ref 4
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
let default_abstractness = ref 2.0
let verbose      = ref false
let only_changes = ref false
let nesting_depth = ref 1
let filter_patterns = ref false
let filter_spatches = ref false

let speclist =
  Arg.align
    [
      "-noncompact",    Arg.Set noncompact,      "bool  also return non-compact solutions";
      "-specfile",      Arg.Set_string mfile,    "str   name of specification file";
      "-top",           Arg.Set_int max_level,   "int   terms larger than this will not have subterms abstracted";
      "-depth",         Arg.Set_int depth,       "int   recursion depth at which we still abstract terms";
      "-strict",        Arg.Set strict,          "bool  strict: fv(lhs) = fv(rhs) or nonstrict(default): fv(rhs)<=fv(lhs)";
      "-multiple",      Arg.Set mvars,           "bool  allow equal terms to have different metas";
      "-fixed",         Arg.Set fixed,           "bool  never abstract fixed terms";
      "-exceptions",    Arg.Set_int exceptions,  "int   the number of allowed exceptions to the rule derived";
      "-threshold",     Arg.Set_int threshold,   "int   the minimum number of occurrences required";
      "-noif0_passing", Arg.Clear Flag_parsing_c.if0_passing, 
      "bool  also parse if0 blocks";
      "-print_abs",     Arg.Set Diff.print_abs,  "bool  print abstract updates for each term pair";
      "-relax_safe",    Arg.Set Diff.relax,      "bool  consider non-application safe [experimental]";
      "-print_raw",     Arg.Set print_raw,       "bool  print the raw list of generated simple updates";
      "-print_uniq",    Arg.Set print_uniq,      "bool  print the unique solutions before removing smaller ones";
      "-print_add",     Arg.Set print_adding,    "bool  print statement when adding a new solution in generate_sol";
      "-prune",         Arg.Set prune,           "bool  try to prune search space by various means";
      "-strip_eq",      Arg.Set strip_eq,        "bool  use eq_classes for initial atomic patches";
      "-patterns",      Arg.Set patterns,        "bool  look for common patterns in LHS files";
      "-spatch",        Arg.Set spatch,          "bool  find semantic patches (not generic)";
      "-abstractness",  Arg.Set_float default_abstractness,
      "float abstractness(explain)";
      "-only_changes",  Arg.Set only_changes,    "bool  only look for patterns in changed functions";
      "-nesting_depth", Arg.Set_int nesting_depth,
      "int   allow inference of patterns nested this deep (slow)";
      "-verbose",       Arg.Set verbose,         "bool  print more intermediate results";
      "-filter_patterns", Arg.Set filter_patterns, "bool  only produce largest patterns";
      "-malign",        Arg.Set malign,          "bool  use the new subpatch relation definition";
      "-filter_spatches", Arg.Set filter_spatches, "bool  filter non-largest spatches";
      "-macro_file",    Arg.Set_string Config.std_h, "<filename> default macros"
    ]

exception Impossible of int

let v_print s = if !verbose then (print_string s; flush stdout)
let v_print_string = v_print
let v_print_endline s = if !verbose then print_endline s
let v_print_newline () = v_print_endline ""

let ddd = Diff.ddd

let (+>) o f = f o

(* tail recursive version of flatten; does *not* preserve order of elements in
 * the lists 
 *)
let tail_flatten lss =
  lss +> List.fold_left List.rev_append []

let (+++) x xs = if List.mem x xs then xs else x :: xs


let filesep = Str.regexp " +"
let file_pairs = ref []

let read_filepair old_file new_file =
  print_endline 
    ("Reading file pair " ^
       old_file ^ " " ^ new_file);
  Diff.read_src_tgt old_file new_file

let read_filepair_defs old_file new_file =
  print_endline 
    ("Reading file pair " ^
       old_file ^ " " ^ new_file);
  Diff.read_src_tgt_def old_file new_file

let read_filepair_cfg old_file new_file =
  print_endline 
    ("Reading file pair " ^
       old_file ^ " " ^ new_file);
  Diff.read_src_tgt_cfg old_file new_file

let read_spec () =
  print_endline ("Spec. file is: " ^ !mfile);
  let ins = open_in !mfile in
  let rec loop () =
    let next_line = input_line ins in 
    let next_two  = Str.split filesep next_line in
      if Str.string_before (List.hd next_two) 1 = "#"
      then
	print_endline "Comment"
      else (
	print_endline ("Parsed two: " ^ 
			 List.nth next_two 0 ^ ", " ^
			 List.nth next_two 1);
	file_pairs := (
          List.nth next_two 0,
          List.nth next_two 1) :: 
          !file_pairs);
      loop ()
  in
    try loop () with
	End_of_file -> ()

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
    (*List.for_all*)
    (*(function bp' -> *)
    (*Diff.subpatch_changeset chgset bp' bp &&*)
    (*(!noncompact || Difftype.csize bp' <= Difftype.csize bp)*)
    (* ) *)
    (*solutions in*)
    List.for_all
      (function bp' ->
         (Diff.subpatch_changeset chgset bp bp' && bp = bp') ||
           if Diff.subpatch_changeset chgset bp' bp
           then (!noncompact || Difftype.csize bp' <= Difftype.csize bp)
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
      (*not(Diff.subpatch_changeset chgset_orig bp cur_bp) &&*)
      let nbp = unwrap (extend_bp (Some cur_bp) bp) in
	(*print_endline "[Main] applying 1:";*)
	(*print_endline (Diff.string_of_diff nbp);*)
	if !Diff.relax 
	then (
	  let chgset' = Diff.apply_changeset nbp chgset_orig in
	    (*print_endline "[Main] applying 2:";*)
	    (*print_endline (Diff.string_of_diff cur_bp);*)
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
    | None -> bps (*simple_patches*)
    | Some cur_bp -> (
	(*print_string "[Main] considering next w.r.t.\n\t";*)
	(*print_endline (Diff.string_of_diff cur_bp);*)
	let res = List.filter (function bp ->
				 try app_pred cur_bp bp with Diff.Nomatch -> false
			      ) bps

        (* (restrict_bps cur_bp bps) (* this is just too slow to be worth
         * it*) *) in
	(*print_endline "[Updates added";*)
	(*List.iter (function bp -> print_endline ("\t"^Diff.string_of_diff bp)) res;*)
	  res
      )
  in
  let add_sol cur_bp sol = 
    match cur_bp with 
      | None -> print_endline "[Main] no solutions?"; []
      | Some cur_bp -> (
          if !print_adding
          then (
            print_string ("[Main] trying solution... (" ^
                            string_of_int (List.length sol) ^")");
            flush stdout;
            print_endline (Diff.string_of_diff cur_bp)
          );
          (*        let res = filter_smaller chgset_orig (filter_redundant (cur_bp ::
           *        sol)) *)
          let res = filter_smaller chgset_orig (cur_bp :: sol)
          in
            if !print_adding
            then print_endline ("done (" ^ string_of_int (List.length res) ^ ")");
            res
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
      else
	(
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
				else let bps_new_pool = List.filter (fun bp' -> not(bp = bp')) bps_pool in
				  gen sol bps_new_pool nbp
			      else let bps_new_pool = List.filter (fun bp' -> not(bp = bp')) bps_pool in
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
	print_endline ("[Main] found " ^
			 string_of_int (List.length res) ^ " solutions");
	List.map list_of_bp res


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
  read_spec(); (* gets names to process in file_pairs *)
  (* now make diff-pairs is a list of abs-term pairs *)
  let term_pairs = 
    List.fold_left (fun acc_pairs (lfile, rfile) ->
		      read_filepair_defs lfile rfile @ acc_pairs
		   ) [] !file_pairs
    +> List.filter (function (l,r) ->
    		      not(!only_changes) || not(l = r)
    		   )
  in
    (* assume that a threshold of 0 means the user did not set it
     * thus, set it to max instead 
     *)
    if !threshold = 0
    then threshold := List.length term_pairs;
    Diff.no_occurs := !threshold;
    print_string "[Main] making all lists of all subterms...";
    let subterms_lists = 
      term_pairs 
      +> List.filter (function (l,r) -> not(l = r))
      +> List.rev_map 
      (function x -> x +> fst +> Diff.make_all_subterms) in
      print_newline();
      print_string "[Main] making list of unique subterms...";
      let unique_subterms = subterms_lists
	+> tail_flatten
	+> Diff.rm_dub in
      (* now make all (relevant) term updates for each term pair *)
	print_newline ();
	print_endline (
	  "[Main] Constructing all safe parts for " ^ 
	    string_of_int (List.length term_pairs) ^ " term pairs");
	let tcount = ref 1 in
	let abs_patches = List.rev_map 
	  (function (t, t'') ->
	     print_endline ("[Main] Making safe parts for pair " ^ string_of_int !tcount);
	     tcount := !tcount + 1;
	     let r = Diff.make_abs_on_demand term_pairs subterms_lists unique_subterms (t, t'') in
	       print_endline ("[Main] abstracted one pair into " ^ 
				r +> List.length +> string_of_int ^ " abstract");
	       r
	  ) term_pairs in
	  (*{{{*)
	  if !print_raw
	  then (
	    print_endline "Those were the safe parts";
	    print_endline "{{{";
	    List.iter (fun ds ->
			 List.iter (fun d -> 
				      print_endline (Diff.string_of_diff d);
				      print_newline ()
				   ) ds;
			 print_endline " ++ ";
		      ) abs_patches;
	    print_endline "}}}"
	  );
	  (* we now have lists of safe updates as out itemset; create the database to
	   * mine now; we use the db.ml functions for that
	   *)
	  (*do_datamining abs_patches*)(*}}}*)
	  print_endline "[Main] filtering all safe patches."; 
	  let filtered_patches = 
	    if !do_dmine
	    then do_datamining abs_patches
	    else get_all_safe term_pairs abs_patches
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
	if !verbose
	then Diff.verbose_string_of_gtree t
	else Diff.string_of_gtree' t
    | skip when skip == view ddd -> "..."
    | gt -> raise (Match_failure (Diff.string_of_gtree' p, 604,0)) in
  let meta_strings = List.rev_map Diff.collect_metas p +> tail_flatten in
  let head = "@@\n" ^ 
    String.concat "\n" meta_strings ^
    "\n@@\n"
  in
    head ^ String.concat " " (List.map loc p) ^ "\n"

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

let rec is_subset_list l1 l2 =
  l1 = [] ||
  match l1, l2 with
    | x :: xs, y :: ys when x = y -> is_subset_list xs ys
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
let cont_match = Diff.cont_match
let exists_cont_match g p = nodes_of_graph g +> List.exists (cont_match g p) 
let (|-) g p = exists_cont_match g p

let g_glob = ref (None : (Diff.gflow * 'a) option )

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
  let follow_abs t_sub = match !g_glob with
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
  let rec loop depth env t =
    try [rev_assoc t env], env
    with Not_found ->
      let meta, id = new_meta_id ()
      in
	if depth = 0 || follow_abs t
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

let print_patterns ps =
  List.iter (function p -> 
(* 	       print_string "[[[ "; *)
	       print_endline (string_of_pattern p);
(* 	       print_endline " ]]]"; *)
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

let for_some n f ls = 
  let rec loop n ls =
    n = 0 ||
    match ls with
      | x :: xs when f x -> loop (n - 1) xs
      | _ :: xs -> loop n xs
      | [] -> false in
    loop n ls

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
  | x' :: xs' -> chop x xs'

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
  g#nodes#tolist +> List.fold_left (fun acc_trs (i,gt) -> 
				      match Diff.get_traces g sp i with
					| None -> acc_trs
					| Some trs -> trs :: acc_trs
				   ) []

(* a pattern sp is a subpattern of another sp' if all the traces of sp are contained within the traces of sp *)
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
    | x' :: xs' when Diff.can_match !!x !!x'  
	&& abstractness x <= abstractness x' -> xs'
    | x' :: xs' when Diff.find_match !!x !!x' -> xs' 
    | x' :: xs' -> chop x xs' in
  let rec (<++) p p' = p = [] || match p, p' with
    | x :: xs, ys -> let ys' = try Some (chop x ys) with Not_found -> None in
	(match ys' with
	   | None -> false
	   | Some ys' -> xs <++ ys')
    | _, _ -> false in
    sp1 <++ sp2

let filter_shorter_sub gss sub_pat pss =
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

let find_seq_patterns_new sub_pat is_frequent_sp orig_gss get_pa  =
  print_endline "[Main] growing patterns";
  reset_meta();
  let mk_pat p = [mkC("CM",[p])] in
  let (<==) sp ps gss = ps +> List.exists (function sp' -> 
					     sub_pat gss sp sp' && embedded_pattern sp sp'
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
	| p :: seq when loop seq && is_match p -> 
	    not(List.exists (function p' -> equal_pattern_term p p') seq)
	    &&
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
	     then acc_abs_P_env
	     else (pat,env, gss') :: acc_abs_P_env
	) [] in
	v_print_endline "done";
	res
    end 
  in
    (* ext1 = p1 p2  -- immediate successort *)
  let ext1 p1 p2 = 
    if p1 = [] 
    then [mkC("CM",[p2])] 
    else p1 @ [mkC("CM", [p2])] in
    (* ext2 = p1 ... p2 -- all-paths quantifier *)
  let ext2 p1 p2 = 
    if p1 = [] 
    then [mkC("CM",[p2])] 
    else p1 @ (ddd :: [mkC("CM", [p2])]) in
  let rec grow' ext p ps (p', env', gss) =
    (* flush_string "."; *)
    let ext_p = ext p p' in
    let pp' = renumber_metas_pattern ext_p in
      if !verbose then ( 
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
	  grow ps' (ext_p, env', gss)
      )
      else (
	v_print_endline "";
	ps)
  and grow ps (p, env, gss) =
    v_print_string "[Main] getting common cterms after pattern: ";
    v_print_endline (string_of_pattern p);
    let abs_P_env = 
      get_pa env
(*       +> List.filter (function (pat,env) -> *)
(* 			p = [] || *)
(*       			gss *)
(*       			+> for_some !threshold *)
(*       			  (function flows -> *)
(*       			     flows *)
(*       			     +> List.exists *)
(*       			       (function f -> *)
(*       				       f |- p && f |- mk_pat pat *)
(*       			       ) *)
(*       			  ) *)
(*       		     ) *)
    in
      v_print_endline ("done (" ^ string_of_int (List.length abs_P_env) ^ ")");
      let nextP1 = get_next abs_P_env ext1 p gss in
	(* there is no need to look for matches of "p...p'" in case
	   there were no matches of "p p'" because 
	   |- p p' => |- p...p'
	   thus, if we found a p' such that |- p p' we do not look for p ... p'
	*)
      let abs_P_env' = abs_P_env
	+> List.filter
	(fun (pat, env) -> 
	   not(nextP1 +> List.exists (function (p'', env', gss') -> pat = p''))
	) in
      let nextP2 = get_next abs_P_env' ext2 p gss in
	v_print_endline ("[Main] from pattern : " ^ string_of_pattern p);
	v_print_endline ("[Main] potential new patterns : " ^ string_of_int (
			   List.length nextP1 + List.length nextP2));
	v_print_newline ();
	let ps' = 
	  List.fold_left (fun acc_ps pair -> grow' ext1 p acc_ps pair) ps nextP1 in
	  List.fold_left (fun acc_ps pair -> grow' ext2 p acc_ps pair) ps' nextP2
  in
    grow [] ([], [], orig_gss)

let patterns_of_graph is_frequent_sp common_np g =
  if !verbose then print_endline ("[Main] considering graph with [" ^ 
				    string_of_int (List.length (concrete_of_graph g)) ^ 
				    "] cnodes");
  (*
    let pa = concrete_of_graph g in
  *)
  let ps = find_seq_patterns is_frequent_sp common_np g in
    if !verbose
    then (
      print_endline "[Main] found patterns:";    
      print_patterns ps);
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


let rm_dups_pred eq_f ls =
  print_endline "[Main] removing duplicates based on pred-eq";
  let (+++) x xs = if List.exists (function y -> eq_f x y) xs then xs else x :: xs in
    List.fold_left (fun acc_xs x -> x +++ acc_xs) [] ls

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
      if !verbose then 
	abs_P_env +> List.iter (function (gts,env) -> 
				  gts +> List.iter (function gt -> print_endline (Diff.string_of_gtree' gt)));
      abs_P_env




let common_patterns_graphs gss =
  (* detect whether a threshold was given *)
  let loc_pred = 
    if !threshold = 0
    then (
      threshold := List.length gss;
      List.for_all)
    else begin
      threshold := int_of_float (
	((float (List.length gss)) /. 100.0) *. 
	(float !threshold));
      for_some !threshold
    end in
    print_endline ("[Main] threshold is " ^ string_of_int !threshold ^
		  " of " ^ gss +> List.length +> string_of_int);
    Diff.no_occurs := !threshold;
  let subterms_lists = gss
    +> List.rev_map (function 
		       | [f] -> 
			   concrete_of_graph f
			   +> List.filter (function n -> 
					     not(Diff.is_head_node n))
		       | _ -> raise (Impossible 1)
		    )
  in
  let unique_subterms = subterms_lists 
    +> tail_flatten 
    +> Diff.rm_dub in
  let (|-) g sp = List.exists (cont_match g sp) (nodes_of_graph g) in
  let (||-) gss sp = gss +> loc_pred (function fs -> 
				   fs +> List.exists (function f -> f |- sp)
				) in
  let is_frequent_sp_some gss sp = gss ||- sp in
  let is_subpattern gss sp1 sp2 = subpattern_some gss sp1 sp2 in
  let new_get_pa = 
    function env ->
      Diff.abstract_all_terms subterms_lists unique_subterms env 
      +> List.filter (function (p,e) -> not(infeasible p))
  in
  (* let get_pa = get_common_node_patterns gss in *)
    find_seq_patterns_new is_subpattern is_frequent_sp_some gss new_get_pa
    +> rm_dups
    +> (function pss -> 
	  if !filter_patterns
	  then filter_shorter_sub gss (is_subpattern gss) pss 
	  else pss)
      
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
	  

let get_arcs g i =
  (g#successors i)#tolist

let equal_arcs arcs1 arcs2 =
  is_subset_list arcs1 arcs2 &&
    is_subset_list arcs2 arcs1

(* equality of flows *)
let equal_flows f1 f2 =
  let ns1 = f1#nodes#tolist in
  let ns2 = f2#nodes#tolist in
    (* all nodes must have same index and value *)
    is_subset_list ns1 ns2 &&
      is_subset_list ns2 ns1 
      (* arcs should also be equal, we ignore predecessors  *)
    && 
      ns1 +> List.for_all (function (i,n) -> 
			     equal_arcs (get_arcs f1 i) (get_arcs f2 i)
			  ) &&
      ns2 +> List.for_all (function (i,n) -> 
			     equal_arcs (get_arcs f1 i) (get_arcs f2 i)
			  ) 

(* given a set of patterns and a terms that have been identified as
 * belonging to a change, we wish to find the patterns that match the
 * term
 *)
let get_change_matches spatterns term =
  v_print_endline "[Main] getting patterns that relate to: ";
  v_print_endline (Diff.string_of_gtree' term);
  spatterns +> List.filter 
    (function spat ->
       (* recall that spat is a list of term-patterns *)
       spat 
       +> List.filter (function p -> match view p with 
			 | C("CM",[p]) -> true 
			 | _ -> false) 
       +> List.exists (function p -> Diff.can_match (extract_pat p) term)
    ) 

(* given a set of patterns and a set of terms that have been identified as
 * belonging to a change, we wish to find the patterns that match any of the
 * terms
 *)
let get_change_matches_terms spatterns terms =
  v_print_endline "[Main] filtering patterns that are related to changed terms";
  let changes = terms 
    +> List.rev_map (get_change_matches spatterns) in
  let tmp = tail_flatten changes in
  let tmp1 = rm_dups tmp in
    tmp1


(* filter_changed uses the "flow-changes" information to extract a list of terms
 * that it thinks have changed or are related to a change to filter out patterns
 * match at least one of those terms
 *)
let filter_changed gss gpats = 
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
  let res = 
    List.rev_map (fun ((gt,flows), (gt',flows')) -> 
		    if !only_changes 
		    then
		      let filtered_lhs_flows = flows +> List.filter 
			(function f -> 
			   (* is f changed in RHS ? *)
			   let f_name = try get_fun_name_gflow f 
			   with Not_found -> 
			     raise (Diff.Fail ("function not found")) 
			   in
			     if not(flows' +> List.exists (equal_flows f))
			     then (
			       print_endline ("[Main] function " ^ f_name ^ " changed");
			       true)
			     else (
			       false
			     )
			)
		      in
			filtered_lhs_flows
		    else flows
		 ) term_pairs
  in
    res 
    +> List.rev_map 
      (function flows -> 
	 flows +> List.rev_map 
	   (function f -> [f])
      ) 
    +> tail_flatten

(* at this point we have a set/list of spatterns that we know to match
   on some term that is believed to have been involved in a change; the
   function is_freq determines whether a node-term is frequent in the RHS
   graphs *)
let rec get_context_point chunk =
  match chunk with
    | [] -> raise (Diff.Fail "no context point?")
    | Difftype.ADD _ :: chunk -> get_context_point chunk
    | c :: _ -> c

let construct_spatches patterns is_freq =
  (* let local_extract diff = *)
  (*   let local i = match i with *)
  (*     | Difftype.ID (i,t) -> Difftype.ID t *)
  (*     | Difftype.ADD (i,t) -> Difftype.ADD t *)
  (*     | Difftype.RM (i,t) -> Difftype.RM t in *)
  (*     List.map local diff in *)
    (* The idea is to refine a spatch given a chunk under a certain
     * environment. What kinds of chunks are there and what are appropriate
     * actions for them?
     * chunk ::= (+t)* (-t | t) (+t)* 
     * All additions can be selected for inclusion so for each chunk we need
     * to construct a list of potential chunks to build from
     * *)
  let use_chunk chunk = 
    let suffix_all res e =
      if res = [] 
      then [[e]]
      else
        res +> List.fold_left (fun res ls -> 
				 ((e :: List.rev ls)
				  +> List.rev)
				 :: res
			      ) []
    in
      (* results is a list of chunks to include/use/apply *)
    let rec loop chunk results =
      match chunk with
	| [] -> results
	| ((Difftype.ID _ | Difftype.RM _) as m) :: chunk -> loop chunk (suffix_all results m)
	| m :: chunk -> 
            let results' = 
              suffix_all results m 
              +> List.rev_append results in 
              loop chunk results'
    in
      loop chunk [] in
  let rec get_before chunk =
    match chunk with
      | [] -> []
      | (Difftype.ID _ | Difftype.RM _) :: _ -> []
      | a :: chunk -> a :: get_before chunk
  in
    (* assume that there is always a context-point in a chunk *)
  let rec get_after chunk =
    match chunk with
      | [] -> []
      | Difftype.ADD _ :: chunk -> get_after chunk
      | (Difftype.ID _ | Difftype.RM _) :: chunk ->  chunk
      | _ -> raise (Impossible 3)
  in
    (* the following function does the real work: given a spatch, an env,
     * and a chunk it finds the context-point of the chunk and inserts the
     * modifications mentioned in the chunk based on the environment given;
     * the result is a new spatch + env and the old one is not preserved *)
  let apply_chunk_one chunk (acc_spatch, env) = 
    (* find context point in chunk *)
    let chunk_context_point = get_context_point chunk in
    let before_ops = get_before chunk in
    let after_ops  = get_after chunk in
      (* look for the (could there be more than one?) context point in
       * the spatch and decide whether it has already been handled
       * it it has not, insert the operations mentioned in the chunk
       * operations are "before" "at" "after"
       *)
    let has_been_modified pp chunk_context =
      match pp with
	| Difftype.ID _ -> false
	| _ -> true 
	    (* TODO ; need to mark prev. modifications or use
	       safe_part filter *) in
    let at_context_point pp chunk_context env =
      match pp, chunk_context_point with
	| (Difftype.ID p | Difftype.RM p) , (Difftype.ID t | Difftype.RM t) -> 
	    (try Some (Diff.match_term (extract_pat p) t) with _ -> None) 
	| _ -> raise (Impossible 4) 
    in
    let embed_context_point pp chunk_context_point =
      match pp, chunk_context_point with
	| Difftype.ID p, Difftype.ID _ -> Difftype.ID p
	| Difftype.ID p, Difftype.RM _ -> Difftype.RM p
	| _, _ -> raise (Diff.Fail ("pp not Difftype.ID"))  in
    let rec insert_ops env suffix iops = 
      match iops with
	| [] -> suffix
	| Difftype.ADD t :: iops -> 
	    insert_ops env (Difftype.ADD (Diff.rev_sub env t) :: suffix) iops 
	| _ -> raise (Impossible 5)
    in
    let rec loop prefix_spatch suffix_spatch =
      match suffix_spatch with
	| [] -> (List.rev prefix_spatch, [])
	| ((Difftype.ID p | Difftype.RM p) as pp) :: suffix_spatch ->
	    (
	      match at_context_point pp chunk_context_point env
	      with
		| None -> loop (pp :: prefix_spatch) suffix_spatch
		| Some env' ->
		    if has_been_modified pp chunk_context_point
		    then 
		      (* assume that a context point should
		       * only match in one patch point
		       *)
		      ((List.rev prefix_spatch) @ (pp :: suffix_spatch)), []
		    else 
	 	      (* insert operations *)
		      (List.rev (insert_ops env' prefix_spatch (List.rev before_ops))) 
		      @ (embed_context_point pp chunk_context_point
			 :: (insert_ops env' suffix_spatch (List.rev after_ops)))
			, env' 
	    )
	| i :: suffix_spatch -> loop (i :: prefix_spatch) suffix_spatch
    in
      loop [] acc_spatch 
  in
  let is_pattern_diff sp = sp +> List.for_all 
    (function p ->
       match p with
	 | Difftype.ID _ -> true
	 | _ -> false
    ) in
  let apply_chunk acc_spatch_env chunk =
    acc_spatch_env +> List.fold_left 
      (fun acc_spatch_env sp_e -> 
	 let (sp, env) = apply_chunk_one chunk sp_e in
	   if is_pattern_diff sp
	   then acc_spatch_env
	   else 
	     if acc_spatch_env +> 
	       List.exists (function (sp',_) ->
			      sp = sp'
			   )
	     then acc_spatch_env
	     else (sp, env) :: acc_spatch_env
      )
      acc_spatch_env in
  let is_transformation_chunk chunk = 
    match chunk with
      | [Difftype.ID _] -> false
      | _ -> true in
    (* this function uses the above _one version to iterate over all
     * spatches given a chunk; it does NOT preserve the already given based
     * on the intuition that we already given the spatch_construct functions
     * more patterns than needed???
     *)
  let build_from_chunk spatches_env chunk = 
    let potential_chunks = use_chunk chunk  in
      v_print_endline ("[Main] potential chunks: " ^
		       List.length potential_chunks +> string_of_int);
      potential_chunks +> List.iter (function diff -> 
				       v_print_endline "[Chunk]";
				       v_print_endline (diff 
						      +> List.map Diff.string_of_diff
						      +> String.concat "\n");
				       v_print_endline "[End]"
				    );
      potential_chunks 
      +> List.filter is_transformation_chunk
      +> List.fold_left apply_chunk spatches_env
  in 
    print_endline "[Main] constructing semantic patches";
    let chunks = 
      !Diff.flow_changes +>
	List.fold_left (fun acc_chunks_lists diff ->
			  List.rev_append 
			    (Diff.chunks_of_diff diff)
			    acc_chunks_lists) [] in
      (* chunks is now a list of (+t)*(t|-t)(+t)* diffs; for each chunk we
       * can extract the context/attachment-point (t|-t) which is to be found
       * in some pattern ...
       *)
    let good_chunks = chunks 
      +> List.filter (function diff -> match diff with 
			| [Difftype.ID _] -> false
			| _ -> true)
      +> List.filter (function diff -> match get_context_point diff with
			| Difftype.ID context_point 
			| Difftype.RM context_point -> 
			    (* does the context-point match anything in at least some pattern *)
			    not(get_change_matches patterns context_point = [])
			| _ -> raise (Impossible 6)
		     )
      +> List.rev_map (function chunk -> 
			 chunk +> List.filter (function it -> match it with
						 | Difftype.ADD t -> is_freq t
						 | _ -> true))
    in
      good_chunks  
      +> List.iter (function diff -> 
		      v_print_endline "[Chunk]";
		      v_print_endline (diff 
				     +> List.map Diff.string_of_diff
				     +> String.concat "\n");
		      v_print_endline "[End]"
                   );
      (* for each pattern, we wish to try and construct a (or many) spatch
       * from it; we iterate over each chunk to try and see whether the chunk
       * allows us to add rm/add instructions to the pattern
       *)
      v_print_endline "[Main] making init_spatches";
      let init_spatches_env = 
	patterns 
	+> List.rev_map (function sp -> 
			   sp +> List.map (function p -> Difftype.ID p), []) in
	v_print_endline ("[Main] building spatches based on " ^
			 List.length good_chunks +> string_of_int 
		       ^ " chunks");
	let spatches_env =
	  good_chunks 
	  +> List.fold_left 
	    (fun acc_spatch_env chunk -> 
               build_from_chunk acc_spatch_env chunk) 
	    init_spatches_env
	    (*
	      +> rm_dups_pred (fun (sp,_) (sp', _) -> sp = sp')
	    *)
	in
	  print_endline ("[Main] *CANDIDATE* semantic patches inferred: " ^ 
			   List.length spatches_env +> string_of_int);
	  spatches_env 
	  +> List.iter (function diff, env -> 
			  print_endline "[spatch:]";
			  print_endline (diff 
					 +> List.map Diff.string_of_diff
					 +> String.concat "\n");
                       );
	  List.rev_map fst spatches_env


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

(* this function takes a CFG for a function def and a node within that
   flow and returns the path from the root to the node (both nodes
   included); a path is a list of node-indices excluding "phony" nodes
*)

let is_exit_node t = match view t with
  | C("head:dowhiletail", _)
  | A("head:seqend",_) -> true
  | _ -> false

let get_path g n = 
  let path = ref [] in
  let f xi path' = 
    if xi = n then path := xi :: path' in
    Ograph_extended.dfs_iter_with_path 0 f g;
    !path 
    +> List.filter (function xi -> 
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
    trace +> List.fold_left anno_seq spatch

exception LocateSubterm 
exception Next of int list 


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
	       | C("macroit",      [{Hashcons.node=C(t_name, [st])}]), 
		 C("head:macroit", [{Hashcons.node=C(g_name, _)}]) when t_name = g_name ->
		   (match next_node_val with
		      | None -> raise (Diff.Fail "no next control node val: InLoop could have been expected")
		      | Some control_node ->
			  if control_node = Diff.control_inloop
			  then
			    Some([st], 
				 (function 
				    | [st'] -> 
					mkC("macroit",[mkC(t_name, [st'])]) +> s_func
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
			  else (* select true branch and do not consume node from path *)
			    Some([t],(function 
					| [t] -> mkC("if", [b;t;f]) +> s_func
					| _ -> raise (Impossible 12))) +> same_path
		   )
	       | C("switch",[e;s]), C("head:switch", [e']) when e = e' ->
		   Some ([s], function s' ->
			   mkC("switch", e :: s') +> s_func) +> same_path
	       | C("while",[e;s]), C("head:while", _) ->
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
	       | C("dowhile", [s;e]), C("head:do", [e']) when e = e' ->
		   Some ([s], (function s' ->
				 mkC("dowhile", s' @ [e]) +> s_func)) +> same_path
	       | C("for", [e1;e2;e3;st]), C("head:for", _) ->
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
			   mkC("caseRage", e1 :: e2 :: st') +> s_func) +> same_path
	       | C("labeled", [{Hashcons.node=A("lname", s_lab)} as l; st]), 
		   A("head:label", lab) ->
		   Some ([st], function 
			   | [st] -> mkC("labeled", [l; st]) +> s_func
			   | _ -> raise (Impossible 14)) +> same_path
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


let locate_subterm g orig_subterm path f =
  let extract_label t = 
    match view t with 
      | C("stmt", [
	    {Hashcons.node=A("goto", lab)}
	  ]) -> Some lab
      | _ -> None
  in
  let pathht = Hashtbl.create 101 in
  let get_val n = 
    try 
      Hashtbl.find pathht n
    with Not_found ->
      let res = Diff.get_val n g in
	(
	  Hashtbl.add pathht n res;
	  res
	) in
    v_print_string "[Main] looking in ";
    v_print_endline (Diff.verbose_string_of_gtree orig_subterm);
    v_print_string "[Main] path ";
    v_print_endline (path +> List.map string_of_int +> String.concat " ");
    let last = List.nth path (List.length path - 1) in
      v_print_string "[Main] looking for:";
      v_print_endline (get_val last +> Diff.verbose_string_of_gtree);

      let is_typed e = match view e with
	| C("TYPEDEXP", _) -> true
	| _ -> false in
      let rec (===) t1 t2 = match view t1, view t2 with
	| C("pending", ot :: _ ), _ -> ot === t2
	| C("stmt",[s]), (C("dlist", _) | C("mdecl", _)) ->  s === t2
	| C("exp",[te;e]), C("exp", [e']) when is_typed te -> e === e'
	| C(ty1,ts1), C(ty2,ts2) when ty1 = ty2 ->
	    (try 
	       List.for_all2 (===) ts1 ts2
	     with Invalid_argument e -> (
	       print_endline "ts1";
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
      let get_next_node_val path = match path with
	| [] -> None
	| n :: _ -> Some (get_val n) in
      let rec loop subterm path =
	match path with
	  | [] -> (raise LocateSubterm)
	  | [n] -> 
	      let node_term = get_val n in
		if is_at_context node_term subterm
		then f node_term (* subterm -- can the subterm can have more info than the node-term ? *)
		else (raise LocateSubterm)
	  | n' :: path -> 
	      let t = get_val n' 
	      in 
		if subterm === t
		then 
		  (match extract_label t with
		     | Some lab -> raise (Goto (lab, path))
		     | None     -> raise (Next path)
		  )
		else
		  (
		    match corresponds subterm t (get_next_node_val path) path  with
		      | None -> (raise LocateSubterm)
		      | Some (ts, ins_f, new_path) ->
			  (ts *> loop) new_path 
			  +> ins_f
		  ) 
      and locate_label (lab, path) t =
	match view t with 
	  | C("stmt", [
		{Hashcons.node=C("labeled", [
				   {Hashcons.node=A("lname",lab') }; _])}
	      ]) 
	      when lab = lab' -> loop t path
	  | C(ty, ts) -> 
	      let ts' = iterate_lab ts loop locate_label (lab, path)
	      in mkC(ty,ts')
	  | _ -> raise (Label_not_found lab) 
      in
      let rec search_label (lab, path) =
	try locate_label (lab, path) orig_subterm
	with
	    Goto (lab', path') -> search_label (lab', path')
      in
	try loop orig_subterm path 
	with Goto (lab, path) ->
	  search_label (lab, path) 


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
    chunk +> List.map gtree_of_ann_iop
  in 
    (
      mkC("pending", subterm :: embedded_chunk)
    )

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
  (*
    print_endline "[Main] insert_chunk:";
    print_endline (chunk
    +> List.map (function iop -> match iop with
    | Difftype.ID  (p, _) -> Difftype.ID p
    | Difftype.RM  (p, _) -> Difftype.RM p
    | Difftype.ADD (p, _) -> Difftype.ADD p)  
    +> List.map Diff.string_of_diff
    +> String.concat "\n");
    print_endline "[End]";
    print_endline "[Main] into term: ";
    pending_term +> Diff.string_of_gtree' +> print_endline;
  *) 
  let ctx_point_nodes = match get_context_point chunk with
    | Difftype.ID(p,is) | Difftype.RM(p,is) -> is
    | _ -> raise (Diff.Fail "insert_chunk get_context_point") in
    (* the 'f' function is responsible to checkin chunk compatibility *)
  let f t = 
    match view t with
      | C("pending", [orig_cp; embed]) -> (
 	  print_endline "[Main] SKIPPING chunk...";
	  t)
      | _ -> pending_of_chunk chunk t in
  let paths = ctx_point_nodes +> List.rev_map (get_path flow) in
    paths +>
      List.fold_left (fun acc_t path -> 
			locate_subterm flow pending_term path f) pending_term


let perform_pending pending_term = 
  let get_env orig_cp emb =
    let ctx = 
      match List.find (function p -> match view p with 
			 | C("=",[ctx])  
			 | C("-",[ctx]) -> true
			 | _ -> false) emb +> view with
	| C("=",[p]) | C("-",[p])-> p
	| _ -> raise (Impossible 16)
    in
      Diff.match_term (extract_pat ctx) orig_cp in
  let unfold_embedded orig embs = 
    let env = get_env orig embs in
      List.fold_right 
	(fun emiop res_ts -> 
	   match view emiop with
	     | C("=", [p]) -> (orig :: res_ts) (* should be able to assert(Diff.rev_sub env p = orig *)
	     | C("-", [p]) -> (res_ts) (* should be able to assert(Diff.rev_sub env p = orig *)
	     | C("+", [p]) -> (
		 let interm = Diff.sub env p in
		   interm :: res_ts)
	     | _ -> raise (Impossible 17)

	) embs []
  in
  let rec loop t = match view t with
    | C("pending", orig_cp :: embedded) -> unfold_embedded orig_cp embedded
    | C(ty, ts) -> 
	let ts' = ts 
	  +> List.rev_map loop 
	  +> List.rev
	  +> List.flatten
	in [mkC(ty, ts')]
    | _ -> [t] in
    match loop pending_term with
      | [t'] -> t'
      | _ -> raise (Diff.Fail "perform pending error")
	  

(* this function applies a semantic patch to a term given a flow representing the term; the idea is to do the following
   - extract the pattern from the spatch
   - match the pattern with the flow and collect the traces

   - use the traces to annotate the spatch (notice there can be
   several annotated spatches when the pattern matches in more than
   one node; however, notice by the shortest-paths semantics of
   ... that the same pattern can not have overlapping matches

   - for each anno_spatch: split in chunks
   - for each set of chunks (corresponding to one anno_spatch)
   => for each chunk
   o  locate the chunk in the lhs_term
   o  insert application information from chunk
   
   - once all chunks in all chunk-set have been handled, perform
   transformations mentioned in the inserted chunks
*)
	  
let apply_spatch spatch (term,flow) = 
  let pattern = List.fold_right (fun iop acc_pattern -> match iop with
				   | Difftype.ID p | Difftype.RM p -> p :: acc_pattern
				   | Difftype.ADD _ -> acc_pattern
				   | _ -> raise (Impossible 16)
				) spatch [] in
  let traces = get_pattern_traces flow pattern in
  let stripped_spatch = spatch +> List.filter 
    (function iop -> match iop with
       | Difftype.ID p when p ==  ddd -> false
       | _ -> true) in
  let init_annotated = stripped_spatch +> List.map (function iop -> match iop with
						      | Difftype.ID p -> Difftype.ID (p, empty_annotation)
						      | Difftype.RM p -> Difftype.RM (p, empty_annotation)
						      | Difftype.ADD p -> Difftype.ADD (p, empty_annotation)
						      | _ -> raise (Impossible 17)) in
  
  let annotated_spatches = traces +> List.map (annotate_spatch init_annotated) in
  let chunkified_spatches = annotated_spatches +> List.rev_map Diff.chunks_of_diff in
  let pending_term = chunkified_spatches +> 
    List.fold_left (fun acc_pending_term chunk_set -> 
		      chunk_set +> List.fold_left (insert_chunk flow) acc_pending_term
		   ) term in
    perform_pending pending_term


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
				   | Difftype.ID p | Difftype.RM p -> p :: acc_pattern
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
  let patched_lhss = funs +> List.map (function (fname, flow, lhs_def_term, rhs_def_term) ->
					 (lhs_def_term, 
					  apply_spatch spatch (lhs_def_term, flow), 
					  rhs_def_term)
				      ) in
    (* check safety of result *)
    v_print_string "safety check: ";
    spatch +> List.map Diff.string_of_diff +> String.concat " " +> v_print_endline;
    patched_lhss +> List.exists (function (left,middle,right) -> 
				   v_print_endline ("t1\t" ^ Diff.string_of_gtree' left);
				   v_print_endline ("t2\t" ^ Diff.string_of_gtree' middle);
				   v_print_endline ("t3\t" ^ Diff.string_of_gtree' right);
				   if Diff.part_of_edit_dist left middle right
				     (* if Diff.msa_cost left middle right *)
				   then (v_print_endline "ok"; true)
				   else (v_print_endline "unsafe"; false)
				)

(* decide whether sp1 <= ttf_list *)
let is_spatch_safe_ttf_list sp ttf_list =
  v_print_endline "[Main] considering safety of:";
  sp +>
    List.iter (function p -> 
  		 Diff.string_of_diff p +> v_print_endline
  	      );
  ttf_list +> for_some !threshold (function ttf ->
				     is_spatch_safe_one ttf sp
				  )

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
					  apply_spatch spatch (lhs_def_term, flow), 
					  rhs_def_term)
				      ) in
    patched_lhss


(* decide whether sp1 <= sp2 relative to ttf_list *)
let get_largest_spatchs ttf_list spatches =
  (* - for spatch
     -- for each triple (lhs,rhs,flows) produce 
     [ (f_lhs, f_mhs) | f_lhs ∈ lhs, [[spatch]](f_lhs) = f_mhs ]
     - we can then produce a list indexed by spatches:
     [ (spatch, [(lhs, [(f_lhs, f_mhs) | f_lhs ∈ lhs, [[spatch]](f_lhs)=f_mhs] ) | (lhs,rhs,flows) ∈ ttf_list]
     we denote this list "applied_spatches"
     - now sp1 ≼ sp2 (relative to t1,t2,t3) iff
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
  v_print_endline "[Main] applying spatches";
  let applied_spatches = spatches
    +> List.rev_map 
    (function sp -> 
       sp,
       ttf_list +> 
	 List.rev_map 
	 (function (lhs,rhs,flows)  ->
	    lhs, apply_spatch_ttf sp (lhs,rhs,flows)
	 )
    )
  in
  let is_sub lhss_fmlists1 lhss_fmlists2 = 
    lhss_fmlists2 +> for_some !threshold 
      (function (lhs2, fm_lists2) ->
	 try
	   let (_, fm_lists1) = List.find (function (lhs1, _) -> lhs1 = lhs2) lhss_fmlists1 in
	     fm_lists2 +> List.for_all
	       (function (f2,m2,_) ->
		  try
		    let (_, m1, _) = List.find (function (f1,m1,r1) -> f1 = f2) fm_lists1 in
		      Diff.part_of_edit_dist f2 m1 m2
			(* Diff.msa_cost f2 m1 m2 *)
		  with Not_found -> 
		    (v_print_endline  ("Not finding: " ^ Diff.string_of_gtree' f2);
		     raise Not_found)
	       )
	 with Not_found -> false
      )
  in
    (* the largest spatches are those for which all others are either smaller or not-comparable *)
    applied_spatches 
    +> List.rev_map
      (function (sp, lhs_fmlists) ->
	 v_print_endline "[Main] testing one for largest:";
	 v_print_endline (sp
			  +> List.map Diff.string_of_spdiff
			  +> String.concat "\n");
	 
	 if applied_spatches +> List.for_all (function (sp', lhs_fmlists') ->
						v_print_endline "[Main] against : ";
						v_print_endline (sp'
								 +> List.map Diff.string_of_spdiff
								 +> String.concat "\n");
						
						is_sub lhs_fmlists' lhs_fmlists ||
						  not(is_sub lhs_fmlists lhs_fmlists')
					     )
	 then
	   (
	     v_print_endline "[Main] including as largest: ";
	     Some sp 
	   )
	 else (
	   v_print_endline "[Main] not largest";
	   None
	 )
      )
    +> List.fold_left (fun acc opt -> match opt with Some sp -> 
			 sp :: acc | _ -> acc) []


let find_common_patterns () =
  malign := true;
  Diff.malign_mode := true;
  read_spec(); (* gets names to process in file_pairs *)
  let term_pairs = List.rev (
    List.fold_left (fun acc_pairs (lfile, rfile) ->
		      read_filepair_cfg lfile rfile :: acc_pairs
		   ) [] !file_pairs) in
    print_endline ("[Main] read " ^ string_of_int (List.length term_pairs) ^ " files");
    let gss = lhs_flows_of_term_pairs term_pairs in
    let gss_rhs = List.rev_map (fun (_, (gt',flows)) -> flows) term_pairs in
    let gpats'' = common_patterns_graphs gss in
    let gpats' = filter_changed gss_rhs gpats'' in
      if List.length gpats' = 0
      then print_endline "[Main] *NO* common patterns found"
      else begin
	print_endline "[Main] *Common* patterns found:";
	print_patterns gpats';
      end;
      if not(!patterns)
      then begin
	print_endline "[Main] getting rhs flows";
	let rhs_flows = get_rhs_flows term_pairs in
	  print_endline "[Main] getting COMMON rhs node-patterns";
	  let common_rhs_node_patterns = get_common_node_patterns rhs_flows [] in
	  let is_freq t = common_rhs_node_patterns +> 
	    List.exists (function (gts,env) -> 
			   gts +> List.exists (function cmp -> Diff.can_match cmp t)
			) 
	  in
	  let sp_candidates = construct_spatches gpats' is_freq in
	  let ttf_list = term_pairs +> List.rev_map (function ((lhs_gt, lhs_flows),(rhs_gt,_)) -> 
						       (lhs_gt, rhs_gt, lhs_flows)
						    ) in
	  let is_transformation_sp sp = 
	    sp +> List.exists (function p ->
				 match p with
				   | Difftype.ID _ -> false
				   | _ -> true) in
	  let trans_patches = sp_candidates +> List.filter is_transformation_sp in
	    print_endline ("[Main] filtering safe semantic patches ("^ trans_patches +> 
	    		     List.length +> 
			     string_of_int ^")");
	    let res_spatches = 
	      trans_patches
	      +> List.filter (function sp -> is_spatch_safe_ttf_list sp ttf_list)
	    in
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
					       +> List.map Diff.string_of_spdiff
					       +> String.concat "\n");
			     )
      end		  
		  
		  
let main () =
  (* decide which mode to operate in *)
  Arg.parse speclist (function _ -> ()) "Usage: ";
  Diff.be_strict     := !strict;
  Diff.use_mvars     := !mvars;
  Diff.be_fixed      := !fixed;
  Diff.no_exceptions := !exceptions;
  Diff.verbose       := !verbose;
  Diff.nesting_depth := !nesting_depth;
  Diff.malign_mode   := !malign;
  Diff.patterns      := !patterns;
  Diff.abs_subterms  := !max_level;

  if !Config.std_h <> "" then
    (print_endline ("[Main] have std.h file: " ^ !Config.std_h);
     Parse_c.init_defs !Config.std_h
    );
  if !threshold = 0 then do_dmine := false;
  if !mfile = ""
  then raise (Diff.Fail "No specfile given")
  else if !spatch || !patterns
  then find_common_patterns ()
  else spec_main ()


let _ = main()

