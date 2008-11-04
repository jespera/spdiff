(* this is the main file for the spfind CFU program
 *)

let do_dmine     = ref false
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

let speclist =
  Arg.align
    [
      "-noncompact",    Arg.Set noncompact,      "bool  also return non-compact solutions";
      "-dmine",         Arg.Set do_dmine,        "bool  indicate to do datamining";
      "-specfile",      Arg.Set_string mfile,    "str   name of specification file";
      "-top",           Arg.Set_int max_level,   "int   terms larger than this will not have subterms abstracted";
      "-depth",         Arg.Set_int depth,       "int   recursion depth at which we still abstract terms";
      "-strict",        Arg.Set strict,          "bool  strict: fv(lhs) = fv(rhs) or nonstrict(default): fv(rhs)<=fv(lhs)";
      "-multiple",      Arg.Set mvars,           "bool  allow equal terms to have different metas";
      "-fixed",         Arg.Set fixed,           "bool  never abstract fixed terms";
      "-exceptions",    Arg.Set_int exceptions,  "int   the number of allowed exceptions to the rule derived";
      "-threshold",     Arg.Set_int threshold,   "int   the minimum number of occurrences required";
      "-noif0_passing", Arg.Clear Flag_parsing_c.if0_passing, "bool  also parse if0 blocks";
      "-print_abs",     Arg.Set Diff.print_abs,  "bool  print abstract updates for each term pair";
      "-relax_safe",    Arg.Set Diff.relax,      "bool  consider non-application safe [experimental]";
      "-print_raw",     Arg.Set print_raw,       "bool  print the raw list of generated simple updates";
      "-print_uniq",    Arg.Set print_uniq,      "bool  print the unique solutions before removing smaller ones";
      "-print_add",     Arg.Set print_adding,    "bool  print statement when adding a new solution in generate_sol";
      "-prune",         Arg.Set prune,           "bool  try to prune search space by various means";
      "-strip_eq",      Arg.Set strip_eq,        "bool  use eq_classes for initial atomic patches";
      "-patterns",      Arg.Set patterns,        "bool  look for common patterns in LHS files"
  ]


let filesep = Str.regexp " +"
let file_pairs = ref []

let read_filepair old_file new_file =
  print_endline 
    ("Reading file pair " ^
    old_file ^ " " ^ new_file);
  Diff.read_src_tgt old_file new_file


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
  let restrict_bps cur_bp bps =
    List.filter (function bp ->
      not(Diff.subpatch_changeset chgset_orig bp cur_bp)
    ) bps in
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
  let isComplete bp = Diff.complete_changeset 
    chgset_orig (list_of_bp bp) in
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
      print_string "\t";
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
  List.map (fun eq_class -> List.hd eq_class) pot_res


let spec_main () =
  Diff.abs_depth     := !depth;
  Diff.abs_subterms  := !max_level;
  read_spec(); (* gets names to process in file_pairs *)
  (* now make diff-pairs is a list of abs-term pairs *)
  let term_pairs = List.rev (
    List.fold_left (fun acc_pairs (lfile, rfile) ->
      read_filepair lfile rfile :: acc_pairs
    ) [] !file_pairs) in
  (* assume that a threshold of 0 means the user did not set it
   * thus, set it to max instead 
   *)
  if !threshold = 0
  then threshold := List.length term_pairs;
  (* we must now find the frequent subterms; 
   * that is, the subterms that occur in all term pair LHS'es *)
  Diff.no_occurs := !threshold;
  (* {{{  Common subterms printing *)
  Diff.fdebug_endline !Diff.print_abs "[Main] Common subterms: ";
  let frqnt_st = Diff.make_fixed_list term_pairs in
  List.iter (function st -> 
    print_string (Diff.string_of_gtree' st);
    print_string " ") frqnt_st;
  print_newline ();
  (* }}} *)
  let fixf = Diff.list_fixed frqnt_st in
  (*let terms_changed_list = Diff.find_changed_terms fixf term_pairs in*)
  (*print_string "[Main] terms that changed: ";*)
  (*List.iter *)
    (*(function a -> print_string (Diff.string_of_gtree' a); print_string " ")*)
    (*terms_changed_list;*)
  (*print_newline ();*)
  (*let terms_changed = function a -> List.mem a terms_changed_list in*)
  (* now make all (relevant) term updates for each term pair *)
  print_endline (
    "[Main] Constructing all safe parts for " ^ 
    string_of_int (List.length term_pairs) ^ " term pairs");
  let tcount = ref 1 in
  let abs_patches = List.map (function (t, t'') ->
    print_endline ("[Main] Making safe parts for pair " ^ string_of_int !tcount);
    tcount := !tcount + 1;
    (* print_endline (Diff.string_of_diff (Difftype.UP(t,t'')));  *)
    let terms_changed_list = Diff.find_changed_terms_pair fixf (t,t'') in
    let terms_changed = function a -> List.mem a terms_changed_list in
    print_string "[Main] terms that changed: ";
    List.iter
      (function a -> print_string (Diff.string_of_gtree' a); print_string " ")
      terms_changed_list;
    print_newline ();
    let r = Diff.make_abs terms_changed fixf (t, t'') in
		print_endline "[Main] abstracted one pair";
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


let find_patterns_term term =
  let add_pattern pats p = match p with
    | None -> pats 
    | Some p -> match Gtree.view p with
        | Gtree.A("meta", _) -> pats
        | _ -> p :: pats in
  let subterms = Diff.make_all_subterms term in
    print_endline ("[Main] #no subterms " ^ string_of_int (List.length subterms));
    let res = List.fold_left (fun acc_pats t -> 
                                List.fold_left (fun acc_pats p ->
                                                  add_pattern acc_pats p
                                ) acc_pats (List.map (Diff.merge_patterns t) acc_pats)
    ) subterms subterms in
      Diff.reset_meta ();
      let norm_res = List.map (fun p -> fst(Diff.fold_botup p Diff.renumber_metas [])) res in 
                                                                                               List.iter (fun p -> 
                                                                                               print_endline (Diff.string_of_gtree' p)) norm_res;
                                                                                               
        norm_res

let find_common_patterns () =
  print_endline "[Main] looking for common patterns";
  read_spec(); (* gets names to process in file_pairs *)
  let term_pairs = List.rev (
    List.fold_left (fun acc_pairs (lfile, rfile) ->
      read_filepair lfile rfile :: acc_pairs
    ) [] !file_pairs) in
  print_endline ("[Main] read " ^ string_of_int (List.length term_pairs) ^ " files");
  let subterms_lists = List.map (fun (t,t') -> Diff.make_all_subterms t) term_pairs 
  in 
    print_endline ("[Main] number of subterms " ^ string_of_int (List.fold_left (+) 0 (List.map List.length subterms_lists)));
  let common_patterns = List.fold_left (fun acc_patterns subterms ->
                                          List.fold_left (fun acc_pats t -> List.rev_append (
                                                            List.map (fun (Some v) -> (Diff.reset_meta(); 
                                                                                       fst(Diff.fold_botup v Diff.renumber_metas [])
                                                                                      )
                                                            ) (
                                                            List.filter (fun t' -> match t' with
                                                                           | None -> false
                                                                           | _ -> true
                                                            ) (List.map (fun t' -> Diff.merge_patterns t t') acc_patterns)))
                                                            acc_pats
                                          ) [] subterms
  ) (List.hd subterms_lists) subterms_lists
  in
    List.iter (fun p ->
      print_endline (Diff.string_of_gtree' p)
    ) common_patterns
      


let main () =
  (* decide which mode to operate in *)
  Arg.parse speclist (function _ -> ()) "Usage: ";
  Diff.be_strict     := !strict;
  Diff.use_mvars     := !mvars;
  Diff.be_fixed      := !fixed;
  Diff.no_exceptions := !exceptions;
  if !mfile = ""
  then raise (Diff.Fail "No specfile given")
  else if !patterns 
  then find_common_patterns ()
  else spec_main ()


let _ = main()
