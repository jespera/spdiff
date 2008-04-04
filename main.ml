(* this is the main file for the spfind CFU program
 *)

let src_file     = ref ""
let tgt_file     = ref ""
let toprint      = ref false
let mk_closed    = ref false
let abs          = ref false
let spec         = ref false
let mfile        = ref ""
let our_level    = ref 0
let max_level    = ref 10
let depth        = ref 0
let strict       = ref false
let mvars        = ref false
let fixed        = ref false
let exceptions   = ref 0 
let print_close  = ref false
let print_raw    = ref false
let print_uniq   = ref false 
let print_adding = ref false

let speclist =
  Arg.align
    ["-src",           Arg.Set_string src_file, "str   gives the name of the src file";
     "-tgt",           Arg.Set_string tgt_file, "str   gives the name of the tgt file";
     "-mk_closed",     Arg.Set mk_closed,       "bool  indicates that we should also produce the closed db";
     "-print",         Arg.Set toprint,         "bool  indicates printing of the (non-closed) db";
     "-abs",           Arg.Set abs,             "bool  indicates whether to perform meta-variable abstraction";
     "-specfile",      Arg.Set_string mfile,    "str   name of specification file";
     "-level",         Arg.Set_int our_level,   "int   terms larger than this will not be abstracted";
     "-top",           Arg.Set_int max_level,   "int   terms larger than this will not have subterms abstracted";
     "-depth",         Arg.Set_int depth,       "int   recursion depth at which we still abstract terms";
     "-strict",        Arg.Set strict,          "bool  strict: fv(lhs) = fv(rhs) or nonstrict(default): fv(rhs)<=fv(lhs)";
     "-multiple",      Arg.Set mvars,           "bool  allow equal terms to have different metas";
     "-fixed",         Arg.Set fixed,           "bool  never abstract fixed terms";
     "-exceptions",    Arg.Set_int exceptions,  "int   the number of allowed exceptions to the rule derived";
     "-print_close",   Arg.Set print_close,     "bool  whether to close the resulting mined database (default: no)";
     "-noif0_passing", Arg.Clear Flag_parsing_c.if0_passing, "bool  also parse if0 blocks";
     "-print_abs",     Arg.Set Diff.print_abs,  "bool  print abstract updates for each term pair";
     "-relax_safe",    Arg.Set Diff.relax,      "bool  consider non-application safe";
     "-print_raw",     Arg.Set print_raw,       "bool  print the raw list of generated simple updates";
     "-print_uniq",    Arg.Set print_uniq,      "bool  print the unique solutions before removing smaller ones";
     "-print_add",     Arg.Set print_adding,    "bool  print statement when adding a new solution in generate_sol"
  ]

let old_main () =
  (* read the sources *)
  print_string "Reading and parsing and converting files...";
  flush stdout;
  let gt1, gt2 = Diff.read_src_tgt !src_file !tgt_file in
  print_endline "done.";
  print_endline "gt1:";
  print_endline (Diff.string_of_gtree Diff.str_of_ctype Diff.str_of_catom gt1);
  print_endline "gt2:";
  print_endline (Diff.string_of_gtree Diff.str_of_ctype Diff.str_of_catom gt2);
  (* produce the list of solutions *)
  print_endline "Making (unabs) solutions...";
  let sols = Diff.unabstracted_sol gt1 gt2 in
  print_endline "done.";
  Diff.print_sols sols

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

let get_best_itemset ndb =
	let supp b = Diff.DBD.get_support_itemset ndb b in
	let f acc_itemset itemset =
	if supp itemset >= supp acc_itemset &&
	   List.length itemset >= List.length acc_itemset
		 then itemset
		 else acc_itemset in
  Diff.DBD.fold_itemset ndb f [] 

let do_datamining abs_patches =
  let edb = Diff.DBD.makeEmpty () in
  print_endline "[Main] Constructing database...";
  let fdb = List.fold_left Diff.DBD.add_itemset edb abs_patches in
  let threshold = List.length abs_patches in
  print_endline ("[Main] Mining using minimum support: " ^
  string_of_int (threshold - !exceptions));
  print_endline ("[Main] initial db size " ^ string_of_int (Diff.DBD.sizeOf fdb));
  let mfunc = if !mk_closed then 
    (print_endline "[Main] using closed sub-itemsets";
    Diff.DBD.dmine_cls)
    else Diff.DBD.dmine in
  let cdb = mfunc fdb (threshold - !exceptions) in
  (* close the database occording to command line prefs *)
  (*
  let cdb = if !close then (
    print_endline "[Mine] closing";
    Diff.DBD.close_db fdb rdb)
    else rdb in
  (*print_endline "[Main] resulting database";*)
  (*Diff.DBD.print_db*)
    (*Diff.string_of_diff*)
    (*cdb;*)
  *)
(*
  print_endline "[Main] resulting database";
  Diff.DBD.print_db
   Diff.string_of_diff
    cdb;
*)
	get_best_itemset cdb
(*
  print_endline "[Main] done mining; merging...";
  let f = fun acc itemset -> Diff.non_dub_app itemset  acc in
  Diff.DBD.fold_itemset cdb f []
*)
  

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

(* there may be solutions that are smaller than others as illustrated
   by the following update:

   (f(1)+a)+a) -> (f(2)+b)+b

   here we would have both f(1)->f(2) and f(1)+a -> f(2)+b in the
   generated results; we notice that neither can be applied together,
   so we need to separate them in two solutions. Thus, we have
   f(1)->f(2) <= f(1)+a -> f(2)+b.

   Clearly, we should remove the smaller solutions from the list.
*)

let filter_smaller chgset solutions =
  (* turn the lists into SEQ-bps *)
  (*let bp_sols = List.map bp_of_list solutions in*)
    (* predicate for when to keep a solution: if all other solutions are
       smaller *)
  let keep_sol bp = 
    List.for_all
      (function bp' -> 
        Diff.subpatch_changeset chgset bp' bp &&
        Difftype.csize bp' <= Difftype.csize bp
      )
      solutions in
    (*print_string "[Main] filter_small considering ";*)
    (*print_string (string_of_int (List.length solutions));*)
    (*print_endline " solutions";*)
    (*List.map list_of_bp *)
    (List.filter keep_sol solutions)


let generate_sols chgset_orig simple_patches =
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
          try app_pred cur_bp bp with Diff.Nomatch -> false) 
            (restrict_bps cur_bp bps) in
        (*print_endline "[Updates added";*)
        (*List.iter (function bp -> print_endline ("\t"^Diff.string_of_diff bp)) res;*)
        res
    )
    in
  let add_sol cur_bp sol = 
    match cur_bp with 
    | None -> 
        print_endline "[Main] no solutions?";
        []
    | Some cur_bp -> (
        if !print_adding
        then (
          print_string "[Main] trying solution... ";
          flush stdout;
          (*print_endline (Diff.string_of_diff cur_bp)*)
        );
        let res = filter_smaller chgset_orig (filter_redundant (cur_bp :: sol))
        in
        if !print_adding
        then print_endline "done";
        res
      ) in
  let isComplete bp = Diff.complete_changeset 
    chgset_orig (list_of_bp bp) in
  let rec gen sol bps cur_bp =
    if try isComplete (unwrap cur_bp) with _ -> false
    then add_sol cur_bp sol
    else
      let bps' = next_bps bps cur_bp in
      if bps' = []
      then add_sol cur_bp sol
      else
        (
          (*print_endline ("[Main] bps'.length " ^*)
            (*string_of_int (List.length bps'));*)
          List.fold_left (fun sol bp ->
            let nbp = extend_bp cur_bp bp in
            (* let nbps = restrict_bps (unwrap nbp) bps in *)
            (* gen sol nbps nbp *)
            gen sol bps' nbp (* maybe s/bps/bps' for efficiency? *)
          ) sol bps'
        )
  in
  if simple_patches = []
  then (
    print_endline "[Main] no input to work with";
    [])
  else
    List.map list_of_bp (gen [] simple_patches None)



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

let spec_main () =
  Diff.abs_depth     := !depth;
  Diff.abs_threshold := !our_level;
  Diff.abs_subterms  := !max_level;
  read_spec(); (* gets names to process in file_pairs *)
  (* now make diff-pairs is a list of abs-term pairs *)
  let term_pairs = List.rev (
    List.fold_left (fun acc_pairs (lfile, rfile) ->
      read_filepair lfile rfile :: acc_pairs
    ) [] !file_pairs) in
  (* we must now find the frequent subterms; 
   * that is, the subterms that occur in all term pair LHS'es *)
  (* {{{  Common subterms printing *)
  Diff.fdebug_string !Diff.print_abs "[Main] Common subterms: ";
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
    if !mk_closed
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
  let solutions = generate_sols term_pairs filtered_patches in
  print_sols solutions
  (*
  let uniq_sols = filter_redundant solutions in
    print_string "[Main] filtered ";
    print_string (string_of_int (List.length solutions - List.length uniq_sols));
    print_string " solutions of ";
    print_string (string_of_int (List.length solutions));
    print_endline " possible";
    if !print_uniq then (
      print_endline "[Main] printing unique solutions";
      print_sols uniq_sols
    );
    print_endline "[Main] removing smaller solutions";
    let subsumed_sols = filter_smaller term_pairs uniq_sols in
      print_string "[Main] removed ";
      print_string (string_of_int (List.length uniq_sols - List.length subsumed_sols));
      print_endline " smaller patches";
      print_sols subsumed_sols
*)

let main () =
  (* decide which mode to operate in *)
  Arg.parse speclist (function _ -> ()) "Usage: ";
  Diff.be_strict     := !strict;
  Diff.use_mvars     := !mvars;
  Diff.be_fixed      := !fixed;
  Diff.no_exceptions := !exceptions;
  if !mfile = ""
  then old_main ()
  else spec_main ()


let _ = main()
