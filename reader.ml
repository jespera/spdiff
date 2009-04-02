(* This module is used to read specfiles and read the individual files
   mentioned in a specfile.

   It also takes care of mapping function definitions in LHS to the
   most similar in RHS.
*)



open Hashcons
open Gtree
open Db
open Difftype

type term = gtree
type up = term diff

type node = gtree
type edge = Control_flow_c2.edge

type gflow = (node, edge) Ograph_extended.ograph_mutable


let v_print s = if !Jconfig.verbose then (print_string s; flush stdout)
let v_print_string = v_print
let v_print_endline s = if !Jconfig.verbose then print_endline s
let v_print_newline () = v_print_endline ""


let do_option f a =
  match a with 
    | None -> ()
    | Some v -> f v

let (+>) o f = f o

(* separator for files is at least one SPACE (not tabs) *)
let filesep = Str.regexp " +"


let get_fname_ast gt = match view gt with
  | C("def", gt_name :: _ ) -> (
      match view gt_name with 
	| A("fname", name) -> name
	| _ -> raise (Diff.Fail "no fname!")
    )
  | _ -> raise (Diff.Fail "no fname!!")

let gtree_of_ast_c parsed = Visitor_j.trans_prg2 parsed

let is_def gt = match view gt with
  | C("def", _) -> true
  | _ -> false

let extract_gt p gt = 
  let rec loop acc gt = 
    if p gt then gt :: acc 
    else match view gt with
      | A _ -> acc
      | C(_, ts) -> ts +> List.fold_left loop acc
  in loop [] gt



(* This function reads a specfile with name given in mfile into a list
   of pairs such that the first component is the name of the first
   file and the second component is the filename of the second
   component.
*)
let read_spec mfile =
  print_endline ("Spec. file is: " ^ mfile);
  let file_pairs = ref [] in
  let ins = open_in mfile in
  let rec loop () =
    let next_line = input_line ins in 
    let next_two  = Str.split filesep next_line in
      if Str.string_before (List.hd next_two) 1 = "#"
      then
	print_endline "# Comment"
      else (
	print_endline ("Pair of files: " ^ 
			 List.nth next_two 0 ^ ", " ^
			 List.nth next_two 1);
	file_pairs := (
          List.nth next_two 0,
          List.nth next_two 1) :: 
          !file_pairs);
      loop ()
  in
    try loop () with
	End_of_file -> !file_pairs


let i2s i = string_of_int i

let translate_node (n2, ninfo) = match n2 with
  | Control_flow_c2.TopNode -> mkA("phony","TopNode")
  | Control_flow_c2.EndNode -> mkA("phony","EndNode")
  | Control_flow_c2.FunHeader def -> mkC("head:def", [Visitor_j.trans_def def])
  | Control_flow_c2.Decl decl -> Visitor_j.trans_decl decl
  | Control_flow_c2.SeqStart (s,i,info) -> mkA("head:seqstart", "{" ^ i2s i)
  | Control_flow_c2.SeqEnd (i, info) -> mkA("head:seqend", "}" ^ i2s i)
  | Control_flow_c2.ExprStatement (st, (eopt, info)) -> Visitor_j.trans_statement st
  | Control_flow_c2.IfHeader (st, (cond,info)) -> mkC("head:if", [Visitor_j.trans_expr cond])
  | Control_flow_c2.Else info -> Diff.control_else
  | Control_flow_c2.WhileHeader (st, (cond, info)) -> mkC("head:while", [Visitor_j.trans_expr cond])
  | Control_flow_c2.DoHeader (st, e, info) -> mkC("head:do", [Visitor_j.trans_expr e])
  | Control_flow_c2.DoWhileTail (expr, info) -> mkC("head:dowhiletail", [Visitor_j.trans_expr expr])
  | Control_flow_c2.ForHeader (st, (((e1opt, _), 
                                   (e2opt, _),
                                   (e3opt, _)),info)) -> mkC("head:for",
							     let handle_empty x = match x with
							       | None -> mkA("expr", "empty")
							       | Some e -> Visitor_j.trans_expr e in
							       [
								 handle_empty e1opt;
								 handle_empty e2opt;
								 handle_empty e3opt;
							       ]) 
  | Control_flow_c2.SwitchHeader (st, (expr, info)) -> mkC("head:switch", [Visitor_j.trans_expr expr])
  | Control_flow_c2.MacroIterHeader (st, 
                                   ((mname, aw2s), info)) ->
      mkC("head:macroit", [mkC(mname, List.map (fun (a,i) -> Visitor_j.trans_arg a) aw2s)])
  | Control_flow_c2.EndStatement info -> mkA("phony", "[endstatement]")

  | Control_flow_c2.Return (st, _) 
  | Control_flow_c2.ReturnExpr (st, _) -> Visitor_j.trans_statement st
      (* BEGIN of TODO

      (* ------------------------ *)
	 | Control_flow_c2.IfdefHeader of ifdef_directive
	 | Control_flow_c2.IfdefElse of ifdef_directive
	 | Control_flow_c2.IfdefEndif of ifdef_directive
         

      (* ------------------------ *)
	 | Control_flow_c2.DefineHeader of string wrap * define_kind

	 | Control_flow_c2.DefineExpr of expression 
	 | Control_flow_c2.DefineType of fullType
	 | Control_flow_c2.DefineDoWhileZeroHeader of unit wrap

	 | Control_flow_c2.Include of includ

      (* obsolete? *)
	 | Control_flow_c2.MacroTop of string * argument wrap2 list * il 

      (* ------------------------ *)


  *)
	 | Control_flow_c2.Default (st, _) ->
	     mkA("head:default", "default")
	 | Control_flow_c2.Case (st,(e,_)) -> 
	     mkC("head:case", [Visitor_j.trans_expr e])
	 | Control_flow_c2.CaseRange (st, ((e1, e2), _ )) ->
	     mkC("head:caserange", [Visitor_j.trans_expr e1; 
				    Visitor_j.trans_expr e2])
	 | Control_flow_c2.Continue (st,_) 
	 | Control_flow_c2.Break    (st,_) 
   (*
      (* no counter part in cocci *)

*)
	 | Control_flow_c2.Goto (st, _) -> Visitor_j.trans_statement st
	 | Control_flow_c2.Label (st, (lab, _)) -> mkA("head:label", lab)
(*

	 | Control_flow_c2.Asm of statement * asmbody wrap
	 | Control_flow_c2.MacroStmt of statement * unit wrap

      (* ------------------------ *)
      (* some control nodes *)

	 END of TODO *)

  | Control_flow_c2.Enter -> mkA("phony", "[enter]")
  | Control_flow_c2.Exit -> mkA("phony", "[exit]")
  | Control_flow_c2.Fake -> mkA("phony", "[fake]")

  (* flow_to_ast: In this case, I need to know the  order between the children
   * of the switch in the graph. 
   *)
  | Control_flow_c2.CaseNode i -> mkA("phony", "[case" ^ i2s i ^"]")

  (* ------------------------ *)
  (* for ctl:  *)
  | Control_flow_c2.TrueNode -> mkA("phony", "[then]")
  | Control_flow_c2.FalseNode -> mkA("phony", "[else]")
  | Control_flow_c2.InLoopNode (* almost equivalent to TrueNode but just for loops *) -> 
      Diff.control_inloop
      (* mkA("phony", "InLoop") *)
  | Control_flow_c2.AfterNode -> mkA("phony", "[after]")
  | Control_flow_c2.FallThroughNode -> mkA("phony", "[fallthrough]")

  | Control_flow_c2.ErrorExit -> mkA("phony", "[errorexit]")
  | _ -> mkA("NODE", "N/A")

let print_gflow g =
  let pr = print_string in
    pr "digraph misc {\n" ;
    pr "size = \"10,10\";\n" ;

    let nodes = g#nodes in
      nodes#iter (fun (k,gtree) -> 
	(* so can see if nodes without arcs were created *) 
	let s = Diff.string_of_gtree' gtree in
	  pr (Printf.sprintf "%d [label=\"%s   [%d]\"];\n" k s k)
      );

      nodes#iter (fun (k,node) -> 
	let succ = g#successors k in
	  succ#iter (fun (j,edge) ->
            pr (Printf.sprintf "%d -> %d;\n" k j);
	  );
      );
      pr "}\n" ;
      ()


let add_node i node g = g#add_nodei i node

(* convert a graph produced by ast_to_flow into a graph where all nodes in the
 * flow have been translated to their gtree counterparts
 *)
let flow_to_gflow flow =
  let gflow = ref (new Ograph_extended.ograph_mutable) in
  let nodes = flow#nodes in
    nodes#iter (fun (index, (node1, s)) ->
      !gflow +> add_node index (translate_node node1);
    );
    nodes#iter (fun (index, node) ->
      let succ = flow#successors index in
	succ#iter (fun (j, edge_val) -> 
          !gflow#add_arc ((index,j), edge_val)
        )
    );
    !gflow



let read_ast_cfg_old file =
  v_print_endline "[Reader] parsing...";
  let (pgm2, parse_stats) = 
    Parse_c.parse_print_error_heuristic file in
    (*  let flows = List.map (function (c,info) -> Ast_to_flow2.ast_to_control_flow c) pgm2 in *)
    (* ast_to_control_flow is given a toplevel entry and turns that into a flow *)
    v_print_endline "[Reader] type annotating";
    let tops_envs = 
      pgm2 +> List.map fst +>
	Type_annoter_c.annotate_program 
	!Type_annoter_c.initial_env
    in
    let flows = tops_envs +> List.map (function (c,info) -> Ast_to_flow2.ast_to_control_flow c)  in
    let  gflows = ref [] in
      flows +> List.iter (do_option (fun f -> 
				       gflows := (flow_to_gflow f) :: !gflows));
      (* among the gflows constructed filter out those that are not flows for a
       * function definition
       *)
      (pgm2, !gflows +> List.filter (function gf -> 
				       gf#nodes#tolist +> List.exists (
					 function (i,n) -> match view n with
					   | C("head:def",[{node=C("def",_)}]) -> true
					   | _ -> false)
				    ))


let read_ast_cfg file =
  v_print_endline "[Reader] parsing...";
  let (pgm2, parse_stats) = 
    Parse_c.parse_print_error_heuristic file in
    (*  let flows = List.map (function (c,info) -> Ast_to_flow2.ast_to_control_flow c) pgm2 in *)
    (* ast_to_control_flow is given a toplevel entry and turns that into a flow *)
    v_print_endline "[Reader] type annotating";
    let tops_envs = 
      pgm2 +> List.map fst +>
	Type_annoter_c.annotate_program 
	!Type_annoter_c.initial_env
    in
      tops_envs +>
	List.fold_left
	(fun acc_gt_f_list (c,info) -> 
	   let gt_ast = Visitor_j.trans_top c in
	     if is_def gt_ast
	     then 
	       match Ast_to_flow2.ast_to_control_flow c with
		 | None -> acc_gt_f_list
		 | Some f -> (gt_ast, flow_to_gflow f) :: acc_gt_f_list
	     else acc_gt_f_list
	) []

let read_src_tgt_cfg src tgt =
  let gt_f_list_src = read_ast_cfg src in
  let gt_f_list_tgt = read_ast_cfg tgt in
    if !Jconfig.verbose then (
      print_endline "[Diff] gflows for file:";
      print_endline "[Diff] LHS flows";
      gt_f_list_src +> List.iter (function (gt, flow) ->  print_gflow flow);
      print_endline "[Diff] RHS flows";
      gt_f_list_tgt +> List.iter (function (gt, flow) ->  print_gflow flow);
      print_endline "[Diff] DFS diff");
    (* for each g1:fun<name> in flows1 such that g2:fun<name> in flows2:
     * we assume all g in flows? are of function-flows
     * compute diff_dfs g1 g2
     * print diff
     *)
    let pairs = gt_f_list_src +> List.fold_left
      (fun acc_pairs (gt_lhs, flow_lhs) ->
	 let fname = get_fname_ast gt_lhs in
	   gt_f_list_tgt 
	   +> List.find_all
	     (function (gt_rhs, flow_rhs) ->
		get_fname_ast gt_rhs = fname
	     )
	   +> List.fold_left (fun selected_def (gt,f) -> 
				let cost = Diff.edit_cost gt_lhs gt in
				match selected_def with
				  | None -> Some((gt,f), cost)
				  | Some ((gt',f'), cost') ->
				      if cost < cost'
				      then Some ((gt,f),cost)
				      else selected_def
			     ) None 
	   +> (function x -> match x with
		 | None -> acc_pairs
		 | Some (gt_f,cost) -> ((gt_lhs,flow_lhs), gt_f) :: acc_pairs)
      ) [] in
      pairs +> List.iter (function ((gt1,f1), (gt2,f2)) -> 
			    Diff.get_flow_changes [f1] [f2]);
      pairs


(* first, let's try to parse a C program with Yoann's parser *)
let read_ast file =
  let (pgm2, parse_stats) = 
    Parse_c.parse_print_error_heuristic file in
    pgm2


let read_src_tgt src tgt =
  let gt1 = gtree_of_ast_c (read_ast src) in
  let gt2 = gtree_of_ast_c (read_ast tgt) in
    gt1, gt2

let read_filepair old_file new_file =
  print_endline 
    ("Reading file pair " ^
       old_file ^ " " ^ new_file);
  read_src_tgt old_file new_file


let read_src_tgt_def src tgt =
  let gts1 = gtree_of_ast_c (read_ast src)
    +> extract_gt is_def in
  let gts2 = gtree_of_ast_c (read_ast tgt)
    +> extract_gt is_def in
    gts1 +> List.fold_left
      (fun acc_pairs gt1 -> 
	 let f_name = get_fname_ast gt1 in
	   (gt1, 
	    gts2 
	    +> List.filter (function gt2 -> 
			      get_fname_ast gt2 = f_name
			   )
	    +> List.fold_left (fun selected_def gt2_cand ->
				 match selected_def with
				   | None -> Some (gt2_cand, Diff.edit_cost gt1 gt2_cand)
				   | Some (gt2, cost) ->
				       let cost' = Diff.edit_cost gt1 gt2_cand in
					 if cost' < cost
					 then Some (gt2_cand, cost')
					 else selected_def
			      ) None
	    +> (function x -> match x with
		  | None -> gt1
		  | Some (gt2,_) -> gt2)
	   ) :: acc_pairs
      ) []


let read_filepair_defs old_file new_file =
  print_endline 
    ("Reading file pair " ^
       old_file ^ " " ^ new_file);
  read_src_tgt_def old_file new_file


let read_filepair_cfg old_file new_file =
  print_endline 
    ("Reading file pair " ^
       old_file ^ " " ^ new_file);
  read_src_tgt_cfg old_file new_file
