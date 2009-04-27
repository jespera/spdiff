(* custom traversal of ast_c since I could not figure out how to use the ones
 * others have already struggled with.
 *)

open Gtree
open Ast_c
open Type_annoter_c

let (+>) o f = f o

exception Fail of string

let type_c_term ty te = mkC(ty, [te])
let type_a_term ty a  = mkA(ty, a)
let make_type_expl t  = mkA("grammar",t)
let (<<) a b = make_type_expl a :: b
let (@@) a b' = match view b' with
  (*| C(b,l) -> C(a^":"^b,l)*)
  (*| C(b,l) -> C(a, b << l)*)
  | C(b,_)
  | A(b,_) -> mkC(a, [b'])
let (@@@) a b = mkC(a, b)
let (%%) a b = type_a_term a b
let (!!) a = mkA(a, "N/H")


let rec trans_expr exp = 
  let (unwrap_e, typ), ii = exp in
  match unwrap_e with
  | Ident s -> "exp" @@ "ident" %% s
      (* (match !typ with *)
      (*   | None, _ -> "exp" @@ "ident" %% s *)
      (*   | Some (ft, _), _ -> "exp" @@@ [ "TYPEDEXP" @@ trans_type ft; "ident" %% s]) *)
  | Constant (String (s, _)) -> 
      "exp" @@ "const" @@ "string" %% s
  | Constant (Int s) -> 
      "exp" @@ "const" @@ "int" %% s
  | Constant (Char (s, _)) ->
      "exp" @@ "const" @@ "char" %% s
  | Constant (Float (s, flT)) ->
      "exp" @@ "const" @@ "float" %% s
  | Constant _ ->
      "exp" @@ "const" @@ !! "other"
  | FunCall (f, args) ->
      let gt_f = trans_expr f in
      let gt_args = List.map (fun (e, ii) ->
        trans_arg e
      ) args in
      "exp" @@ "call" @@@ gt_f :: gt_args
  | CondExpr (e1, None, e3) ->
      let gt_e1 = trans_expr e1 in
      let gt_e3 = trans_expr e3 in
      "exp" @@ "cond2" @@@ [gt_e1; gt_e3]
  | CondExpr (e1, Some e2, e3) ->
      let gt_e1 = trans_expr e1 in
      let gt_e2 = trans_expr e2 in
      let gt_e3 = trans_expr e3 in
      "exp" @@ "cond3" @@@ [gt_e1; gt_e2; gt_e3]
  | Assignment (e1, op, e2) ->
      let gt_e1 = trans_expr e1 in
      let gt_e2 = trans_expr e2 in
(*      let gt_op = trans_assi op in *)
      let op_str = trans_assi op in
      "exp" @@ ("assign"^op_str) @@@ [gt_e1;gt_e2]
  | ArrayAccess (e1, e2) ->
      let gt_e1 = trans_expr e1 in
      let gt_e2 = trans_expr e2 in
      "exp" @@ "array_acc" @@@ [gt_e1;gt_e2]
  | RecordAccess (e1, str) -> 
      let gt_e1 = trans_expr e1 in
      let gt_e2 = "ident" %% str in
      "exp" @@ "record_acc" @@@ [gt_e1;gt_e2]
  | RecordPtAccess (e1, str) -> 
      let gt_e1 = trans_expr e1 in
      let gt_e2 = "ident" %% str in
      "exp" @@ "record_ptr" @@@ [gt_e1;gt_e2]
  | Postfix (e1, fOp) ->
      let gt_fop = trans_fop fOp in
      let gt_e1 = trans_expr e1 in
      "exp" @@ "postfix" @@ gt_fop @@ gt_e1
  | Infix (e1, fOp) ->
      let gt_fop = trans_fop fOp in
      let gt_e1 = trans_expr e1 in
      "exp" @@ "infix" @@ gt_fop @@ gt_e1
  | Unary (e1, unop) ->
      let gt_e1 = trans_expr e1 in
      let gt_up = trans_unary unop in
      "exp" @@ gt_up @@ gt_e1
  | Binary (e1, bop, e2) ->
      "exp" @@ (trans_binary e1 bop e2)
  | SizeOfType (ft) ->
      let gt_e1 = trans_type ft in
      "exp" @@ "sizeoftype" @@ gt_e1
  | SizeOfExpr (e) ->
      let gt_e1 = trans_expr e in
      "exp" @@ "sizeof" @@ gt_e1
  | ParenExpr e -> trans_expr e
  | Sequence (e1, e2) ->
      "exp" @@ ",seq" @@@ [
        trans_expr e1;
        trans_expr e2
      ]
  | Cast (ftype, e) -> "exp" @@ "cast" @@@ [trans_type ftype; trans_expr e] 
  | StatementExpr (comp, _)  -> 
      let comp' = stmt_elems_of_sequencable comp in
      "exp" @@ "stmtexp" @@@ List.map trans_statement comp'
  | Constructor (ft, initw2) -> "exp" %% "constr"

and trans_binary e1 bop e2 = 
  let gt_e1 = trans_expr e1 in
  let gt_e2 = trans_expr e2 in
  match bop with
  | Arith aop   -> "binary_arith" @@@ [trans_aop aop; gt_e1; gt_e2]
  | Logical lop -> "binary_logi" @@@ [trans_lop lop; gt_e1; gt_e2]

and trans_unary uop =
  match uop with
  | GetRef      -> "&ref"
  | DeRef       -> "*ref"
  | UnPlus      -> "+"
  | UnMinus     -> "-"
  | Tilde       -> "~"
  | Not         -> "!"
  | GetRefLabel -> "&&"

and trans_fop fop =
  match fop with 
  | Dec -> "--"
  | Inc -> "++"

and trans_aop aop =
  match aop with
  | Plus    -> "aop" %% "+"
  | Minus   -> "aop" %% "-"
  | Mul     -> "aop" %% "*"
  | Div     -> "aop" %% "/"
  | Mod     -> "aop" %% "%"
  | DecLeft -> "aop" %% "<<"
  | DecRight-> "aop" %% ">>"
  | And     -> "aop" %% "&"
  | Or      -> "aop" %% "|"
  | Xor     -> "aop" %% "^"

and trans_lop lop =
  "logiop" %%
  match lop with
  | Inf    -> "<"
  | Sup    -> ">"
  | InfEq  -> "<="
  | SupEq  -> ">="
  | Eq     -> "=="
  | NotEq  -> "!="
  | AndLog -> "&&"
  | OrLog  -> "||"

and trans_assi op =
  match op with
  | SimpleAssign -> "="
  | OpAssign Plus -> "+="
  | OpAssign Minus -> "-="
  | OpAssign Mul -> "*="
  | OpAssign Mod -> "%="
  | OpAssign Div -> "/="
  | OpAssign And -> "&="
  | OpAssign Or  -> "|="
  | OpAssign Xor -> "x="
  | _ -> "?=?"

and trans_assi_old op = (*{{{*)
  match op with
  | SimpleAssign -> mkA("simple_assi", "=")
  | OpAssign Plus -> mkA("op_assi", "+=")
  | OpAssign Minus -> mkA("op_assi", "-=")
  | OpAssign Mul -> mkA("op_assi", "*=")
  | OpAssign Mod -> mkA("op_assi", "%=")
  | OpAssign Div -> mkA("op_assi", "/=")
  | OpAssign And -> mkA("op_assi", "&=")
  | OpAssign Or  -> mkA("op_assi", "|=")
  | OpAssign Xor -> mkA("op_assi", "x=")
  | _ -> mkA("op_assi", "N/H")(*}}}*)

and trans_arg arg = match arg with
  | Common.Left e -> trans_expr e
  | Common.Right (ArgType p) -> mkC("argtype",
				    [trans_param (p,[])]
				   )
  | Common.Right (ArgAction amac) -> mkA("argact", "N/H")

and trans_statement (sta : statement) = 
  let unwrap_st, ii = sta in
  match unwrap_st with
  | ExprStatement None -> "stmt" @@ "exprstmt" %% "none"
  | ExprStatement (Some e) -> "stmt" @@ "exprstmt" @@ trans_expr e
  | Compound sts ->
      let sts' = stmt_elems_of_sequencable sts in
      let gt_sts = List.map trans_statement sts' in(*{{{*)
      if sts' = []
      then "stmt" @@ "comp{}" %% "NOP"
      else "stmt" @@ "comp{}" @@@ gt_sts
  | Jump j -> "stmt" @@ trans_jump j 
  | Selection s -> "stmt" @@ trans_select s
  | Iteration i -> "stmt" @@ trans_iter i
  (*| Iteration (For (es1,es2,es3, st)) ->*)
      (*let none_empty f e = *)
        (*match unwrap e with *)
        (*| None -> A("expr", "NONE")*)
        (*| Some r -> f r*)
      (*in*)
      (*let gt_es1 = none_empty trans_expr es1 in*)
      (*let gt_es2 = none_empty trans_expr es2 in*)
      (*let gt_es3 = none_empty trans_expr es3 in*)
      (*let gt_st  = trans_statement st in*)
      (*C("for",[gt_es1;gt_es2;gt_es3;gt_st])*)
  | Decl de -> "stmt" @@ trans_decl de
  | Labeled lab -> "stmt" @@ trans_labeled lab
  | _ -> !! "stmt"

and trans_labeled lab = match lab with
| Label (s, stat) -> "labeled" @@@ ["lname" %% s; trans_statement stat]
| Case (e, stat) -> "case" @@@ [trans_expr e; trans_statement stat]
| CaseRange (e1, e2, st) -> "caseRange" @@@ [
    trans_expr e1; trans_expr e2;
    trans_statement st]
| Default stat -> "default" @@ trans_statement stat

and trans_iter i = 
  match i with
  | While (e, s) -> "while" @@@ [
      trans_expr e;
      trans_statement s]
  | DoWhile (s, e) -> "dowhile" @@@ [
      trans_statement s;
      trans_expr e]
  | For (es1, es2, es3, st) -> 
      let handle_empty x = match unwrap x with
      | None -> "expr" %% "empty"
      | Some e -> trans_expr e in
      "for" @@@ [
        handle_empty es1;
        handle_empty es2;
        handle_empty es3;
        trans_statement st]
  | MacroIteration (s, awrap, st) -> 
      "macroit" @@ s @@@ [
        (*"args" List.map (function (e, ii) -> trans_arg e) awrap;*)
        trans_statement st
      ]
      (*raise (Fail "macroiterator not yet supported")*)

and trans_select s = 
  match s with
  | If(e, st1, st2) -> "if" @@@ [
      trans_expr e;
      trans_statement st1;
      trans_statement st2]
  | Switch (e, s) ->
      "switch" @@@ [
        trans_expr e;
        trans_statement s]
(*  | Ifdef (ss1, ss2) -> "ifdef" @@@ [
      "ifdef1" @@@ List.map trans_statement ss1;
      "ifdef2" @@@ List.map trans_statement ss2]
 *)

and trans_jump j =
  match j with
  | Goto s -> "goto" %% s
  | Continue -> "jump" %% "continue" 
  | Break -> "jump" %% "break"
  | Return -> "jump" %% "return"
  | ReturnExpr e -> "return" @@ trans_expr e
  | GotoComputed e -> "goto" @@ trans_expr e

and trans_type (tqual, typec) =
  let gt_qual = trans_qual tqual in
  let gt_typc = [trans_typec typec] in
  "fulltype" @@@ (gt_qual @ gt_typc)

and trans_qual tq =
  let gt_const = if (unwrap tq).const then ["tqual" %% "const"] else [] in
  let gt_vola  = if (unwrap tq).volatile then ["tqual" %% "vola"] else [] in
  gt_const @ gt_vola

and trans_typec tc =
  match unwrap tc with
  | BaseType bt -> trans_basetype bt
  | Pointer ft -> "pointer" @@ trans_type ft
  | Array (cexpOpt, ft) -> 
      let ft_gt = trans_type ft in
      let cexp_gt = (match cexpOpt with
        | None -> "constExp" %% "none"
        | Some e -> "constExp" @@ trans_expr e) in
      "array" @@@ [cexp_gt; ft_gt]
  | FunctionType funt -> trans_funtype funt
  | Enum (sOpt, enumT) -> 
      let enum_name = (match sOpt with
        | None -> "anon_enum"
        | Some s -> s) in
      let enumt_gt = trans_enumtype_list enumT in
      "enum" @@@ ["ename" %% enum_name; enumt_gt]
  | StructUnion (strun, sOpt, sType) -> 
      let su_str = string_of_structunion strun in
      let stype = trans_struct_type sType in
      let sname = (match sOpt with
        | None -> "anon_structunion"
        | Some s -> s) in
      su_str @@ sname @@ stype
  | EnumName name -> "enumname" %% name
  | StructUnionName (su, name) -> string_of_structunion su %% name
  | TypeName (name, ftOpt) -> 
      let ft_gt = (match ftOpt with
        | None -> "fullType" %% "unknown"
        | Some ft -> trans_type ft) in
      "typeName" @@@ ["ident" %% name; ft_gt]
  | ParenType ft -> trans_type ft
  | TypeOfExpr ex -> "typeOfExp" @@ trans_expr ex
  | TypeOfType ft -> "typeOfType" @@ trans_type ft

and trans_struct_type st = "fields" @@@
  List.map trans_field_type st

and trans_field_type f = match unwrap f with
  | DeclarationField (FieldDeclList (fkinds, _)) -> "fdecls" @@@ List.map (function fkwrap -> 
      (match unwrap (unwrap fkwrap) with
      | Simple (varOpt, ftype) -> 
          (match varOpt with 
          | None -> "field" @@@ 
            ["fieldname" %% "anon"; "fieldtype" @@ trans_type ftype]
          | Some v -> "field" @@@
            ["fieldname" %% v; "fieldtype" @@ trans_type ftype])
      | BitField (varOpt, ftype, cExp) -> 
          let fn = (match varOpt with 
          | None -> "fieldname" %% "anon"
          | Some v -> "fieldname" %% v) in
          let ft_gt = trans_type ftype in
          let bits  = trans_expr cExp in
          "bitfield" @@@ [fn; ft_gt; bits])
      ) fkinds
  | EmptyField -> "field" %% "empty"
  | _ -> "field_type" %% "N/A"

and string_of_structunion su = match su with
| Struct -> "struct"
| Union  -> "union"

and trans_enumtype_list enT = 
  let en_gts = List.map trans_enum_type enT in
  "enumTypes" @@@ en_gts

and trans_enum_type (((enum_val, cExpOpt), _), _) =
  let enum_val_name = "enum_val" %% enum_val in
  let enum_val_val  = (match cExpOpt with
    | None -> "enum_const" %% "unset"
    | Some e -> "enum_exp" @@ trans_expr e) in
  "enum_entry" @@@ [enum_val_name; enum_val_val]

and trans_basetype bt =
  match bt with
  | Void -> mkA("btype","void")
  | IntType it -> "btype" @@ trans_inttype it
  | FloatType ft -> "btype" @@ trans_floattype ft

and trans_inttype it = 
  match it with
  | CChar -> "itype" %% "char"
  | Si si -> "itype" @@@ trans_signed si

and trans_signed (s, b) =
  let gt_sign = match s with 
  | Signed -> "signed"
  | UnSigned -> "unsigned" in
  let gt_base = 
    match b with
    | CChar2 -> "char2"
    | CShort -> "short"
    | CInt   -> "int"
    | CLong  -> "long"
    | CLongLong -> "long long" in
  let gt1 = mkA("sgn", gt_sign) in
  let gt2 = mkA("base", gt_base) in
  [gt1; gt2]

and trans_floattype ft = 
  let gt_ft = match ft with
  | CFloat -> "float"
  | CDouble -> "double"
  | CLongDouble -> "long double" in
  "ftype" %% gt_ft

and trans_decl decl = match decl with
| DeclList (odecls,_) -> "dlist" @@@ 
  List.map trans_odecl odecls
| MacroDecl ((s, args), _) ->
    "mdecl" @@ s @@@ List.map (function a -> trans_arg (unwrap a)) args
(*and trans_odecl ((fopt, ftype, stor, _), _) = match fopt with *)

and trans_odecl ({v_namei = fopt; v_type = ftype; v_storage = stor}, _) = match fopt with
  | None -> "onedecl" %% "()"
      (*raise (Fail "decl_spec with no init_decl")*)
  | Some ((var, initOpt), _) -> 
      let gt_var = "exp" @@ "ident" %% var in
      let gt_ft  = trans_type ftype in
      let gt_sto = trans_storage stor in
      match initOpt with
      | None -> "onedecl" @@@ [gt_var;gt_ft;gt_sto]
      | Some ini -> "onedecl_ini" @@@ 
        [gt_var; trans_ini ini; gt_ft; gt_sto]

and trans_storage (sto, inl) =
  let inl_gt = "inline" %% if inl then "inline" else "notinline" in
  let sto_gt = "stobis" %% match sto with
  | NoSto -> "nosto"
  | StoTypedef -> "stotypedef"
  | Sto sclass -> (match sclass with
      | Auto -> "auto"
      | Static -> "static"
      | Register -> "register"
      | Extern -> "extern") in
  "storage" @@@ [sto_gt;inl_gt]

and trans_ini (ini, _) = match ini with
| InitExpr e -> "ini" @@ trans_expr e
| InitList ilist -> "iniList" @@@ List.map 
  (function (ini, _) -> trans_ini ini)
  ilist
| InitFieldOld (v, ini) -> (* y: value initialiser *)
    "iniFO" @@@ ["field" %% v ; trans_ini ini] 
| InitIndexOld (e, ini) -> (* [102]10 initialiser *)
    raise (Fail "InitIndexOld")
| InitDesignators (deslist, ini) -> (* [0 ... 10] = 1 , .y = 10 *)
    let ini_gt = trans_ini ini in
    "inidesignators" @@@ (ini_gt :: (List.map (function design -> 
      (match unwrap design with
      | DesignatorField s -> "dfield" %% s
      | DesignatorIndex e -> "dindex" @@ trans_expr e
      | DesignatorRange (from, tgt) -> 
          "drange" @@@ [trans_expr from; trans_expr tgt])
    ) deslist))
(* and trans_def def =  *)

and trans_def ({
  f_name = name;
  f_type = ty;
  f_storage = sto;
  f_body = body;
}, _) = 
(*  let (name, ty, (sto, _), body) = unwrap def in(*{{{*) *)
  let gt_funty = trans_funtype ty in
  let gt_comp  = List.map trans_statement (stmt_elems_of_sequencable body) in
  let gt_body  = "stmt" @@ "comp{}" @@@ gt_comp in
  let gt_name  = "fname" %% name in
  mkC("def", [gt_name; gt_funty; gt_body])(*}}}*)

and trans_funtype (rettype, (params, hasdots)) =
  let gt_ret = trans_type rettype in
  let par_types = List.map trans_param params in
  "funtype" @@@ (gt_ret :: par_types)

and trans_param p = 
  match unwrap (unwrap p) with
  | (reg, name, ft) ->
      let reg  = mkA("reg", if reg then "register" else "") in
      let name = mkA("name", match name with Some n -> n | _ -> "") in
      let ft = trans_type ft in
      mkC("param",[reg;name;ft])

and trans_define def = mkA("define", "N/H")

and trans_ccp cpp_dir =
  match cpp_dir with
    | Include inc -> trans_include inc
    | Define def -> trans_define def
    | _ -> "cpp_dir" %% "N/A"

and trans_top top = 
  match top with
  | Definition def -> trans_def def
  | Declaration decl -> trans_decl decl
  | CppTop cpp_dir -> trans_ccp cpp_dir
  | IfdefTop ifdef_dir -> "ifdeftop" %% "N/A"
  | MacroTop (str, args2, _) ->
      "macrotop" @@ str @@@
      List.map (function a2 -> trans_arg (unwrap a2)) args2
  | EmptyDef _ -> mkA("edef", "N/H")
  | NotParsedCorrectly _ -> mkA("NCP","N/H")
  | FinalDef _ -> mkA("fdef", "N/H")
  | _ -> mkA("top", "N/H")
(* and trans_include (inc_f, inc_pos) = *)

and trans_include { i_include = inc_f} =
  let ie s = mkA("inc_elem", s) in
  match unwrap inc_f with
  | Local ies -> mkC("includeL", List.map ie ies)
  | NonLocal ies -> mkC("includeN", List.map ie ies)
  | Wierd s -> mkC("include", [mkA("winc", s)])

let trans_prg prg = 
  let tops = List.map trans_top prg in
  C ("prg", tops)

let trans_prg2 prg = 
  let tops = 
    (List.map (fun (a, _) -> a)
    (List.filter (fun a -> match a with (FinalDef _, _) -> false | _ -> true)
    prg))
    (*List.map (fun (tl,_) -> trans_top tl) prg *)
  in
  let tops_envs = 
    Type_annoter_c.annotate_program 
      !Type_annoter_c.initial_env
      tops in
  "prg2" @@@
  List.map (function (top, (tenvb, tenv)) -> 
    trans_top top
  ) tops_envs
