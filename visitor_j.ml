(* custom traversal of ast_c since I could not figure out how to use the ones
 * others have already struggled with.
 *)

open Gtree
open Ast_c

let (+>) o f = f o

exception Fail of string

let type_c_term ty te = C(ty, [te])
let type_a_term ty a  = A(ty, a)
let make_type_expl t  = A("grammar",t)
let (<<) a b = make_type_expl a :: b
let (@@) a b' = match b' with
  (*| C(b,l) -> C(a^":"^b,l)*)
  (*| C(b,l) -> C(a, b << l)*)
  | C(b,l) -> C(a, [b'])
  | A(b,l) -> C(a, [b'])
let (@@@) a b = C(a, b)
let (%%) a b = type_a_term a b
let (!!) a = A(a, "N/H")


let rec trans_expr exp = 
  let (unwrap_e, typ), ii = exp in
  match unwrap_e with
  | Ident s -> 
      "exp" @@ "ident" %% s
  | Constant (String (s, _)) -> 
      "exp" @@ "const" @@ "string" %% s
  | Constant (Int s) -> 
      "exp" @@ "const" @@ "int" %% s
  | Constant (Char (s, _)) ->
      "exp" @@ "conts" @@ "char" %% s
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
      let gt_op = trans_assi op in
      "exp" @@ "assign" @@@ [gt_op;gt_e1;gt_e2]
  | ArrayAccess (e1, e2) ->
      let gt_e1 = trans_expr e1 in
      let gt_e2 = trans_expr e2 in
      "exp" @@ "array_acc" @@@ [gt_e1;gt_e2]
  | RecordAccess (e1, str) -> 
      let gt_e1 = trans_expr e1 in
      let gt_e2 = A ("ident", str) in
      "exp" @@ "record_acc" @@@ [gt_e1;gt_e2]
  | RecordPtAccess (e1, str) -> 
      let gt_e1 = trans_expr e1 in
      let gt_e2 = A ("ident", str) in
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
      "exp" @@ "stmtexp" @@@ List.map trans_statement comp
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
and trans_assi op = (*{{{*)
  match op with
  | SimpleAssign -> A("simple_assi", "=")
  | OpAssign Plus -> A("op_assi", "+=")
  | OpAssign Minus -> A("op_assi", "-=")
  | OpAssign Mul -> A("op_assi", "*=")
  | OpAssign Mod -> A("op_assi", "%=")
  | OpAssign Div -> A("op_assi", "/=")
  | OpAssign And -> A("op_assi", "&=")
  | OpAssign Or  -> A("op_assi", "|=")
  | OpAssign Xor -> A("op_assi", "x=")
  | _ -> A("op_assi", "N/H")(*}}}*)
and trans_arg arg = match arg with
  | Common.Left e -> trans_expr e
  | Common.Right (ArgType p) -> A("argtype", "N/H")
  | Common.Right (ArgAction amac) -> A("argact", "N/H")
and trans_statement sta = 
  let unwrap_st, ii = sta in
  match unwrap_st with
  | ExprStatement None -> "stmt" @@ "exprstmt" %% "none"
  | ExprStatement (Some e) -> "stmt" @@ "exprstmt" @@ trans_expr e
  | Compound sts ->
      let gt_sts = List.map trans_statement sts in(*{{{*)
      if sts = []
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
  | _ -> A ("statem", "N/H")
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
  | Ifdef (ss1, ss2) -> "ifdef" @@@ [
      "ifdef1" @@@ List.map trans_statement ss1;
      "ifdef2" @@@ List.map trans_statement ss2]
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
  C("fulltype", gt_qual @ gt_typc)
and trans_qual tq =
  let gt_const = if (unwrap tq).const then [A("tqual","const")] else [] in
  let gt_vola  = if (unwrap tq).volatile then [A("tqual","vola")] else [] in
  gt_const @ gt_vola
and trans_typec tc =
  match unwrap tc with
  | BaseType bt -> C("ctype", [trans_basetype bt])
  | _ -> A("typec", "N/H")
and trans_basetype bt =
  match bt with
  | Void -> A("btype","void")
  | IntType it -> C("btype",[trans_inttype it])
  | FloatType ft -> C("btype",[trans_floattype ft])
and trans_inttype it = 
  match it with
  | CChar -> A("itype", "char")
  | Si si -> C("itype", trans_signed si)
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
  let gt1 = A("sgn", gt_sign) in
  let gt2 = A("base", gt_base) in
  [gt1; gt2]
and trans_floattype ft = 
  let gt_ft = match ft with
  | CFloat -> "float"
  | CDouble -> "double"
  | CLongDouble -> "long double" in
  A("ftype", gt_ft)
and trans_decl decl = "decl" %% "N/H"
and trans_ini ini = A("ini", "N/H")
and trans_struct_fields sfields = A("sfields", "N/H")
and trans_def def = 
  let (name, ty, (sto, _), body) = unwrap def in(*{{{*)
  let gt_funty = trans_funtype ty in
  let gt_comp  = List.map trans_statement body in
  let gt_body  = "stmt" @@ "comp{}" @@@ gt_comp in
  let gt_name  = A("fname", name) in
  C("def", [gt_name; gt_funty; gt_body])(*}}}*)
and trans_funtype (rettype, (params, hasdots)) =
  let gt_ret = trans_type rettype in
  let par_types = List.map trans_param params in
  C("funtype", gt_ret :: par_types)
and trans_param p = 
  match unwrap (unwrap p) with
  | (reg, name, ft) ->
      let reg  = A("reg", if reg then "register" else "") in
      let name = A("name", match name with Some n -> n | _ -> "") in
      let ft = trans_type ft in
      C("param",[reg;name;ft])
and trans_define_val = A("def_val", "N/H")
and trans_top top = 
  match top with
  | Definition def -> trans_def def
  | Declaration _ -> A("decl", "N/H")
  | Include i -> trans_include i
  | Define _ -> A("define", "N/H")
  | MacroTop _ -> A("mtop", "N/H")
  | EmptyDef _ -> A("edef", "N/H")
  | NotParsedCorrectly _ -> A("NCP","N/H")
  | FinalDef _ -> A("fdef", "N/H")
  | _ -> A("top", "N/H")
and trans_include (inc_f, inc_pos) =
  let ie s = A("inc_elem", s) in
  match unwrap inc_f with
  | Local ies -> C("includeL", List.map ie ies)
  | NonLocal ies -> C("includeN", List.map ie ies)
  | Wierd s -> C("include", [A("winc", s)])
let trans_prg prg = 
  let tops = List.map trans_top prg in
  C ("prg", tops)
let trans_prg2 prg = 
  let tops = 
    List.map (fun (a, _) -> trans_top a)
    (List.filter (fun a -> match a with (FinalDef _, _) -> false | _ -> true) prg)
    (*List.map (fun (tl,_) -> trans_top tl) prg *)
  in
  C ("prg2", tops)
