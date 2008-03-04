open Gtree

let unparse_c gt =
  match gt with
  | A(at, s) -> (match at with
    | "ident" -> s
    | "const_s" -> s
    | "const_i" -> s
    | "const" -> "nh"
    | "expr" -> "42"
    | "aop" -> s
  )
