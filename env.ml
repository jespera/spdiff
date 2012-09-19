open Gtree

let mk_env (m, t) = [(m, t)]

let empty_env = ([] : ((string * gtree) list))

(* given env and value t, find the _first_ binding m->t in env and return m
 * there may be other bindings in env such that m'->t
 *)
let rev_lookup env t =
  let rec loop env = match env with 
  | [] -> None
  | (m,t') :: env when t = t' -> Some m
  | _ :: env -> loop env
  in
  loop env 

  
(* replace subterms of t that are bound in env with the binding metavariable
   so subterm becomes m if m->subterm is in env
   assumes that if m1->st & m2->st then m1 = m2
   i.e. each metavariable denote DIFFERENT subterms
   so that one can uniquely perform the rev_lookup
*)
let rec rev_sub env t =
  match rev_lookup env t with
  | Some m -> mkA("meta", m)
  | None -> (match view t with 
    | C(ty, ts) -> mkC(ty, 
                       List.rev (List.fold_left 
                                (fun acc_ts t -> rev_sub env t :: acc_ts) 
                                [] ts)
                      )
    | _ -> t)

(* replace metavars in t with their corresponding binding in env (if any)
 *)
let rec sub env t =
  if env = [] then t 
  else
    let rec loop t' = match view t' with
      | C (ct, ts) ->
          mkC(ct, List.rev (
            List.fold_left (fun b a -> (loop a) :: b) [] ts
          ))
      | A ("meta", mvar) -> (try 
			       List.assoc mvar env with Not_found ->
				 mkA ("meta", mvar)
			    )
      | _ -> t'
    in
      loop t

let rev_assoc a l = 
  fst(List.find (function (m,b) -> b = a) l)
