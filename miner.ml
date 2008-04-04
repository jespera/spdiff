(* Structure for handling databases of itemsets *)

(* Operations needed for fpclose method:
 * frequency it:
 *   returns the number of times item it occurs in db
 * filter_item p:
 *   filters out all items in db that do not satisfy p
 * fold_left_item f a:
 *   applies f to all items of db 
 * restrict it:
 *   return db where itemsets are the ones including it but 
 *   stripped of it
 * empty:
 *   boolean whether there are any elements in the db
 *)


(* Threshold, t is already given.
 *
 * fpclose(db)
 * db = filter_infrequent db t
 * if empty -> return
 * otherwise ->
 * for each item
 *   tdb  = restrict db item
 *   res += item ++ fpclose(tdb)
 *   db   = remove db item
 * return res
 *)

(*open Db*)

let ($) db itemset = Db.get_support_itemset db itemset

let mined_db2str string_of_item orig_db db = 
  List.fold_left (function acc_str -> function itemset ->
    List.fold_left (function inner_str -> function item ->
      (string_of_item item) ^ ", " ^ inner_str
    )
    (":"^ string_of_int (orig_db$itemset)^ ";\n"^acc_str)
    itemset
  )
    ""
  db

let idfun = function x -> x

let rec dmine_simple db threshold =
  let localf = fun item -> fun freq -> fun (db, acc) ->
    let ndb = Db.add_to_all (dmine_simple (Db.restrict_item db item) threshold) item in
    let acc = Db.add_db ndb acc in
    let db  = Db.remove db item in
    (db, acc) in
  let db = Db.rm_infrequent db threshold in
  if Db.isEmpty db
  then Db.makeEmpty ()
  else snd (Db.fold_unique db localf (db, Db.makeEmpty ()))


(*let rec dmine_cls cont db threshold =*)
  (*if Db.isEmpty db*)
  (*then cont (Db.makeEmpty ())*)
  (*else*)
    (*let tfun = function item -> function -> ldb ->*)
      (*Db.add_to_all ldb item in*)
    (*let mfun = function mdb -> function ndb -> Db.add_db mdb ndb in*)
    (*let ifun = function ilist -> function fdb ->*)
      (*List.fold_left () fdb ilist in*)

let rec dmine db threshold =
  let localf = fun item -> fun freq -> fun (db, acc) ->
    let ndb = Db.add_to_all (dmine (Db.restrict_item db item) threshold) item in
    let acc = Db.add_db ndb acc in
    let db  = Db.remove db item in
    (db, acc) in
  let db = Db.rm_infrequent db threshold in
  if Db.isEmpty db
  then Db.makeEmpty ()
  else 
    if Db.sizeOne db
    then Db.makeAllPerms db
    else snd (Db.fold_unique db localf (db, Db.makeEmpty ()))

let dmine_cls db_orig threshold =
  let get_items db = Db.fold_unique db (fun a b -> a :: b) [] in
  let g_sup iset = db_orig $ iset in
  let (++) iset db = Db.add_itemset_cdb g_sup db (iset, g_sup iset) in
  let rec gen acc_db current_db current_iset =
    let next_db = Db.rm_infrequent current_db threshold in
    if Db.isEmpty next_db
    then current_db ++ acc_db
    else
      let next_items = get_items next_db in
      List.fold_left (fun acc_db item ->
        let next_iset = item :: current_iset in
        let restricted_db = Db.restrict_item current_db item in
        gen acc_db restricted_db next_iset
      ) acc_db next_items in
  gen (Db.makeEmpty ()) db_orig []

  (*let rec loop db res =*)
    (*match filter_infrequent db threshold with*)
    (*[] -> []*)
      (*print_string ("loop returning\n"^ db2str idfun res ^ "***\n  ");*)
      (*assert (emptydb res);*)
      (*res*)
    (*| fdb -> *)
        (*print_string ("Processing items: " ^ List.fold_left (function acc_str -> function item -> item ^ ", " ^ acc_str) "\n" (items fdb));*)
        (*let (edb, fres) = List.fold_left ( *)
          (*function (tdb, tres) -> function item ->*)
            (* ( *)
              (*remove tdb item*)
              (*, *)
              (*(add_to_all item (dmine (restrict tdb item) threshold)) @ tres*)
            (* ) *)
        (* ) (fdb,res) (items fdb)*)
    (*in*)
    (* at this point it should be the case that the database is empty
     * and fres is the result of dmine
     *)
      (*assert (emptydb edb);*)
      (*print_string "result:\n";*)
      (*print_string (db2str idfun fres);*)
      (*print_string "\n";*)
      (*fres*)
  (*in*)
    (*Printf.printf "dmine: \n%s\n" (db2str idfun db);*)
    (*print_string "dmine: \n";*)
    (*loop db []*)
    

(*******************************************************
 *
 *
 * Entry point to standalone executable follows below; 
 *
 *
 *******************************************************

let fname = ref ""
let threshold = ref 0
let toprint = ref false
let closed = ref false

let speclist = 
  Arg.align
  ["-file", Arg.Set_string fname,       "name   gives the name of file to mine";
   "-threshold", Arg.Set_int threshold, "num   use num as threshold when mining";
   "-print", Arg.Set toprint,           "bool   indicates that the resulting db should be printed to stdout";
   "-close", Arg.Set closed,            "bool   indicates that we should also produce the closed db"
   ]



let s2s s = s
let main () =
  print_string "Reading database";
  flush stdout;
  (*let fname = Sys.argv.(1) in*)
  (*let threshold = int_of_string (Sys.argv.(2)) in*)
  Arg.parse speclist (function _ -> ()) "Usage: ";
  let rdb = Db.read_db_from_file !fname in
  print_endline "done.";
  print_string "Read db size: ";
  print_endline (string_of_int (Db.sizeOf rdb));
  (*Db.print_db rdb;*)
  (*flush stdout;*)
  print_string "Data mining...";
  flush stdout;
  let mdb = dmine rdb !threshold in
  (*let cdb = close_db rdb mdb in*)
  print_endline "done.";
  print_string "Db size: ";
  print_endline (string_of_int (Db.sizeOf mdb));
  if !toprint then 
    (*Db.print_db mdb;*)
    (Db.fold_itemset mdb (function () -> function itemset ->
      let sup = rdb$itemset in
      print_string (string_of_int (Db.interestRatio itemset sup));
      print_string (": " ^ string_of_int sup ^ " ::: ");
      Db.print_itemset s2s itemset ;
      flush stdout) ());
  if !closed then (
    print_string "Closing db...";
    flush stdout;
    let cdb = Db.close_db rdb mdb in
    let _ = print_endline "done." in
    (*Db.print_db cdb)*)
    Db.fold_itemset cdb (function () -> function itemset ->
      let sup = rdb$itemset in
      (*print_string (string_of_int (Db.interestRatio itemset sup));*)
      print_endline ("\n: " ^ string_of_int sup ^ " ::: ");
      Db.print_itemset s2s itemset ;
      flush stdout) ())
  (*else ( *)
    (*print_endline "Non-closed db:";*)
    (*Db.print_db mdb)*)
    (*Db.fold_itemset mdb (function () -> function itemset ->*)
      (*let sup = rdb$itemset in*)
      (*print_string (string_of_int (Db.interestRatio itemset sup));*)
      (*print_endline ("\n: " ^ string_of_int sup ^ " ::: ");*)
      (*Db.print_itemset itemset ;*)
      (*flush stdout) ()*)
      (* ) *)
  ;
  print_newline ()

(*let _ = main ()*)
*)
