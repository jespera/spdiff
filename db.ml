(* Database structure;
 *
 * A database is a datastructure representing the data to be mined. It consists
 * of a number of itemsets each of which contains a number of items. Items are
 * the base data that we need to mine
 *
 * A database must support the following functions;
 *
 * makeEmpty: return empty-database
 *
 * isEmpty db: true iff db is empty
 *
 * add_itemset db itset: adds itset to the database
 *
 * filter db p: remove all items of db that does not satisfy the property
 * expressed in by p
 * 
 * fold_all db f b: fold the function f over all items in the db with b as start
 * value for accumulator
 * 
 * fold_unique f b: fold the function f over all unique items in the db
 * starting from b; the function f recieves for each item a pair of the item
 * and its frequency
 *
 * fold_itemset f b: fold the function f over all itemsets starting with the
 * value given by b
 *
 * map db f: map the function f to all items in all itemsets and assume that
 * the function f is pure so that we may employ memoization to speed up
 * calculations
 *
 * map_itemsets db f: map the function f to all itemsets
 *
 *
 * We also introduce a number of predefined functions that could also have been
 * expressed in terms of the above primitives
 *
 * read_db_from_file fname
 * rm_infrequent db threshold
 * restrict_item db item
 * remove db item
 * close db 
 *
 *
 *)

(* --------------------------- Types ----------------------------- *)

(*type 'a unique_items = ('a * int) list*)
(*module M = Map.Make (String)*)

module type Itemset_type =
  sig
    type t
    val compare : t -> t -> int
  end

module Db (IT : Itemset_type) =
struct

  (*module GT =*)
  (*struct*)
    (*type t = (string, string) Gtree.gtree*)
    (*let compare = Pervasives.compare*)
  (*end*)


module M = Map.Make (IT)

type unique_items = int M.t
type db = EmptyDB | DB of IT.t list list * unique_items

exception InvalidDB
(* ub6 ¶ *)
let itemsep = Str.regexp "\\( *¶ *\\)+"
let itemsepstr = "¶"

(* ---------------------- Primitive functions -------------------- *)

(* make a printable string for the unique items in the database *)
let uniq2str string_of_item uniq =
  let f = fun key -> fun value -> fun acc ->
    "(" ^ string_of_item key ^ ": " ^ string_of_int value ^ ") " ^ acc in
  M.fold f uniq "\n"

let print_unique string_of_item uniq =
  let f = fun key -> fun value ->
    print_endline ("(" ^ string_of_item key ^ ": " ^ string_of_int value ^ ") ") in
  M.iter f uniq

(* make nice printable string for an itemset *)
let rec itemset2str string_of_item itemset = 
  match itemset with
  | [] -> "\n"
  | [item] -> (string_of_item item) ^ "\n"
  | item :: itemset -> 
      (string_of_item item) ^ itemsepstr ^ 
      itemset2str string_of_item itemset

let print_itemset string_of_item itemset =
  match itemset with
  | [] -> print_newline ()
  | [item] -> print_endline (string_of_item item)
  | items -> 
      (List.iter (fun item -> 
        print_string (
          (string_of_item item) ^ itemsepstr)) items; 
        print_newline ())
 
(* make a printable string for the elements of the database *)
let rec elems2str string_of_item elems = 
  List.fold_left (fun acc -> fun itset ->
    (itemset2str string_of_item itset) ^ acc)
    "" elems

let print_elems string_of_item elems = List.iter (function x -> 
  print_endline "[";print_itemset string_of_item x; print_endline "]") 
  elems

(* make a printable string representing the database *)
let db2str string_of_item db = match db with
  | DB (db, items) -> 
      "uniq. items: " ^ uniq2str string_of_item items ^
      "***\n" ^
      elems2str string_of_item db ^
      "***\n"
  | EmptyDB -> "Empty?\n"

(* print_db db; print a string representing the db to stdout *)
let print_db string_of_item db = match db with
| DB (db, items) ->
    print_endline "Unique items: ";
    print_unique string_of_item items;
    print_elems string_of_item db;
| EmptyDB -> print_string "Empty db\n"


(* make new empty db *)
let makeEmpty () = EmptyDB

(* test whether a db is empty *)
let rec isEmpty db = match db with
  | EmptyDB -> true
  | DB ([], uni_items) -> M.is_empty uni_items || raise InvalidDB
  | DB _ -> false


(* update_item items item updf; updates the freq. of item in items by a
 * function updf that takes the current counts as parameter and 0 if item is
 * not already present in db
 *)
let update_item items item updf = try
  match M.find item items with 
  | count -> 
      (*print_string ("addto : "^ item ^", " ^ string_of_int (count + 1) ^ "\n");*)
      M.add item (updf count) items
  with Not_found -> 
    (*print_string ("addto unfound: "^ item ^ "\n");*)
    M.add item (updf 0) items

(* add_item adds another item to the unique items list items and maintains the
 * frequency correctly; if a new item is added the freq is 1 if it already
 * existed it is incremented by one *)
let rec add_item items item = try
  match M.find item items with 
  | count -> 
      (*print_string ("addto : "^ item ^", " ^ string_of_int (count + 1) ^ "\n");*)
      M.add item (count + 1) items
  with Not_found -> 
    (*print_string ("addto unfound: "^ item ^ "\n");*)
    M.add item 1 items
  (*match items with*)
  (*| [] -> [(item, 1)]*)
  (*| (item', n) :: items -> *)
      (*if item = item' *)
      (*then (item, n+1) :: items*)
      (*else (item', n) :: add_item items item*)

(* add itemset to db *)
let add_itemset db itemset = 
  let addto_items items = List.fold_left add_item items itemset in
  match db with
  | DB (isets, items) -> DB(itemset :: isets, addto_items items)
  | EmptyDB -> DB([itemset], addto_items M.empty)

exception NotFoundUniqItem
(* search for item in unique item list of db *)
let lookup_item_freq items item =
  M.find item items
  (*let rec loop items = match items with*)
  (*| (key, freq) :: items -> if key = item then freq else loop items*)
  (*| [] -> raise NotFoundUniqItem in*)
  (*loop items*)

(* constrain db elements to only those elements mentioned in a unique items
 * list; an unique items list is a list of pairs and associated frequencies;
 * this function assumes that the unique items list already knows the new
 * frequencies
 *)

let constrain_db db new_items = match db with 
  | DB (db, _) -> let rec loop db = match db with
    | itemset :: db -> 
        let iset = (List.fold_left (function acc_itemset -> function item ->
          try match lookup_item_freq new_items item with
          | _ -> item :: acc_itemset
          with Not_found-> acc_itemset
        ) [] itemset) in
        if iset = [] 
        then loop db
        else iset :: loop db
    | [] -> [] in
    DB (loop db, new_items)
  | EmptyDB -> EmptyDB


(* filter out items not satisfying p; p must be of type a * int -> bool where a
 * is an item from the db and int is the frequency of that item in the db *)
(* we shall assume that the filter predicate p is a pure function so that we
 * need not evaluate it several times for the same input
 *)
let filter db p =
  let filter_items items =
    M.fold (fun key -> fun value -> fun acc ->
      if p (key, value) 
      then M.add key value acc
      else acc
    ) items M.empty
    (*match items with*)
    (*| itemandfreq :: items ->*)
        (*if p itemandfreq*)
        (*then itemandfreq :: loop items*)
        (*else loop items*)
    (*| [] -> []*)
  in
  match db with
  | DB(db, items) as db'-> constrain_db db' (filter_items items)
  | EmptyDB -> EmptyDB


(* filter_itemset db p: filters out all itemsets that does not satisfy p;
 * notice that this is rather different from filtering only items as now the
 * frequencies may(will) change for some items
 *)
let filter_itemset db p = 
  let rec loop db_acc itemsets =
    match itemsets with
    | itemset :: itemsets -> if p itemset 
        then loop (add_itemset db_acc itemset) itemsets 
        else loop db_acc itemsets 
    | [] -> db_acc in
  match db with
  | DB (db, _) -> loop (makeEmpty ()) db
  | EmptyDB -> EmptyDB

(* fold f over all items of db *)
let fold_all db f b =
  let rec loop db acc = match db with
  | itemset :: db -> loop db (List.fold_left 
      (function a -> function item -> f a item) acc itemset)
  | [] -> acc in
  match db with
  | DB(db,items) -> loop db b
  | EmptyDB -> b

(* fold f over all itemsets in db starting with b *)
let fold_itemset db f b =
  match db with
  | DB (db, _) -> 
      (*print_endline ("Folding itemsets: " ^ *)
        (*string_of_int (List.length db));*)
      List.fold_left f b db

  | EmptyDB -> b

(* fold f over unique items *)
let fold_unique db f b =
  match db with
  | DB (_, items) -> M.fold f items b
  | EmptyDB -> b

(* ---------------------- Predefined functions ------------------- *)

(* Function to read database from input. We assume that the format of input is
 * (*{{{*)
 * as described by the following grammar:
  * db      ::= itemset+
  * itemset ::= item itemsep itemset | '\n'
  * item    ::= /string/
  * itemsep ::= \( *¶ *\)*
 * A db is at least one itemset. An itemset is a 'itemsep' separated list of
 * items (which are just strings)
 *)


(*let itemsep = Str.regexp "[ \t]+"*)
(* ub6 = ¶ *)
let itemsep = Str.regexp "\\( *¶ *\\)+"
let itemsepstr = "¶"

(* Reading of database from input-file
 * We assume that there can not be duplicates in itemsets and remove those in
* the constructed database
*) (*}}}*)
let rec read_db_from_file item_of_string fname =(*{{{*)
  let ins = open_in fname in
  let jdb = ref (makeEmpty ()) in
  (try
    let rec loop () =
        let next_line = input_line ins in
        (*let new_itemset = List.map Hashtbl.hash (Str.split itemsep next_line) in*)
        let new_itemset = 
          List.fold_left 
            (function acc_its -> function item -> 
              let item = item_of_string in
              if List.mem item acc_its
              then acc_its
              else item :: acc_its
            )
            []
            (Str.split itemsep next_line)
        in 
        print_string ".";
        flush stdout;
        jdb := (add_itemset !jdb new_itemset);
        loop ()
    in loop ()
  with 
  End_of_file -> ());
  close_in ins;
  !jdb (*}}}*)


(* rm_infrequent db threshold; remove all items from the database that have
 * frequency strictly less than given threshold; notice that removing items will
 * not change the frequency of the items that are frequent *)
let rm_infrequent db threshold = filter db (function (_,freq) -> freq >= threshold)

(* restrict_item db item; remove all itemsets not containing item and in the/*{{{*/
 * remaining itemsets, remove item. This means that frequencies may go down for
 * all items remaining in the db.
 *)
(* the naive approach:
  * filter all itemsets containing item
  * remove the item from the resulting unique_items
  * constrain the database to this new reduced uniq_items
  *
  * we can reduce the number of iterations of the db as we know certain things
  *)
let restrict_item db item =
  match filter_itemset db (fun is -> List.exists ((=) item) is) with
  | DB (db, items) as db' -> constrain_db db' (M.remove item items)
  | EmptyDB -> EmptyDB
(*}}}*)

(* remove db item; removes the item from all itemsets in db/*{{{*/
 * the easy implementation
 * remove item from unique_items and constrain db to this new reduced db
 *)
let remove db item =
  match db with
  | DB (db, items) as db' -> constrain_db db' (M.remove item items)
  | EmptyDB -> EmptyDB
(*}}}*)

(*/*{{{*/
 * add_to_all db item ; adds item to all itemsets in db
*)
let add_to_all db item = match db with
  | DB (db, items) -> DB (
    [item] :: List.rev_map (fun itemset -> item :: itemset) db,
    update_item items item (fun c -> c + List.length db + 1)
  )
  | EmptyDB -> add_itemset EmptyDB [item]
(*}}}*)

(* {{{
 * add_db db1 db2; adds all entries from db1 to those of db2. The operation is
 * (should be) communicative so the order of the db's have no influence on the
 * result
 *)
let add_db db1 db2 =
  (*print_string ("Adding " ^ db2str db1);*)
  (*print_string ("To " ^ db2str db2);*)
  (* naive approach: for all itemsets in db1, add it to db2 *)
  (* more efficient: append itemsets and merge the unique_items maps *)
  let rec merge_unique items1 items2 = 
    M.fold (fun item -> fun freq -> fun acc_items -> update_item acc_items item
    (fun f -> f + freq)) items2 items1 in
  match db1 with
  | DB (db1, items1) as db1'-> (match db2 with
    | DB (db2, items2) -> 
        DB(db1 @ db2, merge_unique items1 items2)
    | EmptyDB -> db1')
  | EmptyDB -> db2

(* sizeOne db; returns one exactly when the db has only one itemset 
 * in it. This is a special case of a general size function, but for 
 * the moment we only need this sizeOne function.
 *)

let sizeOne db = match db with
(*| DB ([_],_) -> (print_string ("*IS* sizeOne: " ^ (db2str db)); flush stdout; true)*)
(*| _ -> (print_string ("Not sizeOne: " ^ (db2str db)); false)*)
| DB ([_],_) -> true
| _ -> false

(* function to test whether "itset1 ⊂ itset2" *)
let rec subset itset1 itset2 = 
  List.length itset1 < List.length itset2 &&
  List.for_all 
    (function it1 -> 
      List.exists ((=) it1) itset2
    )
    itset1

(* macro shorthand for subset *)
let (<<) a b = subset a b

(* function to test whether "itset1 ⊆ itset2" *)
let rec subseteq itset1 itset2 =
  List.for_all 
    (function it1 -> 
      List.exists ((=) it1) itset2
    )
    itset1

(* macro shorthand for subseqeq *)
let (<<=) a b = subseteq a b

(* the following function takes a database and (sub)itemset and computes the
 * support of the itemset in the given database *)
let rec get_support_itemset db subitemset =
  let get_sup acc itemset = 
    if subseteq subitemset itemset then acc + 1 else acc in
  match db with
  | DB(db, _) -> List.fold_left get_sup 0 db
  | EmptyDB -> 0

let ($) a b = get_support_itemset a b
  (*| itemset :: dbrest -> if subitemset subseteq itemset *)
      (*then 1 + get_support_itemset dbrest subitemset*)
      (*else get_support_itemset dbrest subitemset*)
  (*| [] -> 0*)


(* A db is considered closed if each itemset does not have a super-itemset where
 * the support wrt. to the original db is the same (or bigger which is
 * impossible)
 *
 * Suppose we have a database of closed itemsets, cdb. How can we extend this
 * database with one more itemset and still keep the property that the resulting
 * database is closed?
 *
 * If the database is empty, the task is trival, we can simply return the
 * database containing the itemset as sole element. If there are more than one
 * itemset in the database we must look at each element and consider whether to
 * include or not the already present itemset in the newly formed database.
 *
 * Below we assume that we never try to add an itemset that is already contained
 * in cdb. This reduces the number of cases to consider in the 'loop' function
 *)
exception Closed_DB_violation

(* add_itemset_cdb get_support cdb (new_itemset, new_support); try to add new_itemset
 * with new_support to cdb -- add_itemset_cdb may use get_support to know the
 * support of each itemset in cdb
 *)
let add_itemset_cdb get_support cdb (new_itemset, new_support) = 
  let rec loop itemsets = match itemsets with
  | itemset :: cdb -> (
        match (itemset << new_itemset, new_itemset << itemset) with
        (false, false) -> (* not related; both can be in the database *)
          add_itemset (loop cdb) itemset
      | (true, false) -> (* new_itemset is superset; If the supports are the same,
      (*we should remove itemset and add new_itemset unless other itemsets exist*)
      (*that can not coexist with new_itemset. If the supports differ, it could*)
      (*be safe to add new_itemset to the database while not removing itemset.*)*)
          if new_support = get_support itemset
          then
            loop cdb
          else
            add_itemset (loop cdb) itemset
      | (false, true) -> (* new_itemset is subset; If supports differ, it could be
      (*safe to add new_itemset otherwise, adding new_itemset would violate the*)
      (*closed itemsets property of the database. Thus, we signal an error. There*)
      (*will never be a need to remove (the sub) itemset since ... [pending good*)
      (*explanation] *)*)
          if new_support = get_support itemset
          then raise Closed_DB_violation
          else add_itemset (loop cdb) itemset
      | (true, true) -> (* this can not happen! a < b & b < a is never the case *)
          raise (Failure "add_itemset_to_cdb: this can not happen") )
  | [] -> add_itemset (makeEmpty ()) new_itemset  in
  match cdb with
  | DB(itemsets, items)  as db -> 
      (try loop itemsets with Closed_DB_violation -> db)
  | EmptyDB -> add_itemset (makeEmpty ()) new_itemset
    
  
  (*try loop cdb with Closed_DB_violation -> cdb [>}}}<]*)

(* close_db orig_db mined_db; function to produce database which has the closed
 * itemsets property. orig_db is the original database before datamining and
 * mined_db is the database after datamining. We need the original db to be able
 * to determine supports of itemsets in the mined database;
 *)
let close_db orig_db mined_db =
  let g_sup = function itemset -> orig_db$itemset in
  let lfun = function acc_cdb -> function itemset ->
    add_itemset_cdb g_sup acc_cdb (itemset, orig_db$itemset) in
  fold_itemset mined_db lfun (makeEmpty ())
  (*List.fold_left (function acc_cdb -> function itemset ->*)
      (*add_itemset_to_cdb g_sup acc_cdb (itemset, orig_db$itemset))*)
  (*[]*)
  (*mined_db*)



(* makeAllPerms db; given the database with size 1/n (exactly one itemset with n
 * elements), construct a new db which contains (2^n)-1 distinct itemsets each
 * of which uses a subset of the items in the original itemset
 *)
  (* the easy implementation uses predefined functions already in db.ml *)
  (*fold_unique db (fun item -> fun _ -> fun acc_db -> add_db (add_to_all acc_db item) acc_db) (makeEmpty ())*)
  (* the clever exploits that we know 1) the freq. of all items, 2) the
   * structure of all itemsets
   * each item will have a frequency of 2^(n-1)
   * each itemset is a subset of the original itemset (use powerset)
   * n is the number of items
   *)
(*let ones = ref 1*)

let prefixAll i ilist = List.fold_left (fun acc_lists -> fun xs -> 
  (i :: xs) :: xs ::  acc_lists) [[i]] ilist
let powerset ilist = List.fold_left (fun acc -> fun el -> (prefixAll el acc)) [] ilist

let makeAllPerms db = 
  print_endline "making makeAllPerms";
  let (num, items) = fold_unique db (fun item 1 (n, items_list) -> 
    (n + 1, item :: items_list)) (0,[]) in
  print_endline "done\npowerset... ";
  let db_list = powerset items in
  print_endline "uniq.items...";
  let uniq_list = List.fold_left (fun unacc -> fun item -> 
    update_item unacc item (fun _ -> 1 lsl (num-1))
  ) M.empty items in
  print_endline "done";
  (*let _ = print_string "done\n" in*)
  (*let _ = print_string "db: \n " in*)
  (*let _ = flush stdout in*)
  (*let _ = print_db (DB (db_list, uniq_list)) in*)
  (*let _ = print_string "done\n" in*)
  (*let _ = flush stdout in*)
  DB (db_list, uniq_list)
  
  (*fold_unique db (fun item -> fun 1 -> fun acc_db -> *)
    (*(print_string ((string_of_int !ones)  ^ " "); ones := !ones + 1;*)
     (*add_db (add_to_all acc_db item) acc_db)) (makeEmpty ())*)
  
(*let rec makeListLoop n acc = if n = 0 then acc else makeListLoop (n - 1) (n :: acc)*)
(*let rec makeList n = makeListLoop n []*)

(* sizeOf db; returns the number of itemsets in the db*)
let sizeOf db = match db with
| DB(db, _) -> List.length db
| EmptyDB -> 0

(* getItems db; returns the list of unique items in the db *)
let getItems db = fold_unique db 
  (fun item-> fun freq -> fun items -> item :: items) []

let interestRatio itemset sup =
  sup * (List.length itemset)

(* ------------ Test functions; uncomment when compiling ---------- *)

(*let ( ** ) db itemset = add_itemset db itemset*)
(*let ff  = function (_, freq) -> freq > 1*)
(*let tdb = (((((add_itemset (makeEmpty ()) *)
  (*["1";"2";"3";"4"]) ** ["1";"3";"5"]) ***)
  (*["5";"6";"2"]) ** ["1";"3";"5"]) ** ["4";"2"]) ***)
  (*["3"]*)
(*let fi = function item -> function itemset -> List.exists ((=) item) itemset*)

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

let rec dmine_simple db threshold =
  let localf = fun item -> fun freq -> fun (db, acc) ->
    let ndb = add_to_all (dmine_simple (restrict_item db item) threshold) item in
    let acc = add_db ndb acc in
    let db  = remove db item in
    (db, acc) in
  let db = rm_infrequent db threshold in
  if isEmpty db
  then makeEmpty ()
  else snd (fold_unique db localf (db, makeEmpty ()))

let rec dmine db threshold =
  let localf = fun item -> fun freq -> fun (db, acc) ->
    let ndb = add_to_all (dmine (restrict_item db item) threshold) item in
    let acc = add_db ndb acc in
    let db  = remove db item in
    (db, acc) in
  let db = rm_infrequent db threshold in
  if isEmpty db
  then makeEmpty ()
  else 
    if sizeOne db
    then makeAllPerms db
    else snd (fold_unique db localf (db, makeEmpty ()))

let dmine_cls db_orig threshold =
  let get_items db = fold_unique db (fun item fre ls -> item :: ls) [] in
  let g_sup iset = db_orig $ iset in
  let (++) iset db = 
    print_string "+";
    flush stdout;
    add_itemset_cdb g_sup db (iset, g_sup iset) in
  let rec gen acc_db current_db current_iset =
    let next_db = rm_infrequent current_db threshold in
    if isEmpty next_db
    then current_iset ++ acc_db
    else
      let next_items = get_items next_db in
      List.fold_left (fun acc_db item ->
        let next_iset = item :: current_iset in
        let restricted_db = restrict_item current_db item in
        gen acc_db restricted_db next_iset
      ) acc_db next_items in
  gen (makeEmpty ()) db_orig []

end
