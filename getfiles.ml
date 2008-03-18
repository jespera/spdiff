(* small script to read a git-commit from stdin and extract files *)

(* read lines from stdin and return list of lines 
 * preserves ordering of lines in the list *)
let read_commit_stdin () =
  let lines = ref [] in
  let rec loop () =
      lines := read_line () :: !lines;
      loop() in
  try (loop ()) with End_of_file -> List.rev (!lines)

let indexmatch = Str.regexp "^index"
let indexsplit = Str.regexp "index\\| +\\|\\.\\."
let filesmatch = Str.regexp "---"
let filegroup  = Str.regexp "/.*"

exception Notfound of string

let rec find_loc locm err ls = 
  match ls with
  | [] -> raise (Notfound err)
  | l :: ls when Str.string_match locm l 0 -> (l, ls)
  | _ :: ls -> find_loc locm err ls

let find_index = find_loc indexmatch "index"
let find_files = find_loc filesmatch "file"

exception Noindices

let get_indices l =
  let ls = Str.split indexsplit l in
  match ls with
  | _ :: i1 :: i2 :: _ -> 
      (*print_endline "indices: ";*)
      (*print_endline (i1 ^ ", " ^ i2);*)
      (i1, i2)
  | _ -> raise Noindices

let get_file l =
  let lastindex = String.length l - 1 in
  let _   = Str.search_backward filegroup l lastindex in
  let fs  = Str.matched_string l in
  let len = String.length fs in
  let name= String.sub fs 1 (len - 1) in
  (name ^ ".orig", name ^ ".new")

let next_files ls =
  let (il, ls1) = find_index ls in
  let (i1, i2)  = get_indices il in
  let (fl, ls2) = find_files ls1 in
  let (oname, nname) = get_file fl in
  ((i1,i2,oname,nname),ls2)


let main () =
  (* output file pairs to dir *)
  let dir = Sys.argv.(1) in
  print_endline ("[main] outputing to " ^ dir);
  let ls = read_commit_stdin () in
  print_endline "[ls]";
  let rec loop ls =
    try
      let (i1, i2, oname, nname),ls = next_files ls in
      let mkc  = function c -> (Sys.command c; ()) in
      let cmd1 = 
        if i1 = "0000000"
        then "echo \" \""
        else "git show " ^ i1 ^ " > " ^ dir ^ oname in
      let cmd2 = 
        if i2 = "0000000"
        then "echo \" \""
        else "git show " ^ i2 ^ " > " ^ dir ^ nname in
      print_endline ("File: " ^ i1 ^ " -> " ^ i2);
      let cmd3 = "echo " ^ oname ^ "  " ^ nname ^ ">> " ^ dir ^ "specfile" in
      List.iter mkc [cmd1;cmd2;cmd3];
      loop ls
    with _ -> () in
  loop ls

let _ = main();
