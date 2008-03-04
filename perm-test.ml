
let rec prefix a lists =
(*print_endline ("prefixing " ^*)
(*string_of_gtree str_of_ctype str_of_catom a);*)
match lists with(*{{{*)
| [] -> []
| lis :: lists -> (a :: lis) :: prefix a lists(*}}}*)

let rec prefix_all lis lists =
	match lis with(*{{{*)
  | [] -> []
	| elem :: lis -> (prefix elem lists) @ prefix_all lis lists(*}}}*)
			
let rec gen_perms lists =
  print_string "gen_perms sizes: ";
  List.iter (fun ec -> 
    print_string "<";
    print_string (string_of_int (List.length ec));
    print_string "> ";
    ) lists;
  print_newline ();
  assert(not(List.exists ((=) []) lists));
match lists with(*{{{*)
| [] -> [[]]
| lis :: lists -> prefix_all lis (gen_perms lists)(*}}}*)

let tv = [[1];[2]]
