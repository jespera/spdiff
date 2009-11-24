let f n_orig = 
  let rec loop n =
          begin
        save_cursor ();
        print_string [on_default] 
          (string_of_int n ^ "/" ^ string_of_int n_orig);
        restore_cursor ();
        if n > 0 then loop (n - 1);
    end in
    loop n_orig
  ;;       
