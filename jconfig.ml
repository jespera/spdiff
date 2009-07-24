(* global configuration used everywhere *)

let verbose = ref false
let print_abs = ref false
let read_generic = ref false

let (+>) o f = f o

let counter_tick counter total =
  begin
    ANSITerminal.save_cursor ();
    ANSITerminal.print_string 
      [ANSITerminal.on_default](
	counter +> string_of_int 
	^ "/" ^	total +> string_of_int);
    ANSITerminal.restore_cursor();
    flush stdout;
  end

