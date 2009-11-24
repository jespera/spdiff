let version = "0.1.5"

let path = 
  try (Sys.getenv "COCCINELLE_HOME") 
  with Not_found->"`pwd`/share/coccinelle"

let std_iso = ref (Filename.concat path "standard.iso")
let std_h   = ref (Filename.concat path "standard.h")
