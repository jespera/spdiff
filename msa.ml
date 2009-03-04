let (+>) o f = f o

let falign callb s1 s2 s3 = 
  let s1_len = Array.length s1 in
  let s2_len = Array.length s2 in 
  let s3_len = Array.length s3 in
  let ( ** ) arr x = if x = 0 then None else Some (arr.(x-1)) in
  let acc s i = s.(i-1) in
  let ss1 i = acc s1 i in
  let ss2 i = acc s2 i in
  let ss3 i = acc s3 i in
  let s (si, sj, sk) = match si, sj, sk with
    | None  , None  , _      -> true
    | _     , None  , None   -> true
    | Some i, Some j, Some k -> (
	s1 ** i = s2 ** j || 
          s2 ** j  = s3 ** k ||
	  callb (ss1 i) (ss2 j) (ss3 k)
      )
    
    | Some i, Some j, None   -> s1 ** i = s2 ** j
    | None  , Some j, Some k -> s2 ** j = s3 ** k
    | _                      -> false in
  let rec loop i j k =
    i = 0 && j = 0 && k = 0 || (
      match i, j, k with
	| 0, 0, 0 -> raise Not_found
	| 0, 0, _ -> true
	| 0, _, 0 -> false
	| 0, _, _ -> s2 ** j = s3 ** k && loop 0 (j-1) (k-1)
	| _, 0, 0 -> true
	| _, 0, _ -> false
	| _, _, 0 -> s1 ** i = s2 ** j && loop (i-1) (j-1) 0
	| _, _, _ ->
	    (
	      (loop (i-1) (j-1) (k-1) && 
		 s(Some i, Some j, Some k)      
	      ) ||
		(loop (i  ) (j-1) (k-1) &&
		   s(None, Some j, Some k)
		) ||
		(loop (i-1) (j-1) (k  ) &&
		   s(Some i, Some j, None)
		) ||
		(loop (i  ) (j  ) (k-1) &&
		   s(None, None, Some k)
		) ||
		(loop (i-1) (j  ) (k  ) &&
		   s(Some i, None, None)
		)
	    )
    )
  in
    loop s1_len s2_len s3_len

let align s1 s2 s3 =
  let s1_len = Array.length s1 + 1 in
  let s2_len = Array.length s2 + 1 in
  let s3_len = Array.length s3 + 1 in 
    
  let r = Array.init s1_len
    (fun _ -> Array.init s2_len
       (fun _ -> Array.init s3_len
	  (fun _ -> false)
       )
    )

  (* false  *)
  (* +> (fun _ -> Array.init s3_len *)
  (* +> (fun _ -> Array.init s2_len) *)
  (* +> (fun _ -> Array.init s1_len) *)
  in

  let ( ** ) arr x = if x = 0 then None else Some (arr.(x-1)) in
  let s (si, sj, sk) = match si, sj, sk with
    | None  , None  , _      -> true
    | _     , None  , None   -> true
    | Some i, Some j, Some k -> s1 ** i = s2 ** j || s2 ** j  = s3 ** k
    | Some i, Some j, None   -> s1 ** i = s2 ** j
    | None  , Some j, Some k -> s2 ** j = s3 ** k
    | _                      -> false
  in
    r +> Array.iteri
      (fun i i_arr ->
	 i_arr +> Array.iteri 
	   (fun j j_arr ->
	      j_arr +> Array.iteri
		(fun k elem ->
		   r.(i).(j).(k) <- 
		     match i, j, k with
		       | 0, 0, 0 -> false
		       | 0, 0, _ -> true
		       | 0, _, 0 -> false
		       | 0, _, _ -> s2 ** j = s3 ** k
		       | _, 0, 0 -> true
		       | _, 0, _ -> false
		       | _, _, 0 -> s1 ** i = s2 ** j
		       | _, _, _ ->
			   (r.(i-1).(j-1).(k-1) && s1 ** i = s2 ** j && s2 ** j = s3 ** k) || 
			   (r.(i-1).(j-1).(k-1) && s(Some i,Some j, Some k)) || (* a,b,c *)
			     (r.(i  ).(j-1).(k-1) && s(None  ,Some j, Some k)) || (* -,b,c *)
			     (r.(i-1).(j-1).(k  ) && s(Some i,Some j, None  )) || (* a,b,- *)
			     (r.(i  ).(j  ).(k-1) && s(None  ,None  , Some k)) || (* -,-,c *)
			     (r.(i-1).(j  ).(k  ) && s(Some i,None  , None  ))    (* a,-,- *)
		)
	   )
      );
    r

let get_alignment m s1 s2 s3 = 
  let s1_len = Array.length s1 in
  let s2_len = Array.length s2 in 
  let s3_len = Array.length s3 in
  let rec loop i j k =
    i = 0 && j = 0 && k = 0 ||
    (try m.(i).(j).(k) with _ -> false) && (
      loop (i-1) (j-1) (k-1) ||
	loop (i  ) (j-1) (k-1) ||
	loop (i-1) (j-1) (k  ) ||
	loop (i  ) (j  ) (k-1) ||
	loop (i-1) (j  ) (k  )
    )
  in
    loop s1_len s2_len s3_len
