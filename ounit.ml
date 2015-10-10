open OUnit2
open Diff


(* tests term merging *)

(*			 TODO test merge_tus:wa
														 a
 *)													 

(* tests of changeset merging *)

let test_empty_changeset_becomes_empty_update_set test_ctx =
	Diff.find_simple_updates_merge_changeset 0 []
	|> assert_equal [] 

let test_singleton_atomic_changeset_becomes_singleton_update test_ctx =
	let a1  = Gtree.mkA("const","42")
	and a1' = Gtree.mkA("const","43")
	in
	(
		Diff.find_simple_updates_merge_changeset 1 [a1,a1']
		|> assert_equal [Difftype.UP(a1,a1')]
	)

let test_multiple_equal_atomic_becomes_singleton_update test_ctx =
	let a1  = Gtree.mkA("const","42")
	and a1' = Gtree.mkA("const","43")
	in
	Diff.find_simple_updates_merge_changeset 2 [a1,a1';
																							a1,a1']
	|> assert_equal [Difftype.UP(a1,a1')]

let test_multiple_nonequal_atomic_becomes_empty test_ctx =
	let a1  = Gtree.mkA("const","42")
	and a1' = Gtree.mkA("const","43")
	and b1  = Gtree.mkA("const", "117")
	and b1' = Gtree.mkA("const", "118")
	in
	Diff.find_simple_updates_merge_changeset 2 [b1,b1';
																							a1,a1']
	|> assert_equal []

let test_multiple_nonequal_with_threshold_atomic_becomes_id test_ctx =
	let a1  = Gtree.mkA("const","42")
	and a1' = Gtree.mkA("const","43")
	and b1  = Gtree.mkA("const", "117")
	and b1' = Gtree.mkA("const", "118") in
	Diff.find_simple_updates_merge_changeset 1 [b1,b1';
																							a1,a1']
	|> List.length
	|> assert_equal 2

let test_single_merged_with_global_threshold test_ctx =
	let f   = Gtree.mkA("const","f") in
	let x   = Gtree.mkA("const","x") in
	let fx  = Gtree.mkC("call",[f;x]) in
	let fxx = Gtree.mkC("call",[f;x;x]) in
	let y   = Gtree.mkA("const","y") in
	let fy  = Gtree.mkC("call",[f;y]) in
	let fyy = Gtree.mkC("call",[f;y;y]) in
	Diff.find_simple_updates_merge_changeset 2 [fx,fxx;
																							fy,fyy]
	|> List.length
	|> assert_equal 1

let test_single_merged_with_global_threshold_and_nesting test_ctx =
	let stmt x = Gtree.mkC("stmt",[x]) in 
	let f   = Gtree.mkA("const","f") in
	let x   = Gtree.mkA("const","x") in
	let fx  = Gtree.mkC("call",[f;x]) in
	let fxx = Gtree.mkC("call",[f;x;x]) in
	let sfx = stmt fx in
	let sfxx = stmt fxx in
	let y   = Gtree.mkA("const","y") in
	let fy  = Gtree.mkC("call",[f;y]) in
	let fyy = Gtree.mkC("call",[f;y;y]) in
	let sfy = stmt fy in
	let sfyy = stmt fyy in
	Diff.find_simple_updates_merge_changeset 2 [sfx,sfxx;
																							sfy,sfyy]
	|> List.length
	|> assert_equal 2


		
let changeset_merging =
	"changeset_merging" >:::
		[
			"test1" >:: test_empty_changeset_becomes_empty_update_set;
			"test2" >:: test_singleton_atomic_changeset_becomes_singleton_update;
			"test3" >:: test_multiple_equal_atomic_becomes_singleton_update;
			"test4" >:: test_multiple_nonequal_atomic_becomes_empty;
			"test5" >:: test_multiple_nonequal_with_threshold_atomic_becomes_id;
			"test6" >:: test_single_merged_with_global_threshold;
			"test7" >:: test_single_merged_with_global_threshold_and_nesting
		]
							 
(* uncategorized tests... for now *)
							 
let simple_diff_cmd test_ctx =
	let a1  = Gtree.mkA("const","42")
	and a1' = Gtree.mkA("const","43")
	in
	assert_equal (Difftype.UP(a1,a1'))
							 (Difftype.UP(a1,a1'))


let rm_dub_removes_duplicate_ups test_ctx =
	let a1  = Gtree.mkA("const","42")
	and a1' = Gtree.mkA("const","43")
	in
	Diff.rm_dub [Difftype.UP(a1,a1'); Difftype.UP(a1,a1')]
	|> assert_equal [Difftype.UP(a1,a1')]									

									
let misc_tests =
	"misc" >:::
		[
			"test4" >:: simple_diff_cmd;
			"test5" >:: rm_dub_removes_duplicate_ups
		]


(* entry point running all tests *)
			
let () =
	run_test_tt_main changeset_merging;
	run_test_tt_main misc_tests
