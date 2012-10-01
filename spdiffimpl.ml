open Spdiff
open Gtree

module SpdiffImpl : Spdiff =
  struct
    type term = gtree
    type term_pattern = gtree
    type term_patch = (term_pattern * term_pattern) list
    
    type changeset = (term * term) list
    
    module Term = 
      struct
        open Hashcons
        type t = gtree
        let compare t1 t2 = 
          if t1 == t2 then 0
          else if t1.hkey < t2.hkey then -1 else 1 
      end

    module TermSet = Set.Make(Term)

    let get_subterms t =
      let rec loop acc subt = match view subt with
      | A _ -> TermSet.add subt acc
      | C(_, ts) -> List.fold_left loop (TermSet.add subt acc) ts in
      loop TermSet.empty t

    (*
     * Given a changeset, find the set of term-patterns that occur in all of the
     * LHS terms.
     *
     * The näive approach:
     * compute all subterms for all LHS terms;
     * for each subterm, try to anti-unify with all subterms in other
     * term-pairs
     *) 
    let get_term_patterns cset = []
    (*
      let lhs_terms = List.rev_map fst cset in
      let lhs_subterm_sets = List.rev_map get_subterms lhs_terms in
      let g subterm acc_term_patterns =

      in
      let f acc_term_patterns term_set =
        TermSet.fold g term_set acc_term_patterns 
      in
      TermSet.elements (
        List.fold_left f TermSet.empty lhs_subterm_sets
      )
*)
    let get_term_patches cset = []
  end
