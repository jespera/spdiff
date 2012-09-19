module type Spdiff =
  sig
    type term
    type term_pattern
    type term_patch

    type changeset

    val get_term_patterns : changeset -> term_pattern list
    val get_term_patches : changeset -> term_patch list
  end

