module type Itemset_type =
  sig
    type t
    val compare : t -> t -> int
  end
