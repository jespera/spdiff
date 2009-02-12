type 'a hash_consed = { hkey : int; tag : int; node : 'a; }
val gentag : unit -> int
type 'a t = {
  mutable table : 'a hash_consed Weak.t array;
  mutable totsize : int;
  mutable limit : int;
}
val create : int -> 'a t
val clear : 'a t -> unit
val fold : ('a hash_consed -> 'b -> 'b) -> 'a t -> 'b -> 'b
val iter : ('a hash_consed -> 'b) -> 'a t -> unit
val count : 'a t -> int
val next_sz : int -> int
val resize : 'a t -> unit
val add : 'a t -> 'a hash_consed -> unit
val hashcons : 'a t -> 'a -> 'a hash_consed
val stats : 'a t -> int * int * int * int * int * int
module type HashedType =
  sig type t val equal : t -> t -> bool val hash : t -> int end
module type S =
  sig
    type key
    type t
    val create : int -> t
    val clear : t -> unit
    val hashcons : t -> key -> key hash_consed
    val iter : (key hash_consed -> unit) -> t -> unit
    val stats : t -> int * int * int * int * int * int
  end
module Make :
  functor (H : HashedType) ->
    sig
      type key = H.t
      type t
      val create : int -> t
      val clear : t -> unit
      val hashcons : t -> key -> key hash_consed
      val iter : (key hash_consed -> unit) -> t -> unit
      val stats : t -> int * int * int * int * int * int
    end
