type ref
(*@ mutable model : integer *)

val ref : int -> ref
(*@ r = ref v
    ensures r = v *)

val get : ref -> int
(*@ v = get r
    ensures r = v
*)

val update : ref -> int -> unit
(*@ update r v
    modifies r @ ref
    ensures r = v *)
