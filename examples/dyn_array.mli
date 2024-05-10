(*@ open Sequence *)

type t
(*@ model : int sequence *)

val create : unit -> t
(*@ a = create ()
    ensures a = empty *)

val make : int -> int -> t
(*@ a = make n e
    ensures a = init n (fun _ -> e) *) 

val get : t -> int -> int
(*@ r = get a i
    ensures r = a[i] *)

val set : t -> int -> int -> unit
(*@ set a i e 
    modifies a
    requires 0 <= i < length a (* <- TODO replace with exceptional postcond *)
    ensures a = old (set a i e) *)

val length : t -> int
(*@ l = length a 
    ensures l = length a *)

val is_empty : t -> bool
(*@ b = is_empty a
    ensures b <-> (a = empty) *)

val find_last : t -> int option
(*@ r = find_last a
    ensures match r with
    |None -> a = empty && old a = empty
    |Some r -> r = a[length a - 1] *)
val copy : t -> t
(*@ c = copy a
    ensures c = a *)

val add_last : t -> int -> unit
(*@ add_last a e 
    modifies a
    ensures a = (old a) ++ (singleton e) *)

val append : t -> t -> unit
(*@ append a1 a2 
    modifies a1 
    ensures a1 = (old a1) ++ a2 *)


val pop_last_opt :  t -> int option
(*@ r = pop_last_opt a
    modifies a
    ensures match r with
    |None -> a = empty && old a = empty
    |Some r -> a ++ singleton r = old a *)

val remove_last : t -> unit
(*@ r = remove_last a
    modifies a
    ensures old a = empty -> a = empty
    ensures a <> empty -> a = old (a[.. length a - 1]) *)

val truncate : t -> int -> unit
(*@ r = truncate a n
    modifies a
    requires n >= 0
    ensures n >= length a -> a = old a
    ensures n < length a -> a = old (a[.. n]) *)
val clear : t -> unit
(*@ r = clear a
    modifies a
    ensures a = empty *)
