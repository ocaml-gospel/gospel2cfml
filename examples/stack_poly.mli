(*@ open Sequence *)

type 'a t
(*@ mutable model : 'a Sequence.t *)

val create : unit -> 'a t
(*@ q = create ()
    produces q @ 'a t
    ensures q = empty
*)

val push : 'a t -> 'a -> unit
(*@ push q x
    modifies q @ 'a t
    ensures q = cons x (old q)
*)

val pop_opt : 'a t -> 'a option
(*@ r = pop_opt q
    consumes q @ 'a t
    produces q @ 'a t

    ensures match r with
    |None -> old q = empty && q = empty
    |Some r_val -> old q = cons r_val q
*)

val top_opt : 'a t -> 'a option
(*@ r = top_opt q
    preserves q @ 'a t

    ensures match r with
    |None -> q = empty
    |Some r -> q <> empty && r = hd q
*)

val clear : 'a t -> unit
(*@ clear q
    consumes q @ 'a t
    produces q @ 'a t
    ensures q = empty *)

val copy : 'a t -> 'a t
(*@ q2 = copy q1
    preserves q1 @ 'a t
    produces q2 @ 'a t
    ensures q2 = q1
*)

val is_empty : 'a t -> bool
(*@ b = is_empty q
    preserves q @ 'a t
    ensures b <-> q = empty *)

val length : 'a t -> int
(*@ l = length q
    preserves q @ 'a t
    ensures Sequence.length q = l *)

val transfer : 'a t -> 'a t -> unit
(*@ transfer q1 q2
    produces q1 @ 'a t
    produces q2 @ 'a t
    consumes q1 @ 'a t
    consumes q2 @ 'a t

    ensures q1 = empty
    ensures q2 = old (q2 ++ q1) *)

(*missing : pop, 'a take, iter, fold, 'a to_seq, add_seq, of_seq *)

(* predicate is_eq (A : 'a type) 
(* 'a this predicate does not hold for unwoned mutable structures and functions*)

val st_eq : 'a -> 'a -> bool
(* b = st_eq x y
    requires is_eq 'a
    ensures b <-> x = y
 *)

(* predicate unowned (A : 'a type) *)



(*
{ R x Mx * R y My * [unowned R] } ph_eq x y {[x = y]}

val ph_eq : 'a -> 'a -> bool
(* b = st_eq x y
    requires addressable 'a
    ensures b <-> &x = &y
 *)

{ [is_loc x && is_loc y] } ph_eq x y {[x = y]}

 predicates over 'a types, 'a type classes *)
(* increase clarity in spatial specs
   adressable vs unowned *)
 *)
