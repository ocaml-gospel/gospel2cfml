(*@ open Sequence *)

type t
(*@ mutable model : int Sequence.t *)

val create : unit -> t
(*@ q = create ()
    produces q @ t
    ensures q = empty
*)

val push : t -> int -> unit
(*@ push q x
    modifies q @ t
    ensures q = cons x (old q) 
*)

val pop_opt : t -> int option
(*@ r = pop_opt q
    consumes q @ t
    produces q @ t
    
    ensures match r with
    |None -> old q = empty && q = empty
    |Some r_val ->
    old q = cons r_val q
 *)

val top_opt : t -> int option
(*@ r = top_opt q
    preserves q @ t
    
    ensures match r with
    |None -> q = empty
    |Some r ->
      q <> empty && r = hd q
 *)

val clear : t -> unit
(*@ clear q
    consumes q @ t
    produces q @ t
    ensures q = empty *)

val copy : t -> t
(*@ q2 = copy q1
    preserves q1 @ t
    produces q2 @ t
    ensures q2 = q1
 *)


val is_empty : t -> bool
(*@ b = is_empty q
    preserves q @ t
    ensures b <-> q = empty *)

val length : t -> int
(*@ l = length q 
    preserves q @ t
    ensures Sequence.length q = l *)

val transfer : t -> t -> unit
(*@ transfer q1 q2
    produces q1 @ t
    produces q2 @ t
    consumes q1 @ t
    consumes q2 @ t

    ensures q1 = empty
    ensures q2 = q2 ++ (old q1) *)

(*missing : pop, take, iter, fold, to_seq, add_seq, of_seq *)
                        
(* predicate is_eq (A : Type) 
(* this predicate does not hold for unwoned mutable structures and functions*)

val st_eq : 'a -> 'a -> bool
(* b = st_eq x y
    requires is_eq 'a
    ensures b <-> x = y
 *)

(* predicate unowned (A : Type) *)



(*
{ R x Mx * R y My * [unowned R] } ph_eq x y {[x = y]}

val ph_eq : 'a -> 'a -> bool
(* b = st_eq x y
    requires addressable 'a
    ensures b <-> &x = &y
 *)

{ [is_loc x && is_loc y] } ph_eq x y {[x = y]}

 predicates over types, type classes *)
(* increase clarity in spatial specs
   adressable vs unowned *)
 *)
