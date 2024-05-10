(*@ open Sequence *)

type 'a t
(*@ mutable model : 'a Sequence.t *)

val create : unit -> 'a t
(*@ q = create ()
    ensures q = empty *)

(* val is_empty : 'a t -> bool *)
(* (\*@ b = is_empty q *)
(*     preserves q @ 'a t *)
(*     ensures b <-> q = empty *\) *)

(* val push : 'a t -> 'a -> unit *)
(* (\*@ push p x *)
(*     modifies p *)
(*     ensures p = cons x (old p) *)
(* *\) *)

(* val pop : 'a t -> 'a *)
(* (\*@ r = pop p *)
(*     modifies p *)
(*     raises Not_found *)
(*     ensures (old p) = cons r p *\) *)

(* val clear : 'a t -> unit *)
(* (\*@ clear p *)
(*     modifies p *)
(*     ensures p = empty *\) *)

(* val concat : 'a t -> 'a t -> unit *)
(* (\*@ concat q1 q2 *)
(*     modifies q1 *)
(*     modifies q2 *)
(*     ensures q1 = old (q1 ++ q2) *)
(*     ensures q2 = empty *)
(* *\) *)

(* val rev_append : 'a t -> 'a t -> unit *)
(* (\*@ rev_append p1 p2 *)
(*     modifies p1 *)
(*     modifies p2 *)
(*     ensures p1 = empty *)
(*     ensures p2 = old (rev p1 ++ p2) *\) *)
