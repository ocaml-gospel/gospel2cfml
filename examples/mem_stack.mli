(*@ type 'a memory *)

(*@ predicate extend (m m': 'a memory) *)
(*@ axiom refl: forall m: 'a memory. extend m m *)
(*@ axiom tran: forall m1 m2 m3: 'a memory.
      extend m1 m2 -> extend m2 m3 ->
      extend m1 m3 *)

(*@ val create_mem : unit -> 'a memory *)

(* Basic operations on ephemeral stacks. *)
type 'a estack
(*@ mutable model eview: 'a memory -> 'a Sequence.t *)

(*@ axiom estack_mon: forall m m': 'a memory, e: 'a estack.
      extend m m' -> e.eview m = e.eview m' *)

val ecreate : 'a -> 'a estack
(*@ r = ecreate [m: 'a memory] x
      ensures r.eview m = Sequence.empty *)

val epush : 'a estack -> 'a -> unit
(*@ epush [m: 'a memory] s x
      modifies s
      ensures  s.eview m = Sequence.cons x (old s.eview m) *)

val epop : 'a estack -> 'a
(*@ r = epop [m: 'a memory] s
      modifies s
      requires s.eview m <> Sequence.empty
      ensures  (old s.eview m) = Sequence.cons r (s.eview m) *)

(* Basic operations on persistent stacks. *)
type 'a pstack
(*@ model pview: 'a memory -> 'a Sequence.t
    mutable model internal: unit *)

(*@ axiom estack_mon: forall m m': 'a memory, p: 'a pstack.
      extend m m' -> p.pview m = p.pview m' *)

val pcreate : 'a -> 'a pstack
(*@ r, [m': 'a memory] = pcreate [m: 'a memory] x
      ensures r.pview m' = Sequence.empty
      ensures extend m m' *)

val ppush : 'a pstack -> 'a -> 'a pstack
(*@ r, [m': 'a memory] = ppush [m: 'a memory] s x
      modifies s
      ensures  r.pview m' = Sequence.cons x (s.pview m)
      ensures  extend m m' *)

val ppop : 'a pstack -> 'a pstack * 'a
(*@ (rs, res) = ppop [m: 'a memory] s
      modifies s
      requires s.pview m <> Sequence.empty
      ensures  s.pview m = Sequence.cons res (rs.pview m) *)

(* Conversions. *)
val pstack_to_estack : 'a pstack -> 'a estack
(*@ re = pstack_to_estack [m: 'a memory] ps
      ensures re.eview m = ps.pview m *)

val estack_to_pstack : 'a estack -> 'a pstack
(*@ rp, [m': 'a memory] = estack_to_pstack [m: 'a memory] es
      consumes es
      ensures  rp.pview m' = es.eview m
      ensures  extend m m' *)
