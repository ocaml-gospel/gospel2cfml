Require TLC.LibLogic.

(* Lists *)

Parameter hd_gospel : forall {A} {Inh:LibLogic.Inhab A}, list A -> A.

Axiom hd_gospel_axiom :
  forall A (x : A) l (Inh : LibLogic.Inhab A), (hd_gospel (x::l)) = x.

Parameter tl_gospel : forall {A}, list A -> list A.

Axiom tl_gospel_axiom :
  forall A (x : A) l, tl_gospel (x::l) = l.

Definition singleton {A} (x : A) : list A := cons x nil.

(* Maps *)

Parameter update : forall {A} {B}, (A -> B) -> A -> B -> (A -> B).

Axiom update_new : forall A B (f : A -> B) k v,
    (update f k v) k = v.

Axiom update_old : forall A B (f : A -> B) k1 k2 v, 
    k1 <> k2 -> (update f k1 v) k2 = f k2.

