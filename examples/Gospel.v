Require TLC.LibLogic.
Require Import TLC.LibMap.

(* Lists *)
Parameter hd_gospel : forall {A} {Inh:LibLogic.Inhab A}, list A -> A.

Axiom hd_gospel_axiom :
  forall A (x : A) l (Inh : LibLogic.Inhab A), (hd_gospel (x::l)) = x.

Parameter tl_gospel : forall {A}, list A -> list A.

Axiom tl_gospel_axiom :
  forall A (x : A) l, tl_gospel (x::l) = l.

Definition singleton {A} (x : A) : list A := cons x nil.

(* Maps *)


