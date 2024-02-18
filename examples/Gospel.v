Require TLC.LibLogic.
Require TLC.LibMap.
Require Import List.
(* Lists *)

Definition hd {A} {Inh:LibLogic.Inhab A} (l : list A) : A :=
  match l with
  |nil => TLC.LibLogic.arbitrary
  |x::_ => x
  end.

Lemma hd_inst :
  forall A (x : A) l (Inh : LibLogic.Inhab A), (hd (x::l)) = x.
Proof. auto. Qed.

Opaque hd.  

Definition tl {A} (l: list A) : list A :=
  match l with
  |nil => nil
  |_::t => t
  end.

Lemma tl_inst :
  forall A (x : A) l, tl (x::l) = l.
Proof. auto. Qed.

Opaque tl.

Definition singleton {A} (x : A) : list A := cons x nil.

Lemma singleton_inst :
  forall A (x : A), singleton x = cons x nil.
Proof. auto. Qed.

Opaque singleton.

