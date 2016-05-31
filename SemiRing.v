Require Export HoTTMath.Monoid.

Class Plus A := plus :> SgOp A.
Class Mult A := mult :> SgOp A.

Instance plus_op `{pl : Plus A} : SgOp A := pl.
Instance mult_op `{ml : Mult A} : SgOp A := ml.

Class Zero A := zero :> A.
Class One A := one :> A.

Instance zero_id `{z : Zero A} : Id A := z.
Instance one_id `{u : One A} : Id A := u.

Infix "+" := plus.
Notation "(+)" := plus (only parsing).
Notation "( x +)" := (plus x) (only parsing).
Notation "(+ x )" := (fun y => y + x) (only parsing).

Infix "*" := mult.
Notation "( x *.)" := (mult x) (only parsing).
Notation "(.*.)" := mult (only parsing).
Notation "(.* x )" := (fun y => y * x) (only parsing).

Notation "0" := zero.
Notation "1" := one.
Notation "2" := (1 + 1).
Notation "3" := (1 + (1 + 1)).
Notation "4" := (1 + (1 + (1 + 1))).

Section Definitions.

Context `{z : Zero A} `{u : One A} `{pl : Plus A} `{ml : Mult A}.

Class LeftDistributes := left_distributes : forall a b c, a * (b + c) = a * b + a * c.
Class RightDistributes := right_distributes : forall a b c, (b + c) * a = b * a + c * a.

Class Distributes :=
  { distributes_left :> LeftDistributes
  ; distributes_right :> RightDistributes }.

Class LeftAbsorbs := left_absorbs : forall x, 0 * x = 0.
Class RightAbsorbs := right_absorbs : forall x, x * 0 = 0.

Class Absorbs :=
  { absorbs_left :> LeftAbsorbs
  ; absorbs_right :> RightAbsorbs }.

Class SemiRing :=
  { semiring_additive :> Monoid A (i:=zero_id) (op:=plus_op) 
  ; semiring_multiplicative :> Monoid A (i:=one_id) (op:=mult_op)
  ; semiring_distributes :> Distributes
  ; semiring_absorbs :> Absorbs }.

Lemma semiring_from_cancelling
  `(StrongMonoid A (i:=zero_id) (op:=plus_op))
  `(Monoid A (i:=one_id) (op:=mult_op))
  `(Distributes)
  : SemiRing.
Proof.
split;try apply _.
split.
- intros x.
  apply (left_cancels (0 * x)).
  path_via (0 * x).
  path_via ((0 + 0) * x).
  + apply symmetry. apply right_distributes.
  + apply (ap (fun a => a * x)).
    apply (left_id (op:=plus_op) (i:=zero_id)).
  + apply symmetry.
    apply (right_id (op:=plus) (i:=zero_id)).
- intros x.
  apply (left_cancels (x * 0)).
  path_via (x * 0).
  path_via (x * (0 + 0)).
  + apply symmetry. apply left_distributes.
  + apply ap.
    apply (left_id (op:=plus_op) (i:=zero_id)).
  + apply symmetry.
    apply (right_id (op:=plus) (i:=zero_id)).
Defined.

End Definitions.

