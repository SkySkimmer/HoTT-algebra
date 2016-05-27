Require Export HoTTMath.Monoid.

Class Opposite A := opposite : A -> A.

Notation "- x" := (opposite x).
Notation "(-)" := opposite (only parsing).
Notation "x - y" := (x ++ -y).

Section Definitions.

Context `{M:Monoid A} {opp:Opposite A}.

Class LeftOpposite := left_opposite : forall x, - x ++ x = id.
Class RightOpposite := right_opposite : forall x, x - x = id.

Class IsOpposite :=
  { opposite_left :> LeftOpposite
  ; opposite_right :> RightOpposite }.

Class Group :=
  { group_monoid :> Monoid A
  ; group_opposite :> IsOpposite }.

End Definitions.

Lemma group_cancels `{Group A} : forall x, Cancels x.
Proof.
split.
- intros y z eq.
  path_via (id ++ z).
  path_via ((-x ++ x) ++ z).
  path_via (-x ++ (x ++ z)).
  path_via (-x ++ (x ++ y)).
  path_via ((-x ++ x) ++ y).
  path_via (id ++ y).
  + apply symmetry. apply left_id.
  + apply (ap (fun a => a ++ y)).
    apply symmetry;apply opposite_left.
  + apply associative.
  + apply ap. assumption.
  + apply symmetry;apply associative.
  + apply (ap (fun a => a ++ z)).
    apply opposite_left.
  + apply left_id.
- intros y z eq.
  path_via (z ++ id).
  path_via (z ++ (x - x)).
  path_via ((z ++ x) - x).
  path_via ((y ++ x) - x).
  path_via (y ++ (x - x)).
  path_via (y ++ id).
  + apply symmetry. apply right_id.
  + apply ap.
    apply symmetry;apply opposite_right.
  + apply symmetry;apply associative.
  + apply (ap (fun a => a - x)). assumption.
  + apply associative.
  + apply ap. apply opposite_right.
  + apply right_id.
Defined.

Instance group_strong `{Group A} : StrongMonoid A.
Proof.
split.
- apply _.
- exact group_cancels.
Defined.
