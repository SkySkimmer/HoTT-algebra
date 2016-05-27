Require Export HoTTMath.SemiGroup.

Class Id A := id : A.

Class LeftId A {i : Id A} {op : SgOp A} := left_id : forall x : A, id ++ x = x.
Class RightId A {i : Id A} {op : SgOp A} := right_id : forall x : A, x ++ id = x.

Class MonoidId A {i : Id A} {op : SgOp A} :=
  { monoid_id_left :> LeftId A
  ; monoid_id_right :> RightId A }.

Class Monoid A {i : Id A} {op : SgOp A} :=
  { monoid_semigroup :> SemiGroup A
  ; monoid_id :> MonoidId A }.


Class LeftCancels `{op : SgOp A} x := left_cancels : forall y z : A, x ++ y = x ++ z -> y = z.
Class RightCancels `{op : SgOp A} x := right_cancels : forall y z : A, y ++ x = z ++ x -> y = z.

Arguments left_cancels {_ _} _ {_ _ _} _.
Arguments right_cancels {_ _} _ {_ _ _} _.

Class Cancels `{op : SgOp A} x :=
  { cancels_left :> LeftCancels x
  ; cancels_right :> RightCancels x }.

Instance id_cancels `{Monoid A} : Cancels id.
Proof.
split.
- intros a b eq.
  path_via (id ++ a).
  + apply symmetry. apply left_id.
  + path_via (id ++ b). apply left_id.
- intros a b eq.
  path_via (a ++ id).
  + apply symmetry;apply right_id.
  + path_via (b ++ id). apply right_id.
Defined.

Lemma id_unique `(i : A) `(i' : A) `{M : @MonoidId A i op} {M' : @MonoidId A i' op} : i = i'.
Proof.
path_via (i ++ i').
- apply symmetry. apply M'.
- apply M.
Defined.

Class StrongMonoid A {i : Id A} {op : SgOp A} :=
  { strongmonoid_monoid :> Monoid A
  ; strongmonoid_cancels :> forall x, Cancels x }.
