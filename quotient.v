Require Import HoTT FunextAxiom UnivalenceAxiom.

Open Local Scope path_scope.

Module Export Quotient.

Local Inductive quotient : (forall A : Type, relation A -> Type) := 
  | class_of : forall A (R : relation A), A -> quotient A R.

Arguments quotient {A} R.
Arguments class_of {A} R _.

Axiom related_classes_eq : forall {A R} {x y : A}, R x y ->
 class_of R x = class_of R y.

Axiom quotient_is_set : forall {A} {R : relation A}, IsHSet (quotient R).
Existing Instance quotient_is_set.

Definition quotient_rect : forall {A} {R : relation A} (P : quotient R -> Type),
  forall dclass : forall x, P (class_of R x),
  forall dequiv : (forall x y (H : R x y), 
           transport _ (related_classes_eq H) (dclass x) = dclass y),
  forall q, P q.
Proof.
intros ? ? ? ?. intro. destruct q. apply dclass.
Defined.

Definition quotient_rect_compute : forall {A} {R : relation A} {P}
 dclass dequiv x, 
  quotient_rect P dclass dequiv (class_of R x) = dclass x.
Proof.
intros. reflexivity.
Defined.

Axiom quotient_rect_compute_path : forall {A} {R : relation A} {P}
dclass dequiv x y (H : R x y), 
apD (quotient_rect P dclass dequiv) (related_classes_eq H)
 = dequiv x y H.

End Quotient.


Section Equiv.

Context {A : Type} {R : relation A}
 {Htrans : Transitive R} {Hsymm : Symmetric R}
{Hprop : forall x y, IsHProp (R x y)}.

Definition quotient_ind : forall P : quotient R -> Type, 
forall (Hprop' : forall x, IsHProp (P (class_of _ x))), 
(forall x, P (class_of _ x)) -> forall x, P x.
Proof.
intros ? ? dclass. apply quotient_rect with dclass.
intros. apply Hprop'.
Defined.

Lemma quotient_path2 : forall {x y : quotient R} (p q : x=y), p=q.
Proof.
apply @set_path2. apply _.
Defined.

Definition in_class : quotient R -> A -> Type.
Proof.
apply (@quotient_rect A R (fun _ => A -> Type) R).
intros.
eapply concat. apply transport_const.
apply funext_axiom. intro z.
apply univalence_axiom. apply equiv_iff_hprop.
intros. eauto.
intros. eauto.
Defined.

Context {Hrefl : Reflexive R}.

Lemma in_class_pr : forall x, in_class (class_of _ x) = R x.
Proof.
intros. reflexivity.
Defined.

Instance in_class_is_prop : forall q x, IsHProp (in_class q x).
Proof.
assert (H : forall x q, IsHProp (in_class q x)).
intro;apply quotient_ind.
intros;apply _.
intros. apply Hprop.
exact (fun q x => H x q).
Defined.

Lemma quotient_rect_prop : forall (P : quotient R -> Type) 
  {_: forall q, IsHProp (P q)},
  forall dclass : forall x, P (class_of R x),
  forall q, P q.
Proof.
intros ? ? ?.
apply (quotient_rect _ dclass).
intros. apply allpath_hprop.
Defined.

Lemma class_of_repr : forall q x, in_class q x -> q = class_of _ x.
Proof.
apply (@quotient_rect A R
 (fun q => forall x, in_class q x -> q = class_of R x)
  (fun x y H => related_classes_eq H)).
intros.
 simpl.
apply funext_axiom. intro z.
apply funext_axiom;intro H'.
apply quotient_path2.
Defined.

Lemma classes_eq_related : forall x y, 
class_of R x = class_of R y -> R x y.
Proof.
intros x y H.
change (in_class (class_of R x) y).
pattern (class_of R x). eapply transport.
symmetry. apply H.
simpl. apply Hrefl.
Defined.

Definition quotient_rec : forall {B : Type}, 
  forall dclass : (forall x : A, B), 
  forall dequiv : (forall x y (H : R x y), dclass x = dclass y), 
  quotient R -> B.
Proof.
intros ? ? ?.
apply (quotient_rect (fun _ : quotient R => B)) with dclass.
intros.
destruct (related_classes_eq H). simpl. apply dequiv. apply H.
Defined.

Definition quotient_rec2 : forall {B : Type} {Hset : IsHSet B}, 
  forall dclass : (A -> A -> B), 
  forall dequiv : (forall x x' (Hx : R x x') y y' (Hy : R y y'),
                  dclass x y = dclass x' y'), 
  quotient R -> quotient R -> B.
Proof.
intros ? ? ? ?.
assert (dequiv0 : forall x x0 y : A, R x0 y -> dclass x x0 = dclass x y).
intros ? ? ? Hx. apply dequiv. apply Hrefl. apply Hx.
refine (quotient_rec 
  (fun x => quotient_rec (dclass x) (dequiv0 x)) _).
intros x x' Hx.
apply funext_axiom.

red.
assert (dequiv1 : forall y : A,
  quotient_rec (dclass x) (dequiv0 x) (class_of R y) =
  quotient_rec (dclass x') (dequiv0 x') (class_of R y)).
intro. simpl. apply dequiv. apply Hx. apply Hrefl. 
 refine (quotient_rect (fun q => 
quotient_rec (dclass x) (dequiv0 x) q =
quotient_rec (dclass x') (dequiv0 x') q)
  dequiv1 _).
intros.
apply Hset.
Defined.


End Equiv.

Section Compatible.

Context {A} (Ra : relation A).
Context {B} (Rb : relation B).
Context {C} (Rc : relation C).

Definition compatible (f : A -> B -> C) :=
  forall x x', Ra x x' -> forall y y', Rb y y' -> Rc (f x y) (f x' y').

Definition lcompat (f : A -> B -> C) := 
  forall x x', Ra x x' -> forall y, Rc (f x y) (f x' y).
Definition rcompat (f : A -> B -> C) := 
  forall x y y', Rb y y' -> Rc (f x y) (f x y').

Lemma transitive_lr_compat {Htrans : Transitive Rc} :
forall f, lcompat f -> rcompat f -> compatible f.
Proof.
intros ? H H';red;intros.
apply Htrans with (f x y').
apply H'; assumption.
apply H; assumption.
Defined.

End Compatible.

Arguments quotient_rec2 {_ _ _ _ _} _ _ _ _.

