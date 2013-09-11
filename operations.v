Require Import HoTT.
Require Export structures basics.

Open Scope path_scope.

Import Magma2_pr.

Section Product.

Definition law_prod : forall {G G'}, law G -> law G' -> law (G*G') 
  := fun G G' f g x y => match x,y with 
    | (a,b) , (a',b') => (f a a', g b b')
    end.

Canonical Structure mag_prod : forall (G G' : magma), magma
 := fun G G' => BuildMagma (G*G') (BuildClass (law_prod gop gop)).

Infix "*" := mag_prod.

Instance prod_comm : forall {G}, Commutative G ->
forall {H}, Commutative H -> Commutative (G * H).
Proof.
red;intros.
destruct x,y. unfold gop;simpl.
apply ap11;[apply ap|];auto.
Defined.

Instance prod_assoc : forall {G}, Associative G ->
forall {H}, Associative H -> Associative (G * H).
Proof.
red;intros.
destruct x,y,z. unfold gop;simpl.
apply ap11;[apply ap|];auto.
Defined.

Instance prod_is_sg : forall G {Hsg : IsSemigroup G}
 H {Hsg' : IsSemigroup H}, IsSemigroup (G * H).
Proof.
intros.
apply BuildIsSemigroup.
apply prod_assoc. apply Hsg. apply Hsg'.
apply prod_comm. apply Hsg. apply Hsg'.
Defined.

Canonical Structure prod_sg : forall {G H : semigroup}, semigroup
  := fun G H => BuildSemigroup (G*H) (prod_is_sg _ _).

Instance prod_is_monoid : forall {G} {Hsg : IsMonoid G}
 {H} {Hsg' : IsMonoid H}, IsMonoid (G * H).
Proof.
intros. apply BuildIsMonoid. apply _. apply BuildIdentity with (gidV, gidV).
apply left_id_id. red. intros [x x'].
unfold gop;simpl.
apply ap11;[apply ap|];apply gid_id.
Defined.

Canonical Structure prod_monoid : forall {G H : monoid}, monoid
  := fun G H => BuildMonoid (G*H) prod_is_monoid.

Lemma prod_Lcancel_pair : forall {G H : magma} (a : G) (b : H), 
Lcancel a -> Lcancel b -> Lcancel (a, b).
Proof.
red;intros.
destruct b0;destruct c.
simpl in X1. apply equiv_path_prod in X1;simpl in X1.
apply path_prod;simpl;[apply X | apply X0];apply X1.
Defined.

Lemma prod_Rcancel_pair : forall {G H : magma} (a : G) (b : H), 
Rcancel a -> Rcancel b -> Rcancel (a, b).
Proof.
red;intros.
destruct b0;destruct c.
simpl in X1. apply equiv_path_prod in X1;simpl in X1.
apply path_prod;simpl;[apply X | apply X0];apply X1.
Defined.

Lemma prod_Cancel_pair : forall {G H : magma} (a : G) (b : H), 
Cancel a -> Cancel b -> Cancel (a, b).
Proof.
intros;split;
[apply prod_Lcancel_pair | apply prod_Rcancel_pair];
first [apply X | apply X0].
Defined.

Instance prod_is_cmonoid : forall {G} {Hsg : IsCMonoid G}
 {H} {Hsg' : IsCMonoid H}, IsCMonoid (G * H).
Proof.
intros. apply BuildIsCMonoid. apply _.
intros; destruct a;apply prod_Cancel_pair;apply cmonoid_cancel.
Defined.

Canonical Structure prod_cmonoid : forall {G H : Cmonoid}, Cmonoid 
 := fun G H => BuildCMonoid (G*H) _.

Definition prod_apart {A B : Type} (f : A -> B) {C D : Type} (g : C -> D) 
 : (A*C) -> (B*D) := fun p => let (a,c) := p in (f a, g c).

Instance prod_linverse : forall {G H : monoid}, 
forall x y : G, Linverse x y -> 
forall x' y' : H, Linverse x' y' -> 
Linverse (x,x') (y,y').
Proof.
intros;red. unfold gop;simpl.
apply ap11;[apply ap;apply X|apply X0].
Defined.

Instance prod_rinverse : forall {G H : monoid}, 
forall x y : G, Rinverse x y -> 
forall x' y' : H, Rinverse x' y' -> 
Rinverse (x,x') (y,y').
Proof.
intros. apply prod_linverse;assumption.
Defined.

Instance prod_inverse : forall {G H : monoid}, 
forall x y : G, IsInverse x y -> 
forall x' y' : H, IsInverse x' y' -> 
IsInverse (x,x') (y,y').
Proof.
intros;split;[apply prod_linverse | apply prod_rinverse];
first [apply X | apply X0].
Defined.

Instance prod_is_group : forall {G} {Hsg : IsGroup G}
 {H} {Hsg' : IsGroup H}, IsGroup (G * H).
Proof.
intros. apply easyIsGroup with prod_is_monoid (prod_apart gopp gopp).
intros [a b]. simpl. apply prod_inverse;apply gopp_correct.
Defined.

Canonical Structure prod_group : forall {G H : group}, group
 := fun G H => BuildGroup (G*H) _.


Canonical Structure mag2_prod : forall (G G' : magma2), magma2
 := fun G G' => BuildMagma2 (G*G') 
(BuildClass (law_prod radd radd)) (BuildClass (law_prod rmult rmult)).

Infix "*" := mag2_prod.

Instance prod_left_distrib : forall {G} (Hg : Ldistributes G)
 {H} (Hh : Ldistributes H), Ldistributes (G*H).
Proof.
intros;red. intros [a1 a2] [b1 b2] [c1 c2].
unfold rmult;unfold radd;unfold gop;simpl;
apply ap11;[apply ap;apply Hg|apply Hh].
Defined.

Instance prod_right_distrib : forall {G} (Hg : Rdistributes G)
 {H} (Hh : Rdistributes H), Rdistributes (G*H).
Proof.
intros;red. intros [a1 a2] [b1 b2] [c1 c2].
unfold radd;unfold rmult;unfold gop;simpl;
apply ap11;[apply ap;apply Hg|apply Hh].
Defined.

Instance prod_distrib : forall {G} (Hg : Distributes G)
 {H} (Hh : Distributes H), Distributes (G*H).
Proof.
intros;split;[apply prod_left_distrib | apply prod_right_distrib];
first [apply Hg | apply Hh].
Defined.

Instance prod_is_semiring : forall {G} {Hg : IsSemiring G}
{H} {Hh : IsSemiring H}, IsSemiring (G*H).
Proof.
intros. apply BuildIsSemiring.
apply (@prod_is_cmonoid (mag2_add G) _ (mag2_add H) _).
apply (@prod_is_monoid (mag2_mult G) _ (mag2_mult H) _).
apply prod_distrib;apply semiring_distributes.
Defined.

Canonical Structure prod_semiring : forall {G H : semiring}, semiring
 := fun G H => BuildSemiring (G*H) prod_is_semiring.

Instance prod_is_ring : forall {G} {Hg : IsRing G}
{H} {Hh : IsRing H}, IsRing (G*H).
Proof.
intros.
apply easyIsRing. apply prod_is_group.
change (IsMonoid (mag_prod (mag2_mult G) (mag2_mult H))).
apply prod_is_monoid.
apply prod_distrib;apply _.
Defined.

Canonical Structure prod_ring : forall {G H : ring}, ring
 := fun G H => BuildRing (G*H) _.

End Product.



