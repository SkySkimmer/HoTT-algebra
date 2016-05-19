Require Import HoTT hit.unique_choice FunextAxiom.
Require Export structures basics.
Require Import quotient.
Require Import syntax.

Open Scope path_scope.

Import BinOpTree.
Import Distributive.
Import Ring_pr.
Import OrderedMagma_pr.
Import Field_pr.

Module Fraction.
Import minus1Trunc.

Section VarSec.

Context {G : Type}.
Variable L : Prering G.
Context {Hg : IsRing L}.

Hypothesis Hdec : DecidablePaths G.
Let Hset : IsHSet G := hset_decidable Hdec.
Existing Instance Hset.
Context {Hint : IsStrictIntegral L}.
Hypothesis Hneq : ZeroV != OneV.

(*
a fraction is a/b with a,b in G

fraction equivalence:
if b,d#0 and ad=bc then a/b == c/d
forall a d, a/0 = 0/d and 0/a = d/0
*)

Let pairT := G*G.

Definition fractionT := sigT (fun p : pairT => neq ZeroV (snd p)).

Instance fractionT_set : IsHSet fractionT.
Proof.
apply @trunc_sigma. apply trunc_prod.
apply _.
Defined.

Definition fracV : fractionT -> pairT := fun x => x.1.
Coercion fracV : fractionT >-> pairT.

Definition fracEquiv : Rel fractionT :=
 fun x y => (fst x.1) ° (snd y.1) = (fst y.1) ° (snd x.1).

Lemma fractionT_eq : forall x y : fractionT, x.1 = y.1 -> x=y.
Proof.
intros ? ? p. apply path_sigma with p.
apply neq_is_prop.
Defined.

Instance fracEquiv_is_prop : forall x y, IsHProp (fracEquiv x y).
Proof.
intros. apply _.
Defined.

Lemma fracEquiv_dec : forall x y, fracEquiv x y + ~ fracEquiv x y.
Proof.
intros.
unfold fracEquiv. apply Hdec.
Defined.

Instance fracEquiv_refl : Reflexive fracEquiv.
Proof.
intro;reflexivity.
Defined.

Instance fracEquiv_symm : Symmetric fracEquiv.
Proof.
intros x y;apply inverse.
Defined.

Instance fracEquiv_trans : Transitive fracEquiv.
Proof.
intros [x Hx] [y Hy] [z Hz] H H0.

assert (Hcan : Rcancel (°) (snd y)).
apply intdom_partial_cancels_right. intro;apply Hy;auto;apply inverse;assumption.
apply Hcan. clear Hcan. simpl.
set (xa := fst x);set (xb := snd x);set (ya := fst y);set (yb:= snd y).
set (za := fst z);set (zb:=snd z).
path_via ((xa°yb)°zb). ssrapply (@ast_use _ (°) _); reflexivity.
path_via ((ya°xb)°zb). apply (ap (fun g => g ° _)). assumption.
path_via ((za ° yb)°xb). path_via ((ya°zb)°xb).
ssrapply (@ast_use _ (°) _); reflexivity.
apply (ap (fun g => g ° _)). assumption.
ssrapply (@ast_use _ (°) _); reflexivity.
Defined.

Definition fracQuot : Type := quotient fracEquiv.

Instance frac_set : IsHSet fracQuot := quotient_is_set.

Definition fracIn : fractionT -> fracQuot := class_of _.

Definition frac_rect := @quotient_rect _ fracEquiv.

Definition fracMult0 (x y : G*G) : G*G := (fst x ° fst y, snd x ° snd y).

Lemma fracMult_NZ : forall x y : fractionT, neq ZeroV (snd (fracMult0 x.1 y.1)).
Proof.
intros [x Hx] [y Hy] H.
simpl in H. apply Hint in H. revert H.
apply minus1Trunc_rect_nondep;[|intros []].
intros [H|H];auto.
Defined.

Instance fracMultU : Mult fractionT
 := fun x y => (fracMult0 x.1 y.1; fracMult_NZ x y).

Instance fracMultU_comm : Commutative fracMultU.
Proof.
red;unfold gop;simpl.
intros. apply fractionT_eq.
simpl. apply path_prod;apply (commutative (°) _).
Defined.

Instance fracMultU_assoc : Associative fracMultU.
Proof.
red;unfold gop;simpl.
intros x y z. apply fractionT_eq.
apply path_prod;apply (associative (°) _).
Defined.

Instance fracMultU_sg : IsSemigroup fracMultU.
Proof.
split;apply _.
Defined.

Definition fracLR_U : OpRel _ := BuildLR_Class _ fracMultU fracEquiv.

Instance fracMultU_passes : IsCompat fracLR_U.
Proof.
apply invariant_compat.
apply _.
assert (H:IsLInvariant fracLR_U);[|split;try assumption].
red. red. unfold rrel;unfold gop;simpl.
unfold fracEquiv,fracMultU.
intros [z Hz] [x Hx] [y Hy]. simpl.

intros H.
set (xa := fst x);set (xb := snd x);set (ya := fst y);set (yb:= snd y).
set (za := fst z);set (zb:=snd z).
path_via ((za°zb) ° (xa ° yb)).
ssrapply (@ast2_full_semiring G L Hg);reflexivity.
path_via ((za°zb) ° (ya ° xb)). apply ap;assumption.
ssrapply (@ast2_full_semiring _ _ Hg);reflexivity.

red;red;intros. change gop with mult.
pattern (x ° z);apply transport with (z ° x). apply (commutative _).
pattern (y ° z);apply transport with (z ° y). apply (commutative _).
apply H;assumption.
Defined.

Instance fracMult : Mult fracQuot.
Proof.
hnf. apply (quotient_rec2 (fun x y => class_of _ (fracMultU x y))).
intros. apply related_classes_eq.
apply fracMultU_passes;assumption.
Defined.

Instance fracMult_comm : Commutative fracMult.
Proof.
red. apply (quotient_ind (fun x => forall y, _)). apply _.
intros x. apply quotient_ind. apply _.
intros y.
unfold gop;simpl. apply ap. apply fracMultU_comm.
Defined.

Instance fracMult_assoc : Associative fracMult.
Proof.
red. apply (quotient_ind (fun x => forall y z, _) _).
intros x. apply (quotient_ind (fun y => forall z, _) _).
intros y. apply quotient_ind. apply _.
intros z.
unfold gop;simpl. apply ap. apply fracMultU_assoc.
Defined.

Instance fracMult_sg : IsSemigroup fracMult := BuildIsSemigroup _ _ _.

Definition fracOne : fracQuot := fracIn ((OneV, OneV);Hneq).

Instance fracOne_left : Left_id (°) fracOne.
Proof.
red. apply quotient_ind.
apply _.
intros [[xa xb] Hx].
unfold gop.
apply (ap fracIn).
apply fractionT_eq. apply path_prod;simpl;apply One.
Defined.

Instance fracOne_id : IsId (°) fracOne.
Proof.
apply left_id_id. apply _.
Defined.

Canonical Structure fracOne_idT : Identity (°)
 := BuildIdentity _ fracOne _.

Instance fracMult_ismonoid : IsMonoid (°) := BuildIsMonoid _ _
 fracOne_idT.

Definition fracAdd0 : Plus (G*G) := fun x y => 
(fst x ° snd y + fst y ° snd x, snd x ° snd y).

Definition fracAdd_NZ : forall x y : fractionT, 
neq ZeroV (snd (fracAdd0 x.1 y.1)) := fracMult_NZ.

Instance fracAddU : Plus fractionT := fun x y => 
(fracAdd0 x.1 y.1 ; fracAdd_NZ x y).

Instance fracAddU_comm : Commutative fracAddU.
Proof.
red. intros [x Hx] [y Hy].
unfold gop;simpl in *. apply fractionT_eq.
apply path_prod;simpl.
apply (commutative). apply Hg.
apply (commutative). apply Hg.
Defined.

Definition fracAddEquivU := BuildLR_Class _ fracAddU fracEquiv.

Instance fracAddU_passes : IsCompat fracAddEquivU.
Proof.
apply invariant_compat.
apply _.
assert (H:IsLInvariant fracAddEquivU);[|split;try assumption].
red;red. unfold rrel;unfold gop;simpl.
unfold fracEquiv;unfold fracAddU. simpl.
intros [[za zb] Hz] [[xa xb] Hx] [[ya yb] Hy] H;simpl in *.
ssrapply (@ast2_full_semiring G L _). simpl. unfold gop.
apply ap.
path_via ((zb°zb)°(xa°yb)).
ssrapply (@ast_use G (°) _);reflexivity.
path_via ((zb°zb)°(ya°xb)). apply ap;assumption.
ssrapply (@ast_use G (°) _);reflexivity.

red;red;intros. change gop with plus.
pattern (x + z);apply transport with (z + x). apply fracAddU_comm.
pattern (y + z);apply transport with (z + y). apply fracAddU_comm.
apply H;assumption.
Defined.

Instance fracAdd : Plus fracQuot.
Proof.
hnf. apply quotient_rec2 with (fun x y => class_of _ (fracAddU x y)).
intros. apply related_classes_eq. apply fracAddU_passes;assumption.
Defined.

Definition fracZero : fracQuot := fracIn ((ZeroV, OneV);Hneq).

Instance fracZero_left : Left_id (+) fracZero.
Proof.
red. apply quotient_ind. apply _.
intros [[xa xb] Hx]. unfold gop;simpl. apply (ap fracIn).
apply fractionT_eq. simpl.
apply path_prod';simpl.
path_via (ZeroV + (xa ° OneV)).
apply ap10. apply ap.
apply rmult_0_l.
path_via (xa ° OneV). apply Zero.
apply One. apply One.
Defined.

Instance fracZero_right : Right_id (+) fracZero.
Proof.
red. apply quotient_ind. apply _.
intros [[xa xb] Hx]. unfold gop;simpl. apply (ap fracIn).
apply fractionT_eq. simpl.
apply path_prod';simpl.
path_via ((xa ° OneV) + ZeroV).
apply ap.
apply rmult_0_l.
path_via (xa ° OneV). apply Zero.
apply One. apply One.
Defined.

Instance fracZero_id : IsId (+) fracZero := BuildIsId _ _ _ _.

Canonical Structure fracZero_idT : Identity (+)
 := BuildIdentity _ fracZero _.

Instance fracPrering : Prering fracQuot := BuildLL_Class _ fracAdd fracMult.

Instance fracAdd_assoc : Associative (+).
Proof.
red.
apply (quotient_ind (fun x => forall y z, _) _).
intros x. apply (quotient_ind (fun y => forall z, _) _).
intros y. apply quotient_ind. apply _.
intros z.

apply related_classes_eq.
destruct x as [[xa xb] Hx];destruct y as [[ya yb] Hy];destruct z as [[za zb] Hz].
simpl in Hx,Hy,Hz.
red; simpl.
ssrapply (@ast2_full_semiring G L _);reflexivity.
Defined.

Instance fracAdd_comm : Commutative (+).
Proof.
red. apply (quotient_ind (fun x => forall y, _) _).
intros x. apply quotient_ind. apply _.
intros y.

apply (ap (class_of _)). apply fracAddU_comm.
Defined.

Instance fracAdd_sg : IsSemigroup (+) := BuildIsSemigroup _ _ _.

Instance fracAdd_ismonoid : IsMonoid (+) := BuildIsMonoid _ _
 fracZero_idT.

(* what for? 
Lemma frac_neq0 : ~ @gidV (fracMult_monoid) = @gidV (fracAdd_monoid).
Proof.
intro H.
unfold gidV in H;simpl in H.
apply classes_eq_related in H.
red in H. simpl in H.
apply Hneq. path_via (@OneV G ° OneV).
apply inverse. apply One.
path_via (@ZeroV G ° OneV).
apply rmult_0_l.
Defined.
*)

Definition fracOppU : fractionT -> fractionT := fun x => 
((roppV (fst x.1), snd x.1) ; x.2).

Definition fracOpp : fracQuot -> fracQuot.
Proof.
apply quotient_rec with (fun x => class_of _ (fracOppU x)).
intros x y H.
red in H.
apply related_classes_eq. red. simpl.
path_via (roppV ((fst x.1) ° (snd y.1))). symmetry. apply ropp_rmult_left.
path_via (roppV (fst y.1 ° snd x.1)). apply ap;assumption.
apply ropp_rmult_left.
Defined.

Instance fracOpp_correct : forall x, IsInverse (+) x (fracOpp x).
Proof.
apply quotient_ind. apply _.
intros [[xa xb] Hx]. simpl in Hx.
apply linverse_inverse. red. unfold gop;simpl.
apply transport with fracZero. symmetry.
apply related_classes_eq.
red. simpl.
path_via ZeroV.
path_via (ZeroV ° OneV).
apply (@ap _ _ (fun g => g ° OneV)).
path_via ((xa + roppV xa) ° xb).
symmetry;apply semiring_distributes;apply _.
path_via (ZeroV ° xb). apply (ap (fun g => g ° _)).
eapply (id_unique (+)). apply ropp. apply Zero.
apply rmult_0_l. apply rmult_0_l.
apply inverse;apply rmult_0_l.
apply _.
Defined.

Canonical Structure fracOppT : forall x : fracQuot, Inverse (+) x
 := fun x => BuildInverse _ _ (fracOpp x) _.

Instance fracAdd_isgroup : IsGroup (+) := easyIsGroup _ fracOppT.

Instance frac_distrib : Distributes fracPrering.
Proof.
assert (H:Ldistributes fracPrering);[|split;try assumption].
red. apply (quotient_ind (fun a => forall b c, _) _).
intros x. apply (quotient_ind (fun b => forall c, _) _).
intros y. apply quotient_ind. apply _.
intros z.

destruct x as [[xa xb] Hx];
destruct y as [[ya yb] Hy];
destruct z as [[za zb] Hz].
simpl in Hx,Hy,Hz.
apply related_classes_eq. red;simpl.
ssrapply (@ast2_full_semiring G L _); reflexivity.

red;intros. path_via (a ° (b+c)). apply fracMult_comm.
eapply concat. apply H.
apply ap11;[apply ap|];apply fracMult_comm.
Defined.

Instance frac_isring : IsRing fracPrering := easyIsRing _ _ _ _.

Lemma frac_dec : DecidablePaths fracQuot.
Proof.
red.
assert (Hprop : forall x y : fracQuot, IsHProp ((x=y) \/ (x != y))).
intros;apply hprop_allpath. intros [x0|x0] [y0|y0].
apply ap. apply quotient_is_set.
destruct y0;auto. destruct x0;auto.
apply ap;apply neq_is_prop.

apply (quotient_ind (fun x => forall y, _) _).
intros x. apply quotient_ind. apply _.
intros y. clear Hprop.

destruct x as [[xa xb] Hx];destruct y as [[ya yb] Hy].
simpl in Hx,Hy.
destruct (Hdec (xa°yb) (ya°xb)) as [?|n].
left. apply related_classes_eq. red;simpl. assumption.
right. intro H.
apply classes_eq_related in H.
apply n;apply H.
Defined.

Definition fracInvU : fractionT -> fracQuot.
Proof.
intros x.
destruct (Hdec ZeroV (fst x.1)).
- exact fracZero.
- apply fracIn. exists (snd x.1,fst x.1). assumption.
Defined.

Definition fracInv : fracQuot -> fracQuot.
Proof.
apply quotient_rec with fracInvU.
intros [[xa xb] Hx] [[ya yb] Hy] Heq.
simpl in *. red in Heq. simpl in Heq. unfold fracInvU. simpl.
destruct (Hdec ZeroV xa);destruct (Hdec ZeroV ya).
- reflexivity.
- apply Empty_rect.
  assert (ZeroV = ya ° xb). path_via (xa ° yb). destruct p.
  apply inverse;apply rmult_0_l.
  apply Hint in X. revert X.
  apply minus1Trunc_rect_nondep;[|intros[]].
  intros [H | H]; auto.
- apply Empty_rect.
  assert (ZeroV = xa ° yb). path_via (ya ° xb). destruct p.
  apply inverse;apply rmult_0_l.
  apply Hint in X. revert X.
  apply minus1Trunc_rect_nondep;[|intros[]].
  intros [H | H]; auto.
- apply related_classes_eq.
  red. simpl. path_via (ya°xb). apply (commutative (°) _).
  path_via (xa ° yb).
  apply (commutative (°) _).
Defined.

Lemma frac_neq : neq fracZero fracOne.
Proof.
intros H.
apply classes_eq_related in H.
red in H;simpl in H. apply Hneq.
eapply concat;[|eapply concat;[apply H|]].
apply inverse. apply One.
apply One.
Defined.

Lemma fracInv_inv : forall x : fracQuot, neq ZeroV x
 -> IsInverse (°) x (fracInv x).
Proof.
apply (quotient_ind (fun x => _ -> _) _).

intros [[xa xb] Hx] H.
simpl in *. unfold fracInvU. simpl.
destruct (Hdec ZeroV xa).
- destruct H.
  apply related_classes_eq. red. simpl.
  eapply concat. apply rmult_0_l.
  destruct p;apply inverse;apply rmult_0_l.
- apply linverse_inverse.
  red. apply transport with OneV.
  symmetry. apply related_classes_eq.
  red;simpl.
  path_via (xa°xb). apply One.
  path_via (xb ° xa). apply (commutative (°) _).
  apply inverse;apply One.
  apply _.
Defined.

Global Instance frac_isdecfield : IsDecField fracPrering.
Proof.
apply BuildIsDecField with frac_isring fracInv.
apply frac_neq.
simpl. unfold fracInvU. simpl.
destruct (Hdec ZeroV ZeroV) as [_|[]]; reflexivity.
apply fracInv_inv.
Defined.

End VarSec.


End Fraction.






