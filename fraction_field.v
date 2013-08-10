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

Variable G : ring.

Hypothesis Hdec : decidable_paths G.
Context {Hset : IsHSet G} {Hint : IsStrictIntegral G}.
Hypothesis Hneq : ~ @OneV G = ZeroV.

(*
a fraction is a/b with a,b in G

fraction equivalence:
if b,d<>0 and ad=bc then a/b == c/d
forall a d, a/0 = 0/d and 0/a = d/0
*)

Definition pairT := G*G.

Definition fractionT := sigT (fun p : pairT => neq (snd p) ZeroV).

Instance fractionT_set : IsHSet fractionT.
Proof.
apply _.
Defined.

Definition fracV : fractionT -> pairT := fun x => x.1.
Coercion fracV : fractionT >-> pairT.

Definition fracEquiv : relation fractionT :=
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

assert (Hcan : @Rcancel (prering_mult G) (snd y)).
apply intdom_partial_cancels_right. intro;apply Hy;auto;apply inverse;assumption.
apply Hcan. clear Hcan;fold (@rmult G).
set (xa := fst x);set (xb := snd x);set (ya := fst y);set (yb:= snd y).
set (za := fst z);set (zb:=snd z).
path_via ((xa°yb)°zb). ssrapply (@ast_use (prering_mult G)); reflexivity.
path_via ((ya°xb)°zb). apply (ap (fun g => g ° _)). assumption.
path_via ((za ° yb)°xb). path_via ((ya°zb)°xb).
ssrapply (@ast_use (prering_mult G)); reflexivity.
apply (ap (fun g => g ° _)). assumption.
ssrapply (@ast_use (prering_mult G)); reflexivity.
Defined.

Definition fracQuot : Type := quotient fracEquiv.

Definition fracIn : fractionT -> fracQuot := class_of _.

Definition frac_rect := @quotient_rect _ fracEquiv.

Definition fracMult0 (x y : G*G) : G*G := (fst x ° fst y, snd x ° snd y).

Lemma fracMult_NZ : forall x y : fractionT, neq (snd (fracMult0 x.1 y.1)) ZeroV.
Proof.
intros [x Hx] [y Hy] H.
simpl in H. apply Hint in H. revert H.
apply minus1Trunc_rect_nondep;[|intros []].
intros [H|H];auto.
Defined.

Definition fracMultU : law fractionT
 := fun x y => (fracMult0 x.1 y.1; fracMult_NZ x y).

Definition fracMagU : magma := BuildMagma _ fracMultU.

Instance fracMultU_comm : Commutative fracMagU.
Proof.
red;unfold gop;simpl.
intros. apply fractionT_eq.
simpl. apply path_prod;apply (@commutative (prering_mult G) _).
Defined.

Instance fracMultU_assoc : Associative fracMagU.
Proof.
red;unfold gop;simpl.
intros x y z. apply fractionT_eq.
apply path_prod;apply (@associative (prering_mult G) _).
Defined.

Instance fracMultU_sg : IsSemigroup fracMagU.
Proof.
split;apply _.
Defined.

Definition fracLR_U : LR_sig := BuildLR_sig _ (BuildLR_Class _ 
  fracMultU fracEquiv).

Instance fracMultU_passes : IsCompat fracLR_U.
Proof.
apply invariant_compat.
red. apply _.
assert (H:IsLInvariant fracLR_U);[|split;try assumption].
red. red. unfold rrel;unfold gop;simpl.
unfold fracEquiv,fracMultU.
intros [z Hz] [x Hx] [y Hy]. simpl.

intros H.
set (xa := fst x);set (xb := snd x);set (ya := fst y);set (yb:= snd y).
set (za := fst z);set (zb:=snd z).
path_via ((za°zb) ° (xa ° yb)).
ssrapply (@ast_use (prering_mult G));reflexivity.
path_via ((za°zb) ° (ya ° xb)). apply ap;assumption.
ssrapply (@ast_use (prering_mult G));reflexivity.

red;red;intros. pattern (gop x z);apply transport with (gop z x). apply sg_comm.
pattern (gop y z);apply transport with (gop z y). apply sg_comm.
apply H;assumption.
Defined.

Definition fracMult : law fracQuot.
Proof.
red. apply (quotient_rec2 (fun x y => class_of _ (fracMultU x y))).
intros. apply related_classes_eq.
apply fracMultU_passes;assumption.
Defined.

Definition fracMultMag : magma := BuildMagma _ fracMult.

Instance fracMult_comm : Commutative fracMultMag.
Proof.
red. apply (quotient_ind (fun x => forall y, _)).
intros. apply trunc_forall.
intros x. apply quotient_ind. intros. red;simpl; apply quotient_is_set.
intros y.
unfold gop;simpl. apply ap. apply fracMultU_comm.
Defined.

Instance fracMult_assoc : Associative fracMultMag.
Proof.
red. apply (quotient_ind (fun x => forall y z, _)).
repeat (intro;apply trunc_forall).
intros x. apply (quotient_ind (fun y => forall z, _)).
repeat (intro;apply trunc_forall).
intros y. apply quotient_ind.
intros;red;simpl;apply quotient_is_set.
intros z.
unfold gop;simpl. apply ap. apply fracMultU_assoc.
Defined.

Instance fracMult_sg : IsSemigroup fracMultMag := BuildIsSemigroup _ _ _.

Definition fracOne : fracMultMag := fracIn ((OneV, OneV);Hneq).

Instance fracOne_left : Left_id fracOne.
Proof.
red. apply quotient_ind.
intros;red;simpl;apply quotient_is_set.
intros [xa xb].
unfold gop;simpl.
apply ap.
apply fractionT_eq. apply path_prod;simpl;apply One.
Defined.

Instance fracOne_right : Right_id fracOne.
Proof.
red. apply quotient_ind.
intros;red;simpl;apply quotient_is_set.
intros [xa xb].
unfold gop;simpl.
apply ap.
apply fractionT_eq. apply path_prod;simpl;apply One.
Defined.

Instance fracOne_id : IsId fracOne := BuildIsId _ _ _ _.

Canonical Structure fracOne_idT : Identity fracMultMag
 := BuildIdentity _ fracOne _.

Instance fracMult_ismonoid : IsMonoid fracMultMag := BuildIsMonoid _ _
 fracOne_idT.

Definition fracMult_monoid : monoid := BuildMonoid fracMultMag _.

Definition fracAdd0 : law (G*G) := fun x y => 
(fst x ° snd y + fst y ° snd x, snd x ° snd y).

Definition fracAdd_NZ : forall x y : fractionT, 
neq (snd (fracAdd0 x.1 y.1)) ZeroV := fracMult_NZ.

Definition fracAddU : law fractionT := fun x y => 
(fracAdd0 x.1 y.1 ; fracAdd_NZ x y).

Definition fracAddMagU : magma := BuildMagma _ fracAddU.

Instance fracAddU_comm : Commutative fracAddMagU.
Proof.
red. intros [x Hx] [y Hy].
unfold gop;simpl in *. apply fractionT_eq.
apply path_prod;simpl.
apply (@commutative (prering_plus G) _).
apply (@commutative (prering_mult G) _).
Defined.

Definition fracAddEquivU := BuildLR_sig _ (BuildLR_Class _
  fracAddU fracEquiv).

Instance fracAddU_passes : IsCompat fracAddEquivU.
Proof.
apply invariant_compat.
red;apply _.
assert (H:IsLInvariant fracAddEquivU);[|split;try assumption].
red;red. unfold rrel;unfold gop;simpl.
unfold fracEquiv;unfold fracAddU. simpl.
intros [[za zb] Hz] [[xa xb] Hx] [[ya yb] Hy] H;simpl in *.
ssrapply (@ast2_full_semiring G). simpl.
apply ap;apply ap.
simpl. fold (@rmult G). fold (@rmult G). fold (@rmult G).
path_via ((zb°zb)°(xa°yb)).
ssrapply (@ast_use (prering_mult G));reflexivity.
path_via ((zb°zb)°(ya°xb)). apply ap;assumption.
ssrapply (@ast_use (prering_mult G));reflexivity.

red;red;intros.
pattern (gop x z);apply transport with (gop z x). apply fracAddU_comm.
pattern (gop y z);apply transport with (gop z y). apply fracAddU_comm.
apply H;assumption.
Defined.

Definition fracAdd : law fracQuot.
Proof.
red. apply quotient_rec2 with (fun x y => class_of _ (fracAddU x y)).
intros. apply related_classes_eq. apply fracAddU_passes;assumption.
Defined.

Definition fracAddMag : magma := BuildMagma _ fracAdd.


Definition fracZero : fracAddMag := fracIn ((ZeroV, OneV);Hneq).

Instance fracZero_left : Left_id fracZero.
Proof.
red. apply quotient_ind.
intros;red;simpl;apply quotient_is_set.
intros [[xa xb] Hx]. unfold gop;simpl. apply ap.
apply fractionT_eq. simpl.
apply (@ap11 _ _ (pair _) (pair _));[apply ap|];simpl.
path_via (@ZeroV G + (xa ° (@OneV G))).
apply ap10. apply ap.
apply rmult_0_l.
path_via (xa ° OneV). apply Zero.
apply One. apply One.
Defined.

Instance fracZero_right : Right_id fracZero.
Proof.
red. apply quotient_ind.
intros;red;simpl;apply quotient_is_set.
intros [[xa xb] Hx]. unfold gop;simpl. apply ap.
apply fractionT_eq. simpl.
apply (@ap11 _ _ (pair _) (pair _));[apply ap|];simpl.
path_via ((xa ° (@OneV G)) + ZeroV).
apply ap.
apply rmult_0_l.
path_via (xa ° OneV). apply Zero.
apply One. apply One.
Defined.

Instance fracZero_id : IsId fracZero := BuildIsId _ _ _ _.

Canonical Structure fracZero_idT : Identity fracAddMag
 := BuildIdentity _ fracZero _.

Definition fracPrering : prering := makePrering _ fracAdd fracMult.

Instance fracAdd_assoc : Associative fracAddMag.
Proof.
red.
apply (quotient_ind (fun x => forall y z, _)).
intros;apply trunc_forall.
intros x. apply (quotient_ind (fun y => forall z, _)).
intros;apply trunc_forall.
intros y. apply quotient_ind.
intros;red;simpl;apply quotient_is_set.
intros z.

apply related_classes_eq.
destruct x as [[xa xb] Hx];destruct y as [[ya yb] Hy];destruct z as [[za zb] Hz].
simpl in Hx,Hy,Hz.
red; simpl.
ssrapply (@ast2_full_semiring G);reflexivity.
Defined.

Instance fracAdd_comm : Commutative fracAddMag.
Proof.
red. apply (quotient_ind (fun x => forall y, _)).
intros;apply trunc_forall.
intros x. apply quotient_ind.
intros;red;simpl;apply quotient_is_set.
intros y.

apply (ap (class_of _)). apply fracAddU_comm.
Defined.

Instance fracAdd_sg : IsSemigroup fracAddMag := BuildIsSemigroup _ _ _.

Instance fracAdd_ismonoid : IsMonoid fracAddMag := BuildIsMonoid _ _
 fracZero_idT.

Definition fracAdd_monoid : monoid := BuildMonoid fracAddMag _.

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

Definition fracOppU : fractionT -> fractionT := fun x => 
((@roppV G (fst x.1), snd x.1) ; x.2).

Definition fracOpp : fracAddMag -> fracAddMag.
Proof.
apply quotient_rec with (fun x => class_of _ (fracOppU x)).
intros [[xa xb] Hx] [[ya yb] Hy] H.
red in H;simpl in H,Hx,Hy.
apply related_classes_eq. red. simpl.
path_via (@roppV G (xa ° yb)). symmetry. apply ropp_rmult_left.
path_via (roppV (ya ° xb)). apply ap;assumption.
apply ropp_rmult_left.
Defined.

Instance fracOpp_correct : forall x : fracAddMag, IsInverse x (fracOpp x).
Proof.
apply quotient_ind. intros. apply isinverse_prop.
intros [[xa xb] Hx]. simpl in Hx.
apply linverse_inverse. red. unfold gop;simpl.
eapply transport;[|apply gid]. symmetry.
apply related_classes_eq.
red. simpl.
path_via (@ZeroV G).
path_via ((@ZeroV G) ° OneV).
apply (ap (fun g => g ° _)).
path_via ((xa + roppV xa) ° xb).
symmetry;apply semiring_distributes.
path_via (@ZeroV G ° xb). apply (ap (fun g => g ° _)).
apply (@id_unique (prering_plus G));apply _.
apply rmult_0_l. apply rmult_0_l.
apply inverse;apply rmult_0_l.
Defined.

Canonical Structure fracOppT : forall x : fracAddMag, Inverse x
 := fun x => BuildInverse _ _ (fracOpp x) _.

Instance fracAdd_isgroup : IsGroup fracAddMag := easyIsGroup _ fracOppT.

Instance frac_distrib : Distributes fracPrering.
Proof.
assert (H:Ldistributes fracPrering);[|split;try assumption].
red. apply (quotient_ind (fun a => forall b c, _)).
intros;apply trunc_forall.
intros x. apply (quotient_ind (fun b => forall c, _)).
intros;apply trunc_forall.
intros y. apply quotient_ind. apply _.
intros z.

destruct x as [[xa xb] Hx];
destruct y as [[ya yb] Hy];
destruct z as [[za zb] Hz].
simpl in Hx,Hy,Hz.
apply related_classes_eq. red;simpl.
ssrapply (@ast2_full_semiring G); reflexivity.

red;intros. path_via (a ° (b+c)). apply fracMult_comm.
eapply concat. apply H.
apply ap11;[apply ap|];apply fracMult_comm.
Defined.

Instance frac_isring : IsRing fracPrering := easyIsRing _.

Definition frac_ring : ring := BuildRing fracPrering _.

Lemma frac_dec : decidable_paths frac_ring.
Proof.
change (decidable_paths fracQuot). red.
assert (Hpr : forall x y : fracQuot, IsHProp ((x=y) + (~x=y))).
intros. apply hprop_allpath.
intros [x0|x0] [y0|y0]. apply ap. apply quotient_is_set.
destruct y0;apply x0.
destruct x0;apply y0.
apply ap. apply neq_is_prop.

apply (@quotient_ind _ _ (fun x => forall y, _)).
intros;apply trunc_forall.
intros x. apply quotient_ind.
intro;apply _.
intros y.

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
intros [[xa xb] Hx].
simpl in Hx.
destruct (Hdec xa ZeroV).
- exact fracZero.
- apply fracIn. exists (xb,xa). assumption.
Defined.

Definition fracInv : fracQuot -> fracQuot.
Proof.
apply quotient_rec with fracInvU.
intros [[xa xb] Hx] [[ya yb] Hy] Heq.
simpl in *. red in Heq. simpl in Heq.
destruct (Hdec xa ZeroV);destruct (Hdec ya ZeroV).
- reflexivity.
- apply Empty_rect.
  assert (ya ° xb = ZeroV). path_via (xa ° yb). apply inverse in p;destruct p.
  apply rmult_0_l.
  apply Hint in X. revert X.
  apply minus1Trunc_rect_nondep;[|intros[]].
  intros [H | H]; auto.
- apply Empty_rect.
  assert (xa ° yb = ZeroV). path_via (ya ° xb). apply inverse in p;destruct p.
  apply rmult_0_l.
  apply Hint in X. revert X.
  apply minus1Trunc_rect_nondep;[|intros[]].
  intros [H | H]; auto.
- apply related_classes_eq.
  red. simpl. path_via (ya°xb). apply (@commutative (prering_mult G) _).
  path_via (xa ° yb).
  apply (@commutative (prering_mult G) _).
Defined.

Lemma frac_neq : neq fracOne fracZero.
Proof.
unfold rrel;simpl.
intros H.
apply classes_eq_related in H.
red in H;simpl in H. apply Hneq.
eapply concat;[|eapply concat;[apply H|]].
apply inverse. apply One.
apply rmult_0_l.
Defined.

Lemma fracInv_inv : forall x : frac_ring, neq x (@ZeroV frac_ring)
 -> @IsInverse (prering_mult frac_ring) x (fracInv x).
Proof.
apply (quotient_ind (fun x => _ -> _)).
intros. apply trunc_forall.

intros [[xa xb] Hx] H.
simpl in *.
destruct (Hdec xa ZeroV).
- destruct H.
  apply related_classes_eq. red. simpl.
  path_via (@ZeroV G).
  apply inverse in p;destruct p. apply rmult_0_l.
  apply inverse;apply rmult_0_l.
- apply linverse_inverse.
  red. eapply transport;[|apply One].
  symmetry. apply related_classes_eq.
  red;simpl.
  path_via (xa°xb). apply One.
  path_via (xb ° xa). apply (@commutative (prering_mult _) _).
  apply inverse;apply One.
Defined.

Instance frac_isdecfield : IsDecField fracPrering.
Proof.
apply BuildIsDecField with frac_isring fracInv.
apply frac_neq.
simpl. destruct (Hdec ZeroV ZeroV) as [_|[]]; reflexivity.
apply fracInv_inv.
Defined.

(*
need to defined DecField
Definition fracDecField : DecField.
*)








