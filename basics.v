Require Import HoTT FunextAxiom UnivalenceAxiom.
Require Import unique_choice.
Require Export structures.

Definition neq {T} : relation T := fun x y => ~ x=y.

Instance iff_trans : Transitive iff.
Proof.
red. intros A B C [H H'] [H0 H0'].
split;
apply (@compose _ B);assumption.
Defined.

Instance iff_symm : Symmetric iff.
Proof.
red. intros A B [H H'];split;assumption.
Defined.

Instance iff_refl : Reflexive iff.
Proof.
intros A. split;exact idmap.
Defined.

Module Magma_pr.
Export Magma.

Instance law_set : forall A, IsHSet A -> IsHSet (law A).
Proof.
intros.
apply @trunc_arrow. exact _.
apply trunc_arrow.
Defined.

Definition magma_sig : sigT law <~> magma.
Proof.
issig BuildMagma gcarr glaw.
Defined.

Instance assoc_prop : forall {G : magma} {Hset : IsHSet G},
 IsHProp (Associative G).
Proof.
intros.
apply trunc_forall.
Defined.

Instance comm_prop : forall {G : magma} {Hset : IsHSet G},
 IsHProp (Commutative G).
Proof.
intros.
apply trunc_forall.
Defined.

Instance issg_prop : forall {G : magma} {Hset : IsHSet G},
 IsHProp (IsSemigroup G).
Proof.
intros G Hset.
apply (@trunc_equiv' (sigT (fun _ : Associative G => Commutative G))).
issig (BuildIsSemigroup G) (@sg_assoc G) (@sg_comm G).
apply @trunc_sigma. apply _. intro. apply _.
Defined.

Lemma id_unique : forall G : magma, forall e : G, 
IsId e -> forall e': G, IsId e' -> e = e'.
Proof.
intros.
apply (@concat _ _ (gop e e')).
 apply inverse;apply id_right.
 apply id_left.
Defined.

Instance id_prop : forall {G : magma} {Hset : IsHSet G} e, IsHProp (@IsId G e).
Proof.
intros.
apply (@trunc_equiv' (sigT (fun _ : Left_id e => Right_id e))).
issig (BuildIsId G e) (@id_left G e) (@id_right G e).

apply @trunc_sigma.
apply trunc_forall.
intros;apply trunc_forall.
Defined.

Lemma left_id_id : forall {G : magma} {Hg : Commutative G} (e : G),
 Left_id e -> IsId e.
Proof.
intros ? ? ? X. split;auto.
intro.
eapply concat. apply commutative. apply X.
Defined.

(*
(*
Proof of concept: we can go between IsSemigroup and semigroup easily
*)
Lemma left_id_id' : forall G, IsSemigroup G ->
 forall e : G, Left_id e -> IsId e.
Proof.
intros G Hsg. apply (@left_id_id _).
Defined.

Lemma left_id_id'' : forall {G : semigroup} (e : G), Left_id e -> IsId e.
Proof.
intros G. apply left_id_id'. apply _.
Defined.
*)

Definition identity_sig : forall G : magma, sigT (@IsId G) <~> Identity G.
Proof.
intros; issig (BuildIdentity G) (@identity_val G) (@identity_pr G).
Defined.

Instance identity_prop : forall {G : magma} {Hset : IsHSet G},
 IsHProp (Identity G).
Proof.
intros G Hset. eapply trunc_equiv'. apply identity_sig.
apply hprop_allpath. intros [x Hx] [y Hy].
apply path_sigma with (id_unique _ _ _ _ _).
apply id_prop.
Defined.

Definition ismonoid_sig : forall G : magma, sigT (fun _ : IsSemigroup G => 
Identity G) <~> IsMonoid G.
Proof.
intros;issig (BuildIsMonoid G) (@monoid_is_sg G) (@monoid_id G).
Defined.

Instance ismonoid_prop : forall {G : magma} {Hset : IsHSet G},
 IsHProp (IsMonoid G).
Proof.
intros.
eapply trunc_equiv'. apply ismonoid_sig.
apply @trunc_sigma. apply _.
intro. apply _.
Defined.

Lemma left_cancel_cancel : forall {G} {Hcomm : Commutative G},
forall a : G, Lcancel a -> Cancel a.
Proof.
intros ? ? ? X. split;auto.
red;intros ? ? X0.
red in X. apply X.
eapply concat. apply Hcomm. eapply concat. apply X0. apply Hcomm.
Defined.

Instance cancelling_prop : forall {G : magma} {Hset : IsHSet G} a,
 IsHProp (@Cancel G a).
Proof.
intros.
apply (@trunc_equiv' (sigT (fun _ : Lcancel a => Rcancel a))).
issig (BuildCancel _ a) (@Left_cancel _ a) (@Right_cancel _ a).
apply @trunc_sigma;[|intro C;clear C];apply trunc_forall.
Defined.

Instance iscmono_prop : forall {G : magma} {Hset : IsHSet G},
 IsHProp (IsCMonoid G).
Proof.
intros.
apply (@trunc_equiv' (sigT (fun _ : IsMonoid G => forall a : G, Cancel a))).
issig (BuildIsCMonoid G) (@cmonoid_is_monoid G) (@cmonoid_cancel G).
apply @trunc_sigma.
apply _.
intro; apply _.
Defined.

Lemma linverse_inverse : forall {G : magma} {Hg : Commutative G} (x y : G), 
Linverse x y -> IsInverse x y.
Proof.
intros;split;auto.
red. apply transport with (gop x y). apply Hg.
apply _.
Defined.

Lemma linverse_eq_gid : forall {G : monoid} {x y : G} {Hinv : Linverse x y},
gop x y = gidV.
Proof.
intros. apply id_unique;apply _.
Defined.

Lemma rinverse_eq_gid : forall {G : monoid} {x y : G} {Hinv : Rinverse x y},
gop y x = gidV.
Proof.
intros;apply id_unique;apply _.
Defined.

Lemma isinverse_sig : forall G x y,
 sigT (fun _ : Linverse x y => Rinverse x y) <~> @IsInverse G x y.
Proof.
intros.
issig (BuildIsInverse G x y) (@inverse_left G x y) (@inverse_right G x y).
Defined.

Instance isinverse_prop : forall {G : magma} {Hset : IsHSet G} x y,
 IsHProp (@IsInverse G x y).
Proof.
intros.
eapply trunc_equiv'. apply isinverse_sig.
apply @trunc_sigma;intros;apply id_prop.
Defined.

Instance inverse_symm : forall G, Symmetric (@IsInverse G).
Proof.
red. intros ? ? ? [? ?]. split;red;apply _.
Defined.

Lemma inverse_symm_rw : @IsInverse  = fun G x y => @IsInverse G y x.
Proof.
apply funext_axiom. intro G.
apply funext_axiom. intro x. apply funext_axiom;intro y.
apply univalence_axiom.
eapply transitive_equiv;[|apply isinverse_sig].
apply symmetric_equiv.
issig (fun H H' => BuildIsInverse G x y H' H)
 (@inverse_right G x y) (@inverse_left G x y).
Defined.

Instance rinverse_lcancel : forall {G : magma} {Hassoc : Associative G},
 forall a b : G, Rinverse a b -> Lcancel a.
Proof.
intros ? ? ? ? H.
red. intros x y ?.
path_via (gop (gop b a) x). apply inverse;apply H.
path_via (gop b (gop a x)).
path_via (gop b (gop a y)). apply ap;assumption.
path_via (gop (gop b a) y).
apply H.
Defined.

Instance linverse_rcancel : forall {G : magma} {Hassoc : Associative G},
 forall a b : G, Linverse a b -> Rcancel a.
Proof.
intros ? ? ? ? H.
red. intros x y ?.
path_via (gop x (gop a b)). apply inverse;apply H.
path_via (gop (gop x a) b).
path_via (gop (gop y a) b). apply (ap (fun g => gop g b));assumption.
path_via (gop y (gop a b)).
apply H.
Defined.

Instance isinverse_cancel : forall {G : magma} {Hassoc : Associative G},
 forall a b : G, IsInverse a b -> Cancel a.
Proof.
intros;split;apply _.
Defined.

Instance inverse_cancel : forall {G : magma} {Hassoc : Associative G}
 (a : G), Inverse a -> Cancel a.
Proof.
intros ? ? ? [b H]. apply isinverse_cancel with b.
assumption.
Defined.

Definition easyIsGroup (G : magma) {Hg : IsMonoid G}
 (gopp : forall x : G, Inverse x) := 
BuildIsGroup G (BuildIsCMonoid G Hg
 (fun a => inverse_cancel a (gopp a))) gopp.

Lemma inverse_unicity : forall {G : magma} {Hassoc : Associative G},
 forall x : G,  atmost1P (IsInverse x).
Proof.
intros ? ? ? y y' X X0. apply inverse_cancel with x. exists y;exact X.
apply id_unique;apply _.
Defined.

Definition inverse_sig : forall {G : magma} (x : G), 
sigT (IsInverse x) <~> Inverse x.
Proof.
intros.
issig (BuildInverse G x) (@inverse_val G x) (@inverse_is_inverse G x).
Defined.

Instance inverse_prop : forall {G : magma} {Hset : IsHSet G} {Ha : Associative G}
(x : G), IsHProp (Inverse x).
Proof.
intros.
eapply trunc_equiv'. apply inverse_sig.
apply hprop_allpath. intros [y H] [y' Hy'].
apply path_sigma with (inverse_unicity _ _ _ _ _). apply isinverse_prop.
Defined.

Lemma group_inverse_gopp : forall {G : group}, forall x y : G,
 @IsInverse G x y -> @paths G (goppV x) y.
Proof.
intros. 
apply (@inverse_unicity G _) with x.
 apply gopp_correct.
 assumption.
Defined.

Lemma gopp_gopp : forall {G : group} (x : G), @paths G (goppV (goppV x)) x.
Proof.
intros. apply group_inverse_gopp.
apply inverse_symm. apply gopp_correct.
Defined.

Instance gid_isinverse : forall G : monoid, @IsInverse G gidV gidV.
Proof.
intros.
split;red;(apply transport with gidV;[symmetry;apply gid|]);apply _.
Defined.

Lemma gopp_gid : forall G : group, @paths G (gopp gidV) gidV.
Proof.
intros. apply group_inverse_gopp. apply _.
Defined.

Lemma linverse_gop : forall {G : magma} {Hassoc : Associative G},
forall x x' : G, Linverse x x' ->
forall y y' : G, Linverse y y' ->
  Linverse (gop x y) (gop y' x').
Proof.
intros ? ? ? ? Hx ? ? Hy.
red. split;red;intro z.
- path_via (gop x (gop (gop y y') (gop x' z))).
  eapply concat. symmetry;apply Hassoc.
  eapply concat. symmetry;apply Hassoc. apply ap.
  eapply concat;[|apply Hassoc]. apply ap. symmetry;apply Hassoc.
  path_via (gop x (gop x' z)). apply ap. apply Hy.
  path_via (gop (gop x x') z). apply Hx.
- path_via (gop (gop z x) (gop (gop y y') x')).
  eapply concat;[|apply Hassoc]. apply ap.
  eapply concat;[symmetry;apply Hassoc|]. apply ap. apply Hassoc.
  path_via (gop (gop z x) x'). apply ap. apply Hy.
  path_via (gop z (gop x x')). apply Hx.
Defined.

Lemma rinverse_gop : forall {G : magma} {Hassoc : Associative G},
forall x x' : G, Rinverse x x' ->
forall y y' : G, Rinverse y y' ->
  Rinverse (gop x y) (gop y' x').
Proof.
intros ? ?.
change (forall x x' : G, Linverse x' x -> forall y y' : G, Linverse y' y ->
  Linverse (gop y' x') (gop x y)).
intros;apply linverse_gop;assumption.
Defined.

Lemma isinverse_gop : forall {G : magma} {Hassoc : Associative G},
forall x x' : G, IsInverse x x' ->
forall y y' : G, IsInverse y y' ->
  IsInverse (gop x y) (gop y' x').
Proof.
intros;split;[apply linverse_gop|apply rinverse_gop];apply _.
Defined.

Lemma gopp_gop : forall G : group, forall x y : G,
 @paths G (gopp (gop x y)) (gop (gopp y) (gopp x)).
Proof.
intros. apply group_inverse_gopp.
apply isinverse_gop;apply _.
Defined.

Lemma gopp_cop_comm : forall G : group, forall x y : G,
 @paths G (gopp (gop x y)) (gop (gopp x) (gopp y)).
Proof.
intros;path_via (gop (gopp y) (gopp x)).
apply gopp_gop. apply commutative.
Defined.

Instance gopp_prop : forall (G : monoid) {Hset : IsHSet G},
 IsHProp (forall x : G, Inverse x).
Proof.
intros.
apply trunc_forall.
Defined.

Definition isgroup_sig : forall G : magma, 
sigT (fun Hmon : IsCMonoid G => forall x : G, Inverse x) <~> IsGroup G.
Proof.
intros.
issig (BuildIsGroup G) (@group_is_cmonoid G) (@g_opp G).
Defined.

Instance isgroup_prop : forall {G : magma} {Hset : IsHSet G},
 IsHProp (IsGroup G).
Proof.
intros;eapply trunc_equiv'. apply isgroup_sig.
apply @trunc_sigma. apply _.
intro. apply _.
Defined.

End Magma_pr.

Module Related_pr.
Export Relation.
Import minus1Trunc.

Instance istrans_prop : forall {r : Relation}
 {Hprop : RelationProp r}, IsHProp (IsTransitive r).
Proof.
intros.
apply trunc_forall.
Defined.

Instance isrefl_prop : forall {r : Relation}
 {Hprop : RelationProp r}, IsHProp (IsReflexive r).
Proof.
intros.
apply trunc_forall.
Defined.

Instance issymm_prop : forall {r : Relation}
 {Hprop : RelationProp r}, IsHProp (IsSymmetric r).
Proof.
intros.
apply trunc_forall.
Defined.

Definition IsEquivalence_sig : forall r, 
sigT (fun _ : IsReflexive r => sigT (fun _ : IsSymmetric r => IsTransitive r))
<~> IsEquivalence r.
Proof.
intro r. issig (BuildIsEquivalence r) (@equivalence_refl r) (@equivalence_symm r)
  (@equivalence_trans r).
Defined.

Instance isequivalence_prop : forall {r : Relation}
 {Hprop : RelationProp r}, IsHProp (IsEquivalence r).
Proof.
intros.
eapply trunc_equiv'.
apply IsEquivalence_sig.
apply @trunc_sigma. apply _.
intro. apply @trunc_sigma. apply _.
intro;apply _.
Defined.

Lemma irrefl_neq : forall {R} {Hr : IsIrreflexive R}, 
  forall x y : R, rrel x y -> neq x y.
Proof.
intros ? ? ? ? ?. intros H. destruct H. apply Hr with x. assumption.
Defined.

Instance isantisymm_prop : forall {r : Relation} {Hset : IsHSet r},
 IsHProp (IsAntisymmetric r).
Proof.
intros.
apply trunc_forall.
Defined.

Instance isirrefl_prop : forall {r}, IsHProp (IsIrreflexive r).
Proof.
intros.
apply trunc_forall.
Defined.

Definition isposet_sig : forall r, sigT (fun _ : IsTransitive r => 
sigT (fun _ : IsReflexive r => IsAntisymmetric r)) <~> IsPoset r.
Proof.
intro r;
issig (BuildIsPoset r) (@order_trans r) (@order_refl r) (@order_antisymm r).
Defined.

Instance isposet_prop : forall {r : Relation} {Hset : IsHSet r}
 {Hprop : RelationProp r}, IsHProp (IsPoset r).
Proof.
intros.
eapply trunc_equiv'.
apply isposet_sig.
apply @trunc_sigma. apply _.
intro. apply @trunc_sigma. apply _.
intro;apply _.
Defined.

Instance iscotrans_prop : forall {r}, IsHProp (IsCotransitive r).
Proof.
intros.
apply trunc_forall.
Defined.

Definition isapart_sig : forall r, sigT (fun _ : IsIrreflexive r =>
sigT (fun _ : IsSymmetric r => sigT (fun _ : IsCotransitive r => 
 forall x y : r, ~ rrel x y -> x=y))) <~> IsApartness r.
Proof.
intros.
issig (BuildIsApartness r) (@apart_irrefl r) (@apart_symm r) (@apart_cotrans r)
  (@apart_tight r).
Defined.

Instance isapart_prop : forall {r : Relation}
 {Hpr : IsMereRelator r}, IsHProp (IsApartness r).
Proof.
intros;eapply trunc_equiv'.
apply isapart_sig.
apply @trunc_sigma. apply _.
intro. apply @trunc_sigma. apply _.
intro. apply @trunc_sigma. apply _.
intro. apply trunc_forall.
Defined.

Lemma apart_from_neq : forall {r} {Ha : IsApartness r}, forall x y : r,
~x=y -> ~ ~ x <> y.
Proof.
intros ? ? ? ? H ?.
apply H;apply apart_tight. assumption.
Defined.

Lemma apart_prove_eq : forall {r} {Ha : IsApartness r},
forall a b x y : r, (rrel x y -> a=b) -> (~x=y -> a=b).
Proof.
intros ? ? ? ? ? ? H H'.
apply apart_tight. intro H0.
assert (Hx : ~ ~ x <> y).
apply apart_from_neq. assumption.
apply Hx;clear Hx;intro Hx.
eapply irrefl_neq. apply H0. auto.
Defined.

Instance islinear_prop : forall {r}, IsHProp (IsLinear r).
Proof.
intro.
apply trunc_forall.
Defined.

Instance constrlinear_linear : forall {r}, IsConstrLinear r -> IsLinear r.
Proof.
red;intros;apply min1;auto.
Defined.

Instance constrtotal_total : forall {r}, IsConstrTotalOrder r -> IsTotalOrder r.
Proof.
intros. constructor; apply _.
Defined.

Definition isstrictorder_sig : forall r, sigT (fun _ : IsIrreflexive r => 
IsTransitive r) <~> IsStrictOrder r.
Proof.
intros. issig (BuildIsStrictOrder r) (@strictorder_irrefl r)
  (@strictorder_trans r).
Defined.

Instance isstrictorder_prop : forall {r : LtRelation}
 {Hp : RelationProp r}, IsHProp (IsStrictOrder r).
Proof.
intros. eapply trunc_equiv'.
apply isstrictorder_sig.
apply @trunc_sigma. apply _. intros;apply _.
Defined.

Lemma strict_poset_antisymm : forall (r : LtRelation)
 {Hstrict : IsStrictOrder r}, forall x y : r, x < y /\ y < x -> Empty.
Proof.
intros ? ? ? ? [? ?]. destruct Hstrict as [Hirr Htrans].
apply Hirr with x;eauto.
Defined.

Instance strict_poset_disjunct_prop : forall (r : LtRelation)
 {Hp : RelationProp r}
 {Hstrict : IsStrictOrder r}, forall x y : r,
  IsHProp (x < y \/ y < x).
Proof.
intros. apply hprop_allpath.
intros [Hx|Hx] [Hy|Hy];try (apply ap;apply Hp).
destruct (strict_poset_antisymm _ _ _ (Hx, Hy)).
destruct (strict_poset_antisymm _ _ _ (Hx, Hy)).
Defined.

Lemma neq_irrefl : forall r : Relation, (forall x y : r, rrel x y -> ~ x=y) -> 
IsIrreflexive r.
Proof.
intros ? H0;intros x H.
apply H0 in H. apply H;reflexivity.
Defined.

Lemma neq_symm : forall r : Relation, (forall x y : r, rrel x y <-> ~x=y) -> 
IsSymmetric r.
Proof.
red;red;intros ? H ? ? H'.
apply H. apply H in H'. intro H0;apply H';symmetry;assumption.
Defined.

Lemma neq_cotrans : forall r : Relation, decidable_paths r ->
(forall x y : r, rrel x y <-> ~x=y) -> IsCotransitive r.
Proof.
intros ? Hdec Hneq x y H z.
apply min1.
destruct (Hdec x z) as [[]|H']. right. assumption.
left;auto;apply Hneq;auto.
Defined.

Lemma neq_apart : forall r : Relation, decidable_paths r ->
(forall x y : r, rrel x y <-> ~x=y) -> IsApartness r.
Proof.
intros ? Hdec Hneq;split.
apply neq_irrefl;intros;apply Hneq;assumption.
apply neq_symm;assumption.
apply neq_cotrans;assumption.
intros ? ? H.
destruct (Hdec x y) as [?|n]. assumption.
apply Hneq in n. destruct H;assumption.
Defined.


Section PseudoOrder.

Context r {Hpr : RelationProp (RR_to_R2 r)} {Hpo : IsPseudoOrder r}.

Lemma apart_total_lt (x y : r) : x <> y -> x < y \/ y < x.
Proof.
apply apart_iff_total_lt.
Defined.

Lemma pseudo_order_lt_apart (x y : r) : x < y -> x <> y.
Proof.
intros. apply apart_iff_total_lt. left;assumption.
Defined.

Lemma pseudo_order_lt_apart_flip (x y : r) : x < y -> y <> x.
Proof.
intros. apply apart_iff_total_lt. right;assumption.
Defined.

Lemma not_lt_apart_lt_flip (x y : r) : ~x < y -> x <> y -> y < x.
Proof.
intros H H'. apply apart_iff_total_lt in H'. destruct H';auto.
destruct H;assumption.
Defined.

Lemma pseudo_order_cotrans_twice (x1 y1 x2 y2 : r)
 : x1 < y1 -> minus1Trunc (x2 < y2 \/ x1 < x2 \/ y2 < y1).
Proof.
intros E1.
pose (Htmp := iscotransitive _ _ E1 x2).
clearbody Htmp. change (minus1Trunc ((x1 < x2) \/ (x2 < y1))) in Htmp.
revert Htmp;apply minus1Trunc_rect_nondep;[|apply minus1Trunc_is_prop].
intros [E2|E2].
apply min1;auto.
pose (Htmp := iscotransitive _ _ E2 y2). clearbody Htmp.
revert Htmp;apply minus1Trunc_rect_nondep;[|apply minus1Trunc_is_prop].
intros [E3|E3];apply min1; auto.
Defined.

Lemma pseudo_order_lt_ext (x1 y1 x2 y2 : r)
 : x1 < y1 -> minus1Trunc (x2 < y2 \/ x1 <> x2 \/ y2 <> y1).
Proof.
intros E.
pose (H := pseudo_order_cotrans_twice x1 y1 x2 y2 E). clearbody H;revert H.
apply minus1Trunc_rect_nondep;[|apply minus1Trunc_is_prop].
intros [?|[?|?]];apply min1; auto using pseudo_order_lt_apart.
Defined.

Global Instance pseudo_is_strict : IsStrictOrder (RR_to_R2 r).
Proof.
split.
- intros x E. destruct pseudoorder_is_antisym with x x;assumption.
- intros x y z E1 E2.
  pose (Htmp := iscotransitive _ _ E1 z);clearbody Htmp;revert Htmp.
  apply minus1Trunc_rect_nondep;[|apply Hpr]. intros [?|?].
  assumption.
  destruct pseudoorder_is_antisym with y z;auto.
Defined.

Global Instance pseudo_complement_trans : Transitive (fun x y : r => ~ x<y).
Proof.
intros x y z.
intros E1 E2 E3.
pose (Htmp := iscotransitive _ _ E3 y);clearbody Htmp;revert Htmp.
apply minus1Trunc_rect_nondep;[|intros []].
intros [?|?] ; contradiction.
Defined.

Global Instance pseudo_complement_antisym
 : IsAntisymmetric (BuildRelation r (fun x y => ~ x < y)).
Proof.
red;simpl. (* warning: <= is complement < here! *)
intros x y H H0.
apply (@apart_tight (RR_to_R1 r) _).
intro H';apply apart_iff_total_lt in H'. destruct H' as [H'|H'];auto.
Defined.

End PseudoOrder.


Section FullPoset.

Context r {Hpr : RelationProp (RRR_to_R1 r)} {Hpo : IsFullPoset r}.

Lemma lt_le : forall x y : r, x < y -> x <= y.
Proof.
intros ? ? H.
apply lt_iff_le_apart in H. apply H.
Defined.

Lemma lt_apart : forall (x y : r), x < y -> x <> y.
Proof.
intros ? ? H.
apply lt_iff_le_apart in H. apply H.
Defined.

Lemma le_not_lt_flip : forall (x y : r), x <= y -> ~ y < x.
Proof.
intros ? ? H H'.
apply lt_iff_le_apart in H'.
destruct H' as [H0 H1].
apply irrefl_neq in H1. apply H1.
apply (@isantisymm (RRR_to_R2 r) _);assumption.
Defined.

Lemma lt_not_le_flip : forall (x y : r), x < y -> ~ y <= x.
Proof.
intros ? ? H H'.
apply lt_iff_le_apart in H.
destruct H as [H0 H1].
apply irrefl_neq in H1. apply H1.
apply (@isantisymm (RRR_to_R2 r) _);assumption.
Defined.

Lemma lt_le_trans : forall x y : r, x < y ->
 forall z, y <= z -> x < z.
Proof.
intros ? ? H ? H'.
apply lt_iff_le_apart in H. destruct H as [H0 H1].
apply lt_iff_le_apart. split.
- eapply istrans. apply H0. apply H'.
- pose (H := apart_cotrans _ _ H1 z). clearbody H.
  change (minus1Trunc ((x<>z) + (z<>y))) in H.
  revert H. apply minus1Trunc_rect_nondep;[|apply Hpr].
  intros [H|H]. assumption.
  apply lt_apart. apply issymm in H.
  apply (@istrans (RRR_to_R3 r) _ _ y);apply lt_iff_le_apart;split;auto.
Defined.

Lemma le_lt_trans : forall x y : r, x <= y -> forall z, y < z -> x < z.
Proof.
intros ? ? H ? H'.
apply lt_iff_le_apart in H';apply lt_iff_le_apart.
destruct H' as [H0 H1];split.
- eapply istrans;[apply H|apply H0].
- pose (H' := apart_cotrans _ _ H1 x).
  clearbody H'. change (minus1Trunc ((y<>x) + (x<>z))) in H'. revert H'.
  apply minus1Trunc_rect_nondep;[|apply Hpr].
  intros [H' | H'];trivial.
  apply lt_apart.
  apply (@istrans (RRR_to_R3 r) _ _ y);apply lt_iff_le_apart;split;auto.
  apply issymm. assumption.
Defined.

End FullPoset.

Section FullPseudoOrder.

Context r {Hpr : RelationProp (RRR_to_R3 r)} {Hpo : IsFullPseudoOrder r}.

Lemma not_lt_le_flip : forall x y : r, ~y<x -> x<=y.
Proof.
intros. apply le_iff_not_lt_flip. assumption.
Defined.

Instance: IsPoset (RRR_to_R2 r).
Proof.
split.
- intros x y z H H'.
  apply le_iff_not_lt_flip.
  apply le_iff_not_lt_flip in H.
  apply le_iff_not_lt_flip in H'.
  revert H;revert H'.
  apply (@pseudo_complement_trans (RRR_to_R1R3 r) _).
- intros x. change (x <= x). apply le_iff_not_lt_flip.
  revert x. change (IsIrreflexive (RRR_to_R3 r)). apply @strictorder_irrefl.
  change (IsStrictOrder (RR_to_R2 (RRR_to_R1R3 r))). apply _.
- intros x y H H'. simpl in x,y.
  apply le_iff_not_lt_flip in H;apply le_iff_not_lt_flip in H'.
  apply (@pseudo_complement_antisym (RRR_to_R1R3 r) _);assumption.
Defined.

Global Instance fullpseudo_is_fullposet : IsFullPoset r.
Proof.
split.
change (IsApartness (RR_to_R1 (RRR_to_R1R3 r))). apply _.
apply _.
change (IsTransitive (RR_to_R2 (RRR_to_R1R3 r)));apply _.
intros x y. split.
intro H. split. apply le_iff_not_lt_flip.
red. apply (@pseudoorder_is_antisym (RRR_to_R1R3 r) _). assumption.
apply (@apart_iff_total_lt (RRR_to_R1R3 r) _). auto.
intros [H0 H1].
apply (@apart_iff_total_lt (RRR_to_R1R3 r) _) in H1. destruct H1.
assumption.
apply le_iff_not_lt_flip in H0. destruct H0;assumption.
Defined.

(* since x<=y is ~y<x, the double negation is equivalent *)
Lemma le_stable : forall x y : r, ~ ~ x <= y -> x<=y.
Proof.
intros ? ? H. apply le_iff_not_lt_flip. intro.
apply H. intro H'. apply le_iff_not_lt_flip in H'. auto.
Defined.

End FullPseudoOrder.


Instance maximum_is_supremum : forall r P m, 
IsMaximum r P m -> IsSupremum r P m.
Proof.
intros ? ? ? [Hup Hp].
split.
intros x Hx.
apply Hx. assumption.
assumption.
Defined.

Instance minimum_is_infimum : forall r P m, 
IsMinimum r P m -> IsInfimum r P m.
Proof.
intros ? ? ? [Hlow Hp].
split.
intros x Hx.
apply Hx. assumption.
assumption.
Defined.

Lemma supremum_unicity : forall r {Ho : IsPoset r}, 
forall P, atmost1P (IsSupremum r P).
Proof.
intros. intros m m' Hm Hm'.
apply Ho;[apply Hm;apply Hm' | apply Hm';apply Hm].
Defined.

Lemma infimum_unicity : forall r {Ho : IsPoset r}, 
forall P, atmost1P (IsInfimum r P).
Proof.
intros. intros m m' Hm Hm'.
apply Ho;[apply Hm';apply Hm | apply Hm;apply Hm'];apply _.
Defined.

Lemma maximum_unicity : forall r {Ho : IsPoset r}, 
forall P, atmost1P (IsMaximum r P).
Proof.
intros;intros m m' Hm Hm';eapply supremum_unicity;apply _.
Defined.

Lemma minimum_unicity : forall r {Ho : IsPoset r}, 
forall P, atmost1P (IsMinimum r P).
Proof.
intros;intros m m' Hm Hm';eapply infimum_unicity;apply _.
Defined.

Definition maximum_supremum : forall {r P}, Maximum r P -> Supremum r P.
Proof.
intros ? ? m. exists (maximum_val m). apply maximum_is_supremum;apply _.
Defined.

Definition minimum_infimum : forall {r P}, Minimum r P -> Infimum r P.
Proof.
intros ? ? m. exists (minimum_val m). apply minimum_is_infimum;apply _.
Defined.

Instance upper_prop : forall (r : LeqRelation)
 {Hp : forall x y : r, IsHProp (x <= y)},
forall P m, IsHProp (IsUpper r P m).
Proof.
intros.
apply trunc_forall.
Defined.

Instance lower_prop : forall (r : LeqRelation)
 {Hp : forall x y : r, IsHProp (x <= y)},
forall P m, IsHProp (IsLower r P m).
Proof.
intros.
apply trunc_forall.
Defined.

Definition ismax_sig : forall r P m, sigT (fun _ : IsUpper r P m => 
P m) <~> IsMaximum r P m.
Proof.
intros. issig (BuildIsMaximum r P m) (@maximum_upper r P m)
 (@maximum_verifies r P m).
Defined.

Definition ismin_sig : forall r P m, sigT (fun _ : IsLower r P m => 
P m) <~> IsMinimum r P m.
Proof.
intros. issig (BuildIsMinimum r P m) (@minimum_lower r P m)
 (@minimum_verifies r P m).
Defined.

Instance ismaximum_prop : forall (r : LeqRelation)
 {Hp : forall x y : r, IsHProp (x <= y)} P {Hp' : forall x, IsHProp (P x)} m,
IsHProp (IsMaximum r P m).
Proof.
intros;eapply trunc_equiv'. apply ismax_sig.
apply trunc_sigma.
Defined.

Instance isminimum_prop : forall (r : LeqRelation)
 {Hp : forall x y : r, IsHProp (x <= y)} P {Hp' : forall x, IsHProp (P x)} m,
IsHProp (IsMinimum r P m).
Proof.
intros;eapply trunc_equiv'. apply ismin_sig.
apply trunc_sigma.
Defined.

Instance issupremum_prop : forall (r : LeqRelation)
 {Hp : forall x y : r, IsHProp (x <= y)},
forall P m, IsHProp (IsSupremum r P m).
Proof.
intros. apply isminimum_prop;apply _.
Defined.

Instance isinfimum_prop : forall (r : LeqRelation)
 {Hp : forall x y : r, IsHProp (x <= y)},
forall P m, IsHProp (IsInfimum r P m).
Proof.
intros;apply ismaximum_prop;apply _.
Defined.

Definition maximum_sig : forall r P, sigT (IsMaximum r P) <~> Maximum r P.
Proof.
intros;issig (BuildMaximum r P) (@maximum_val r P) (@maximum_is_maximum r P).
Defined.

Definition minimum_sig : forall r P, sigT (IsMinimum r P) <~> Minimum r P.
Proof.
intros;issig (BuildMinimum r P) (@minimum_val r P) (@minimum_is_minimum r P).
Defined.

Instance maximum_prop : forall {r} {Ho : IsPoset r}
{Hr : forall x y : r, IsHProp (x <= y)} P {Hp : forall x, IsHProp (P x)},
IsHProp (Maximum r P).
Proof.
intros;eapply trunc_equiv'. apply maximum_sig.
apply hprop_allpath. intros [x Hx] [y Hy].
apply path_sigma with (maximum_unicity _ _ _ _ _ _).
apply ismaximum_prop;apply _.
Defined.

Instance minimum_prop : forall {r} {Ho : IsPoset r}
{Hr : RelationProp r} P {Hp : forall x, IsHProp (P x)},
IsHProp (Minimum r P).
Proof.
intros;eapply trunc_equiv'. apply minimum_sig.
apply hprop_allpath. intros [x Hx] [y Hy].
apply path_sigma with (minimum_unicity _ _ _ _ _ _).
apply isminimum_prop;apply _.
Defined.

Instance supremum_prop : forall {r} {Ho : IsPoset r}
{Hp : RelationProp r}, 
forall P, IsHProp (Supremum r P).
Proof.
intros.
apply minimum_prop;apply _.
Defined.

Instance infimum_prop : forall {r} {Ho : IsPoset r}
{Hp : RelationProp r}, 
forall P, IsHProp (Infimum r P).
Proof.
intros;apply maximum_prop;apply _.
Defined.

Definition islattice_sig : forall r, 
sigT (fun _ : IsPoset r => sigT (fun _ :
   (forall a b, Supremum r (doubleton a b)) => 
      forall a b, Infimum r (doubleton a b))) <~> IsLattice r.
Proof.
intros. issig (BuildIsLattice r) (@lattice_is_poset r) (@lattice_has_sup2 r)
  (@lattice_has_inf2 r).
Defined.

Instance islattice_prop : forall (r : Relation)
{Hset : IsHSet r} {Hp : RelationProp r}, 
IsHProp (IsLattice r).
Proof.
intros. eapply trunc_equiv'. apply islattice_sig.
repeat (apply @trunc_sigma;[try apply _ | intro]).
apply _.
Defined.

Instance doubleton_is_prop : forall {T} {a b x : T}, IsHProp (doubleton a b x).
Proof.
intros;apply minus1Trunc_is_prop.
Defined.

Definition doubleton_comm_fun : forall {T} (a b x : T),
 doubleton a b x -> doubleton b a x.
Proof.
intros ? ? ? ?;apply minus1Trunc_rect_nondep.
intros [H|H];apply min1;auto.
apply minus1Trunc_is_prop.
Defined.

Lemma doubleton_comm_equiv : forall {T} (a b x : T),
 doubleton a b x <~> doubleton b a x.
Proof.
intros. apply equiv_iff_hprop;apply doubleton_comm_fun.
Defined.

Lemma doubleton_comm : forall {T} {a b : T},
 doubleton a b = doubleton b a.
Proof.
intros. apply funext_axiom.
intro x;apply univalence_axiom. apply doubleton_comm_equiv.
Defined.

Lemma total_order_max2 : forall {r : LeqRelation} {Hset : IsHSet r}
{Hpr : forall x y : r, IsHProp (x <= y)} {Hto : IsTotalOrder r},
forall a b, Maximum2 r a b.
Proof.
intros.
destruct Hto as [Hpo Hlin].
eapply minus1Trunc_rect_nondep;[|apply maximum_prop|apply (Hlin a b)].
intros [H|H].
- exists b. split. intros x.
  apply minus1Trunc_rect_nondep;[|apply Hpr]. intros [[]|[]];auto. apply Hpo.
  apply min1. right;reflexivity.
- exists a. split. intros x.
  apply minus1Trunc_rect_nondep;[|apply Hpr]. intros [[]|[]];auto. apply Hpo.
  apply min1. left;reflexivity.
- intros;apply minus1Trunc_is_prop.
Defined.

Lemma total_order_min2 : forall {r : LeqRelation}
{Hset : IsHSet r} {Hpr : RelationProp r} {Hto : IsTotalOrder r},
forall a b, Minimum2 r a b.
Proof.
intros.
destruct Hto as [Hpo Hlin].
eapply minus1Trunc_rect_nondep;[|apply minimum_prop|apply (Hlin a b)].
intros [H|H].
- exists a. split. intros x.
  apply minus1Trunc_rect_nondep;[|apply Hpr]. intros [[]|[]];auto. apply Hpo.
  apply min1. left;reflexivity.
- exists b. split. intros x.
  apply minus1Trunc_rect_nondep;[|apply Hpr]. intros [[]|[]];auto. apply Hpo.
  apply min1. right;reflexivity.
- intros;apply minus1Trunc_is_prop.
Defined.

Instance total_order_lattice : forall {r : Relation} {Hset : IsHSet r}
{Hpr : RelationProp r}
{Hto : IsTotalOrder r}, IsLattice r.
Proof.
intros;split. apply _.
intros. apply maximum_supremum. apply total_order_max2.
intros. apply minimum_infimum. apply total_order_min2.
Defined.

Definition is_union {T : Type} (P1 P2 P' : T -> Type) :=
 forall x, P' x <-> minus1Trunc (P1 x \/ P2 x).
Definition is_inter {T : Type} (P1 P2 P' : T -> Type) :=
 forall x, P' x <-> (P1 x /\ P2 x).

Definition singleton {T : Type} (x : T) := doubleton x x.

Instance singleton_min : forall {r : LeqRelation} {Hpr : RelationProp r}
 {Hr : IsReflexive r} x, IsMinimum r (singleton x) x.
Proof.
intros. split.
intros y. apply minus1Trunc_rect_nondep;[|apply Hpr].
intros [[]|[]];apply Hr.
apply min1;left;reflexivity.
Defined.

Lemma singleton_paths : forall {T : Type} {Hset : IsHSet T} (x : T),
singleton x = paths x.
Proof.
intros. apply funext_axiom;intros y.
apply univalence_axiom. apply @equiv_iff_hprop.
apply minus1Trunc_is_prop. apply hprop_allpath;apply Hset.
apply minus1Trunc_rect_nondep. intros [?|?];assumption.
apply Hset.
intros H;apply min1;left;assumption.
Defined.

Section UnionInterSec.

Context {r : LeqRelation} {Hset : IsHSet r} {Hpr : RelationProp r}
{Hpo : IsPoset r}
{P1 P2 P' : r -> Type}
{Hp1 : forall x, IsHProp (P1 x)} {Hp2 : forall x, IsHProp (P2 x)}
{Hp' : forall x, IsHProp (P' x)}.

Lemma lower_union_inter : is_union P1 P2 P' ->
 is_inter (IsLower r P1) (IsLower r P2) (IsLower r P').
Proof.
intros Hu x;split.
- intro H;split;
  intros y Hy; apply H;
  apply Hu; apply min1;auto.
- intros [H1 H2] y H.
  apply Hu in H. revert H. apply minus1Trunc_rect_nondep;[|apply Hpr].
  intros [?|?];auto.
Defined.

Lemma upper_union_inter : is_union P1 P2 P' ->
 is_inter (IsUpper r P1) (IsUpper r P2) (IsUpper r P').
Proof.
intros Hu x;split.
- intro H;split;
  intros y Hy; apply H;
  apply Hu; apply min1;auto.
- intros [H1 H2] y H.
  apply Hu in H. revert H. apply minus1Trunc_rect_nondep;[|apply Hpr].
  intros [?|?];auto.
Defined.

Lemma infimum_of_union : is_union P1 P2 P' -> 
forall a, IsInfimum r P1 a -> forall b, IsInfimum r P2 b ->
forall x, IsInfimum r P' x -> IsInfimum r (doubleton a b) x.
Proof.
intros Hu ? Ha ? Hb ? Hx.
split.
- intros y Hy.
  apply Hx. intros z Hz.
  apply Hu in Hz. revert Hz;apply minus1Trunc_rect_nondep;[|apply Hpr].
  intros [Hz|Hz].
  apply order_trans with a. apply Hy;apply min1;auto.
  apply Ha. assumption.
  apply order_trans with b. apply Hy;apply min1;auto.
  apply Hb. assumption.
- intros y.
  apply minus1Trunc_rect_nondep;[|apply Hpr].
  intros [[]|[]];clear y.
  apply Ha. apply lower_union_inter. assumption. apply _.
  apply Hb. apply lower_union_inter. assumption. apply _.
Defined.

Lemma infimum_to_union : is_union P1 P2 P' ->
forall a, IsInfimum r P1 a -> forall b, IsInfimum r P2 b ->
forall x, IsInfimum r (doubleton a b) x -> IsInfimum r P' x.
Proof.
intros Hu ? Ha ? Hb ? Hx.
split.
- intros y Hy.
  apply Hx.
  intros z. apply minus1Trunc_rect_nondep;[|apply Hpr]. intros [[]|[]].
  apply Ha. apply lower_union_inter;assumption.
  apply Hb. apply lower_union_inter;assumption.
- intros y Hy. apply Hu in Hy;revert Hy.
  apply minus1Trunc_rect_nondep;[|apply Hpr].
  intros [Hy|Hy].
  apply order_trans with a. apply Hx. apply min1;auto.
  apply Ha. assumption.
  apply order_trans with b. apply Hx. apply min1;auto.
  apply Hb. assumption.
Defined.

Lemma infimum_union : is_union P1 P2 P' ->
forall a, IsInfimum r P1 a -> forall b, IsInfimum r P2 b ->
forall x, IsInfimum r P' x <-> IsInfimum r (doubleton a b) x.
Proof.
intros Hu ? Ha ? Hb x.
split.
apply infimum_of_union;assumption.
apply infimum_to_union;assumption.
Defined.

Lemma infimum_union_and : is_union P1 P2 P' -> forall x, 
IsInfimum r P1 x -> IsInfimum r P2 x ->
IsInfimum r P' x.
Proof.
intros Hu;intros. apply infimum_to_union with x x;try assumption.
apply _.
Defined.

End UnionInterSec.

End Related_pr.

Module OMag_pr.
Export OrderedMagma Magma_pr Related_pr.

Lemma invariant_compat : forall (G : LR_sig) {Htrans : IsTransitive G},
 IsInvariant G -> IsCompat G.
Proof.
red;intros ? ? Hinv ? ? X ? ? Y.
apply Htrans with (gop x y');[apply invariant_left | apply invariant_right];
assumption.
Defined.

Instance compat_linvariant : forall (G : LR_sig) {Hrefl : IsReflexive G}, 
IsCompat G -> IsLInvariant G.
Proof.
red;intros ? ? Hc ? ? ? ?.
apply Hc. apply Hrefl.
assumption.
Defined.

Instance compat_rinvariant : forall (G : LR_sig) {Hrefl : IsReflexive G}, 
IsCompat G -> IsRInvariant G.
Proof.
red;intros ? ? Hc ? ? ? ?.
apply Hc. assumption.
apply Hrefl.
Defined.

Instance linvariant_prop : forall (G : LR_sig)
 {Hprop : forall x y : G, IsHProp (rrel x y)}, IsHProp (IsLInvariant G).
Proof.
intros.
apply @trunc_forall. apply _.
intro. apply trunc_forall.
Defined.

Instance rinvariant_prop : forall (G : LR_sig)
 {Hprop : forall x y : G, IsHProp (rrel x y)}, IsHProp (IsRInvariant G).
Proof.
intros.
apply @trunc_forall. apply _.
intro. apply trunc_forall.
Defined.

Definition invariant_sig : forall G : LR_sig, 
sigT (fun _ : IsLInvariant G => IsRInvariant G) <~> IsInvariant G.
Proof.
intros.
issig (BuildIsInvariant G) (@invariant_left G) (@invariant_right G).
Defined.

Instance invariant_prop : forall (G : LR_sig)
 {Hprop : forall x y : G, IsHProp (rrel x y)}, IsHProp (IsInvariant G).
Proof.
intros;eapply trunc_equiv'.
apply invariant_sig.
apply @trunc_sigma. apply _.
intro; apply _.
Defined.

Instance compat_prop : forall (G : LR_sig)
 {Hprop : forall x y : G, IsHProp (rrel x y)}, IsHProp (IsCompat G).
Proof.
intros.
apply trunc_forall.
Defined.

Lemma rinverse_lregular : forall {G : LR_sig} {Hassoc : Associative G}
{Hcompat : IsLInvariant G}
(x y : G) {Hinv : Rinverse x y}, IsLRegular G x.
Proof.
intros;red. intros a b H.
pattern b. apply transport with (gop y (gop x b)).
path_via (gop (gop y x) b). apply Hinv.
pattern a. apply transport with (gop y (gop x a)).
path_via (gop (gop y x) a). apply Hinv.
apply Hcompat. assumption.
Defined.

Lemma linverse_rregular : forall {G : LR_sig} {Hassoc : Associative G}
{Hcompat : IsRInvariant G}
(x y : G) {Hinv : Linverse x y}, IsRRegular G x.
Proof.
intros;red. intros a b H.
pattern b. apply transport with (gop (gop b x) y).
path_via (gop b (gop x y)). apply Hinv.
pattern a. apply transport with (gop (gop a x) y).
path_via (gop a (gop x y)). apply Hinv.
apply Hcompat. assumption.
Defined.

Lemma inverse_regular : forall (G : LR_sig) {Hassoc : Associative G}
{Hcompat : IsInvariant G}
(x y : G) {Hinv : IsInverse x y}, IsRegular G x.
Proof.
intros;split;[eapply rinverse_lregular|eapply linverse_rregular];apply Hinv.
Defined.

End OMag_pr.

Module Ring_pr.
Export Ring Magma_pr.
Import minus1Trunc.

(*
LATER
Definition prering_sig : sigT (fun carr => sigT (fun _ : law carr => 
  law carr)) <~> prering.
Proof.
issig (fun g l1 l2 => BuildPrering g (BuildPreringC _ l1 l2))
 rigcarr (fun g => prering_plusV _ (rigC g)) (fun g => prering_multV _ (rigC g)).
Defined.
*)

Instance distrib_prop : forall {G : prering} {Hset : IsHSet G},
 IsHProp (Distributes G).
Proof.
intros. apply (@trunc_equiv' (sigT (fun _ : Ldistributes G => Rdistributes G))).
issig (BuildDistributes G) (@distrib_left G) (@distrib_right G).
apply @trunc_sigma;[|intro C;clear C];apply trunc_forall.
Defined.

Instance issemir_prop : forall {G : prering} {Hset : IsHSet G},
 IsHProp (IsSemiring G).
Proof.
intros.
apply (@trunc_equiv' (sigT (fun _ : IsCMonoid (prering_plus G) => 
  sigT (fun _ : IsMonoid (prering_mult G) => 
    Distributes G)))).
issig (BuildIsSemiring G) (@semiring_add G) (@semiring_mult G)
 (@semiring_distributes G).

repeat (apply @trunc_sigma;[|intro C;clear C]);apply _.
Defined.

Instance semiring_cancel : forall {G : semiring} (a : prering_plus G), Cancel a
 := fun _ _ => _.

Lemma rmult_0_l : forall {G : semiring}, 
forall x : G, ZeroV ° x = ZeroV.
Proof.
intros.
apply semiring_cancel with (ZeroV ° x).
path_via ((ZeroV + ZeroV) ° x).
symmetry. apply semiring_distributes.
path_via (ZeroV ° x).
apply (ap (fun g => g ° x)). apply Zero.
apply inverse;apply Zero.
Defined.

Lemma rmult_0_r : forall {G : semiring}, 
forall x : G, x ° ZeroV = ZeroV.
Proof.
intros.
apply semiring_cancel with (x ° ZeroV).
path_via (x ° (ZeroV + ZeroV)).
symmetry;apply semiring_distributes.
path_via (x ° ZeroV). apply ap;apply Zero.
apply inverse;apply Zero.
Defined.

Lemma rmult_inverse_right : forall G : semiring, forall x y : G,
 @IsInverse (semiring_add_cmonoid G) x y -> 
forall z,  @IsInverse (semiring_add_cmonoid G) (z°x) (z°y).
Proof.
intros ? ? ? H ?. apply linverse_inverse.
red. apply transport with gidV;[|apply gid].
path_via (z ° (x + y)).
path_via (z°ZeroV). symmetry; apply rmult_0_r.
apply ap. apply (id_unique (prering_plus G)); apply _.
apply semiring_distributes.
Defined.

Lemma rmult_inverse_left : forall G : semiring, forall x y : G,
 @IsInverse (semiring_add_cmonoid G) x y -> 
forall z,  @IsInverse (semiring_add_cmonoid G) (x°z) (y°z).
Proof.
intros ? ? ? H ?. apply linverse_inverse.
red. apply transport with gidV;[|apply gid]. symmetry; path_via ((x + y)°z).
symmetry;apply semiring_distributes.
path_via (ZeroV°z). apply (ap (fun g => g°z)).
apply (id_unique (prering_plus G));apply _.
apply rmult_0_l.
Defined.

Lemma ropp_rmult_left : forall G : ring, forall x y : G, 
roppV (x°y) = (roppV x)°y.
Proof.
intros. apply (@group_inverse_gopp (ring_group G)).
eapply rmult_inverse_left. apply _.
Defined.

Lemma ropp_rmult_right : forall G : ring, forall x y : G, 
roppV (x°y) = x°(roppV y).
Proof.
intros. apply (@group_inverse_gopp (ring_group G)).
eapply rmult_inverse_right. apply _.
Defined.

Definition isring_sig : forall G : prering, sigT (fun semir : IsSemiring G =>
 forall x : prering_plus G, Inverse x) <~> IsRing G.
Proof.
intros. issig (BuildIsRing G) (@ring_is_semir G) (@r_opp G).
Defined.

Instance isring_prop : forall {G : prering} {Hset : IsHSet G}, IsHProp (IsRing G).
Proof.
intros.
eapply trunc_equiv'. apply isring_sig.
apply @trunc_sigma. apply _.
intro. apply _.
Defined.

Definition easyIsRing (G : prering) {Hgr : IsGroup (prering_plus G)}
 {Hmon : IsMonoid (prering_mult G)} {Hdis : Distributes G} : IsRing G.
Proof.
apply BuildIsRing. apply BuildIsSemiring;apply _.
apply (@gopp' (prering_plus G) _).
Defined.

Lemma strictintegral_integral_pr : forall G {Hr: IsStrictIntegral G}, 
forall a : G, ~a = ZeroV -> forall b : G, ~ b = ZeroV -> ~ a°b = ZeroV.
Proof.
intros ? ? ? Ha ? Hb H.
apply Hr in H. revert H. apply minus1Trunc_rect_nondep.
intros [H|H];auto.
intros [].
Defined.

Lemma strictintegral_intdom : forall (G : ring) {Hr : IsStrictIntegral G},
~ @OneV G = ZeroV ->
  IsIntegralDomain G.
Proof.
intros. apply (BuildIsIntegralDomain _ _).
apply strictintegral_integral_pr. apply _.
assumption.
Defined.

Lemma intdom_partial_cancels_left : forall {G : ring} {Hr : IsStrictIntegral G}
 {Hset : IsHSet G}, forall a : G, ~ a = ZeroV ->
  @Lcancel (prering_mult G) a.
Proof.
intros ? ? ? ? H. red. fold (@rmult G). intros.
assert (a ° (b + (roppV c)) = ZeroV).
eapply concat.
apply (@semiring_distributes G _). 
pose (@semiring_cancel G). 
apply (@Right_cancel _ _ (c0 (a ° c))).
apply (@concat _ _ (a°b + (a° (roppV c) + a°c))).
simpl. symmetry. apply (@sg_assoc (prering_plus G) _).
eapply concat;[|symmetry;apply gid].
eapply concat;[|apply X].
eapply concat;[ apply ap | apply (@gid' (prering_plus G) _)].
eapply concat. symmetry.
apply semiring_distributes.
eapply concat;[apply ap | apply rmult_0_r].
apply (@id_unique (prering_plus G));apply _.
apply Hr in X0. revert X0.
apply minus1Trunc_rect_nondep;[|apply Hset].
intros [p | p].
destruct H;auto.
assert (Hcan : forall a : prering_plus G, Rcancel a). apply _.
apply (Hcan (ropp' c)).
eapply concat. apply p.
symmetry. apply id_unique;apply _.
Defined.

Lemma intdom_partial_cancels_right :forall  {G : ring} {Hr : IsStrictIntegral G}
 {Hset : IsHSet G}, forall a : G, ~ a = ZeroV ->
  @Rcancel (prering_mult G) a.
Proof.
intros ? ? ? ? ? ? ? X. apply intdom_partial_cancels_left with a;auto.
eapply concat;[|eapply concat;[apply X|]];apply (@sg_comm (prering_mult G) _).
Defined.

Lemma intdom_partial_cancels : forall  {G : ring} {Hr : IsStrictIntegral G}
 {Hset : IsHSet G}, forall a : G, ~ a = ZeroV ->
  @Cancel (prering_mult G) a.
Proof.
intros;split;
[apply intdom_partial_cancels_left | apply intdom_partial_cancels_right];
assumption.
Defined.

Lemma zero_inverse_prop : forall G : semiring,
 @Inverse (prering_mult G) (@ZeroV G) -> forall x : G, x = ZeroV.
Proof.
intros G Y x.
path_via (x ° ((inverse_val _ Y) ° ZeroV)).
apply inverse.
apply Y.
path_via (x ° ZeroV);[apply ap|];apply rmult_0_r.
Defined.


End Ring_pr.

Module RelatorInverse.
Export Related_pr OMag_pr.
Import minus1Trunc.

Definition inverseRel (r : Relation) := BuildRelation r (fun x y => rrel y x).

Notation "r ^-1" := (inverseRel r).

Lemma inverse_inverse : forall r, r ^-1 ^-1 = r.
Proof.
intros [T r];reflexivity.
Defined.

Instance inverse_refl : forall {r} {Hr : IsReflexive r}, IsReflexive (r ^-1)
 := fun _ => idmap.

Instance inverse_symm : forall {r} {Hs : IsSymmetric r}, IsSymmetric (r ^-1).
Proof.
intros ? ? ? ?;apply Hs.
Defined.

Instance inverse_trans : forall {r} {Ht : IsTransitive r}, IsTransitive (r ^-1).
Proof.
intros ? ? ? ? ? H H';apply Ht with y;assumption.
Defined.

Definition inverse_P : forall P : Relation -> Prop, 
(forall r, P r -> P (inverseRel r)) -> forall r, P (r ^-1) -> P r.
Proof.
intros ? H [r rel] Hr.
set (R := {| relcarr := r; rel_r := rel |}) in *.
change (P (inverseRel (inverseRel R))). apply H. assumption.
Defined.

Instance inverse_equivalence : forall {r} {He : IsEquivalence r},
 IsEquivalence (r ^-1).
Proof.
intros;split;apply _.
Defined.

Instance inverse_is_prop : forall {r} {Hp : RelationProp r}, RelationProp (r ^-1)
 := fun _ H x y => H y x.

Instance inverse_is_mere : forall {r} {Hm : IsMereRelator r},
 IsMereRelator (r ^-1).
Proof.
intros;split. change (IsHSet r). apply _. apply _.
Defined.

Instance inverse_antisymm : forall {r} {Ha : IsAntisymmetric r},
 IsAntisymmetric (r ^-1).
Proof.
intros ? ? ? ? H H'. apply Ha;assumption.
Defined.

Instance inverse_irrefl : forall {r} {Hi : IsIrreflexive r},
 IsIrreflexive (r ^-1) := fun _ => idmap.

Instance inverse_poset : forall {r} {Hp : IsPoset r}, IsPoset (r ^-1).
Proof.
intros;split;apply _.
Defined.

Instance inverse_cotrans :  forall {r} {Hs : IsCotransitive r},
 IsCotransitive (r ^-1).
Proof.
intros;intros ? ? H ?.
eapply minus1Trunc_rect_nondep;[|apply minus1Trunc_is_prop|apply Hs;apply H].
intros [H'|H'];apply min1;[right|left];apply H'.
Defined.

Instance inverse_apart : forall {r} {Ha : IsApartness r}, IsApartness (r ^-1).
Proof.
intros;split;try apply _.
intros ? ? H;apply Ha. intro H'. apply H. apply Ha. assumption.
Defined.

Instance lower_inverse_upper : forall {r P m} {H : IsLower r P m},
IsUpper (r ^-1) P m.
Proof.
intros. apply H.
Defined.

Instance upper_inverse_lower : forall {r P m} {H : IsUpper r P m},
IsLower (r ^-1) P m.
Proof.
intros. apply H.
Defined.

Definition inverse_lower_upper : forall {r : Relation}
{P : r->Type} {m:r} {H : IsLower (r ^-1) P m},
IsUpper r P m.
Proof.
intros;apply H.
Defined.

Definition inverse_upper_lower : forall {r : Relation}
{P : r->Type} {m:r} {H : IsUpper (r ^-1) P m},
IsLower r P m.
Proof.
intros;apply H.
Defined.

Lemma inverse_upper_rw : IsUpper = fun r P m => IsLower (inverseRel r) P m.
Proof.
reflexivity.
Defined.

Lemma inverse_lower_rw : IsLower = fun r P m => IsUpper (inverseRel r) P m.
Proof.
reflexivity.
Defined.

Definition ismax_sig_rw := fun r P m => path_universe (ismax_sig r P m).
Definition ismin_sig_rw := fun r P m => path_universe (ismin_sig r P m).

Lemma inverse_ismax_iff : forall r P m, IsMaximum r P m <->
 IsMinimum (r ^-1) P m.
Proof.
intros;split;intros;split;apply X.
Defined.

Lemma inverse_ismin_iff : forall r P m, IsMinimum r P m <->
 IsMaximum (r ^-1) P m.
Proof.
intros;split;intros;split;apply X.
Defined.

Lemma inverse_ismax_rw : IsMaximum = fun r => IsMinimum (r ^-1).
Proof.
apply funext_axiom;intro r.
apply funext_axiom;intro P.
apply funext_axiom;intro m.
eapply concat. symmetry. apply ismax_sig_rw.
eapply concat;[| apply ismin_sig_rw].
reflexivity.
Defined.

Lemma inverse_ismin_rw : IsMinimum = fun r => IsMaximum (r ^-1).
Proof.
apply funext_axiom;intro r.
apply funext_axiom;intro P.
apply funext_axiom;intro m.
eapply concat. symmetry. apply ismin_sig_rw.
eapply concat;[| apply ismax_sig_rw].
reflexivity.
Defined.

Lemma inverse_isinf_iff : forall r P m, IsInfimum r P m <->
 IsSupremum (r ^-1) P m.
Proof.
intros. apply inverse_ismax_iff.
Defined.

Lemma inverse_issup_iff : forall r P m, IsSupremum r P m <->
 IsInfimum (r ^-1) P m.
Proof.
intros. apply inverse_ismin_iff.
Defined.

Lemma inverse_isinf_rw : IsInfimum = fun r => IsSupremum (r^-1).
Proof.
unfold IsInfimum;unfold IsSupremum.
change ((fun (r : Relation) (P : r -> Type) (m : r) =>
 IsMaximum r (IsLower r P) m)  =
(fun (r : Relation) (P : r -> Type) (m : r) => IsMinimum r ^-1 (IsLower r P) m)).
apply (@ap _ _ (fun IS : forall r : Relation, (r -> Type) -> r -> Type
  => fun r P m => IS r (IsLower r P) m) IsMaximum (fun r => IsMinimum r^-1)).
apply inverse_ismax_rw.
Defined.

Lemma inverse_issup_rw : IsSupremum = fun r => IsInfimum (r^-1).
Proof.
change ((fun (r : Relation) (P : r -> Type) (m : r) =>
 IsMinimum r (IsUpper r P) m)  =
(fun (r : Relation) (P : r -> Type) (m : r) => IsMaximum r ^-1 (IsUpper r P) m)).
apply (@ap _ _ (fun IS : forall r : Relation, (r -> Type) -> r -> Type
  => fun r P m => IS r (IsUpper r P) m) IsMinimum (fun r => IsMaximum r^-1)).
apply inverse_ismin_rw.
Defined.


End RelatorInverse.

Module Lattice_pr.
Export Lattice Related_pr RelatorInverse.
Import minus1Trunc.

Section Meet_to_order.

Context {r : LR_sig} {Hs : IsHSet r} {Hp : RelationProp r}
{Hr : IsMeetSemiLattice r}.


Instance semilattice_meet_refl : IsReflexive r.
Proof.
intros x.
apply Hr. apply Hr.
Defined.

Instance semilattice_meet_antisymm : IsAntisymmetric r.
Proof.
intros x y H H'.
apply Hr in H;apply Hr in H'.
path_via (gop x y). path_via (gop y x).
apply commutative.
Defined.

Instance semilattice_meet_trans : IsTransitive r.
Proof.
intros x y z H H'.
apply Hr in H;apply Hr in H';apply Hr.
path_via (gop (gop x y) z). apply (ap (fun g => gop g z)).
apply inverse;assumption.
path_via (gop x (gop y z)). apply inverse;apply associative.
path_via (gop x y). apply ap. assumption.
Defined.

Instance semilattice_meet_poset : IsPoset r.
Proof.
split;apply _.
Defined.

Instance meet_is_inf2 : forall {x y : r}, IsInfimum r (doubleton x y) (gop x y).
Proof.
intros. split.
intros z H.
apply Hr. path_via (gop (gop z x) y). apply associative.
path_via (gop z y);[apply (ap (fun g => gop g y))|];apply Hr;apply H;
apply min1;auto.
intros z H.
eapply minus1Trunc_rect_nondep;[|apply Hp|apply H].
clear H. intros [[]|[]];apply Hr.
- path_via (gop (gop x x) y).
  path_via (gop x (gop y x)). symmetry;apply associative.
  path_via (gop x (gop x y)). apply ap;apply commutative.
  apply associative.
  apply (ap (fun g => gop g y)).
  apply isidempotent.
- path_via (gop x (gop y y)).
  symmetry;apply associative.
  apply ap.
  apply isidempotent.
Defined.

End Meet_to_order.

Section Order_to_meet.

Context {r : LR_sig} {Hset : IsHSet r} {Hpr : RelationProp r} {Hpo : IsPoset r}
{Hmeet : forall a b : r, IsInfimum r (doubleton a b) (gop a b)}.

Instance meet_comm : Commutative r.
Proof.
intros x y.
eapply infimum_unicity.
apply Hpo.
apply Hmeet.
change ((fun P => IsInfimum r P (gop y x)) (doubleton x y)).
eapply transport;[|apply Hmeet]. apply doubleton_comm.
Defined.

Instance meet_assoc : Associative r.
Proof.
intros x y z.
eapply infimum_unicity. apply _.
apply Hmeet.
split.
- intros a Ha.
  apply Hmeet. intros b.
  apply minus1Trunc_rect_nondep;[|apply Hpr].
  intros [[]|[]];clear b.
  apply Hmeet. intros b.
  apply minus1Trunc_rect_nondep;[|apply Hpr].
  intros [[]|[]];clear b.
  apply Ha;apply min1. auto.
  apply order_trans with (gop y z).
  apply Ha. apply min1;auto.
  apply Hmeet. apply min1;auto.
  apply order_trans with (gop y z).
  apply Ha. apply min1;auto.
  apply Hmeet. apply min1;auto.
- intros a. apply minus1Trunc_rect_nondep;[|apply Hpr].
  intros [[]|[]];clear a.
  apply order_trans with (gop x y).
  apply (Hmeet (gop x y) z). apply min1;auto.
  apply Hmeet. apply min1;auto.
  apply Hmeet. intros a.
  apply minus1Trunc_rect_nondep;[|apply Hpr].
  intros [[]|[]];clear a.
  apply order_trans with (gop x y).
  apply (Hmeet (gop x y) z). apply min1;auto.
  apply Hmeet. apply min1;auto.
  apply Hmeet. apply min1;auto.
Defined.

Instance meet_sg : IsSemigroup r := BuildIsSemigroup _ _ _.

Instance meet_idempotent : IsIdempotent r.
Proof.
intros x.
eapply infimum_unicity. apply _.
apply Hmeet.
apply _. (* by singleton_min *)
Defined.

Lemma meet_gop_eq_pr : forall x y z : r, IsInfimum r (doubleton x y) z -> 
gop x y = z.
Proof.
intros ? ? ?. apply infimum_unicity;apply _.
Defined.

Instance meet_pr : IsLatticeMeetR r.
Proof.
intros x y.
split. intros.
eapply meet_gop_eq_pr.
apply minimum_is_infimum. split.
intros a. apply minus1Trunc_rect_nondep;[|apply Hpr].
intros [[]|[]]. apply Hpo. assumption.
apply min1;auto.
intros []. apply Hmeet. apply min1;auto.
Defined.

Instance meet_mag_pr : IsLatticeMag r := BuildIsLatticeMag _ _ _.

Instance meet_semilattice : IsMeetSemiLattice r := BuildIsMeetSemiLattice _ _ _.

End Order_to_meet.

Definition semil_inverse (r : LR_sig) : LR_sig := 
BuildLR_sig r (BuildLR_Class _ (@gop r) 
  (fun x y : r => rrel y x)).

Definition semil_inverse_idem : forall r, semil_inverse (semil_inverse r) = r.
Proof.
intros [r [op rel]];reflexivity.
Defined.

Instance semimeet_inverse : forall {r} {Hr: IsMeetSemiLattice r},
IsJoinSemiLattice (semil_inverse r).
Proof.
intros;split.
change (IsLatticeMag r). apply _.
intros ? ?. apply Hr.
Defined.

Definition inverse_semimeet : forall {r}
 {Hr : IsJoinSemiLattice (semil_inverse r)},
IsMeetSemiLattice r.
Proof.
intros;split.
change (IsLatticeMag (semil_inverse r)). apply _.
intros ? ?;apply Hr.
Defined.

Instance semijoin_inverse : forall {r} {Hr: IsJoinSemiLattice r},
IsMeetSemiLattice (semil_inverse r).
Proof.
intros. apply @inverse_semimeet.
split. apply Hr.
apply Hr.
Defined.

Definition inverse_semijoin : forall {r} 
{Hr : IsMeetSemiLattice (semil_inverse r)},
IsJoinSemiLattice r.
Proof.
intros. apply @semimeet_inverse in Hr.
split;apply Hr.
Defined.

Instance semilattice_join_poset : forall {r} {Hr : IsJoinSemiLattice r},
 IsPoset r.
Proof.
intros.
apply inverse_P. apply _.
change (IsPoset (semil_inverse r)).
apply semilattice_meet_poset.
Defined.

Instance join_is_sup2 : forall {r : LR_sig}
{Hs : IsHSet r} {Hp : RelationProp r} {Hr : IsJoinSemiLattice r},
forall {x y : r}, IsSupremum r (doubleton x y) (gop x y).
Proof.
intros ? ? ? ?.
intros.
assert (Hr' : IsMeetSemiLattice (semil_inverse r)). apply _.
apply inverse_issup_iff.
apply (@meet_is_inf2 _ _ Hr').
Defined.

Section Order_to_join.

Context {r : LR_sig} {Hset : IsHSet r} {Hpr : RelationProp r} {Hpo : IsPoset r}
{Hjoin : forall a b : r, IsSupremum r (doubleton a b) (gop a b)}.

Lemma join_gop_eq_pr : forall x y z : r, IsSupremum r (doubleton x y) z -> 
gop x y = z.
Proof.
intros ? ? ?. apply supremum_unicity;apply _.
Defined.

Instance join_semilattice : IsJoinSemiLattice r.
Proof.
apply @inverse_semijoin.
apply @meet_semilattice. apply _. apply _.
intros. apply inverse_issup_iff. apply _.
Defined.

End Order_to_join.



End Lattice_pr.


Module Field_pr.
Export Field Ring_pr Related_pr.
Import minus1Trunc.

Lemma field_intdom_pr : forall {F} {Hf : IsField F}, 
forall a : F, ~ a = ZeroV -> forall b : F, ~ b = ZeroV -> ~ (a ° b) = ZeroV.
Proof.
intros ? ? ? Ha ? Hb H.
assert (Ha' : ~ ~ (rrel a ZeroV)).
  intro H'. apply Ha. apply apart_tight; assumption.

destruct Ha'. intro Ha'.
apply Hb.
apply (@inverse_cancel (prering_mult F) _ a).
apply finv. assumption.
eapply concat. apply H.
apply inverse. apply rmult_0_r.
Defined.

Instance field_is_intdom : forall {F} {Hf : IsField F}, IsIntegralDomain F.
Proof.
intros. apply (BuildIsIntegralDomain _ _).
apply field_intdom_pr.
red. apply irrefl_neq. apply field_neq.
Defined.

Instance field_left_cancel : forall {F} {Hf : IsField F}, 
forall a : F, ~ a = ZeroV -> @Lcancel (prering_mult F) a.
Proof.
intros ? ? ? Ha.
intros b c H.
apply apart_tight. intro H'.
assert (Ha' : ~ ~ (rrel a ZeroV)). intro Ha'.
apply Ha. apply apart_tight. assumption.
destruct Ha'.
intros Ha'.
eapply (@irrefl_neq F _). apply H'.
eapply (@inverse_cancel (prering_mult F) _). apply finv. apply Ha'.
assumption.
Defined.

Instance field_cancel : forall {F} {Hf : IsField F}, 
forall a : F, ~ a = ZeroV -> @Cancel (prering_mult F) a.
Proof.
intros. apply left_cancel_cancel.
apply field_left_cancel. assumption.
Defined.

Lemma field_inverse_apart : forall {F} {Hf : IsField F}, 
forall (a b : F), @IsInverse (prering_mult F) a b -> rrel b ZeroV.
Proof.
intros. apply field_inv_back. exists a. apply inverse_symm. assumption.
Defined.


Section Field_of_DecField.

Variable F : prefield.

Hypothesis Hneq : forall x y : F, x<>y <-> neq x y.

Context {Hdec : decidable_paths F} {Hfield : IsDecField F}.

Global Instance decfield_is_field : IsField F.
Proof.
refine (BuildIsField _ _ decfield_is_ring _ _ _ _ _).
- apply neq_apart. assumption.
  assumption.
- intros ? ? ? ? H.
  apply min1. destruct (Hdec x x');[destruct (Hdec y y')|].
  apply Hneq in H. destruct H;apply ap11;[apply ap|];assumption.
  right;apply Hneq;assumption.
  left ;apply Hneq;assumption.
- intros ? ? ? ? H.
  apply min1. destruct (Hdec x x');[destruct (Hdec y y')|].
  apply Hneq in H. destruct H;apply ap11;[apply ap|];assumption.
  right;apply Hneq;assumption.
  left ;apply Hneq;assumption.
- apply Hneq. apply decfield_neq.
- intros. exists (decInv x). apply decInv_inverse. apply Hneq;assumption.
- intros x X. apply Hneq;intro H.
  apply inverse in H;destruct H.
  apply decfield_neq.
  apply zero_inverse_prop. assumption.
Defined.

End Field_of_DecField.

End Field_pr.

