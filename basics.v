Require Import HoTT FunextAxiom UnivalenceAxiom.
Require Import unique_choice.
Require Export structures.

Instance neq_is_prop : forall {T}, Relation.RelationProp (@neq T).
Proof.
red;intros. apply trunc_forall.
Defined.

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

Instance assoc_prop : forall {G} {L : Gop G} {Hset : IsHSet G},
 IsHProp (Associative L).
Proof.
intros.
apply trunc_forall.
Defined.

Instance comm_prop : forall {G} {L : Gop G} {Hset : IsHSet G},
 IsHProp (Commutative L).
Proof.
intros.
apply trunc_forall.
Defined.

Instance issg_prop : forall {G} {L : Gop G} {Hset : IsHSet G},
 IsHProp (IsSemigroup L).
Proof.
intros G L Hset.
apply (@trunc_equiv' (sigT (fun _ : Associative L => Commutative L))).
issig (BuildIsSemigroup L) (@sg_assoc G L) (@sg_comm G L).
apply @trunc_sigma. apply _. intro. apply _.
Defined.

Lemma id_unique : forall {G} (L : Gop G), forall e : G, 
IsId L e -> forall e': G, IsId L e' -> e = e'.
Proof.
intros.
apply (@concat _ _ (gop e e')).
 apply inverse;apply right_id. apply _.
 apply left_id. apply _.
Defined.

Instance id_prop : forall {G} {L : Gop G} {Hset : IsHSet G} e,
 IsHProp (IsId L e).
Proof.
intros.
apply (@trunc_equiv' (sigT (fun _ : Left_id L e => Right_id L e))).
issig (BuildIsId L e) (@id_is_left G L e) (@id_is_right G L e).

apply @trunc_sigma.
apply trunc_forall.
intros;apply trunc_forall.
Defined.

Lemma left_id_id : forall {G} {L : Gop G} {Hg : Commutative L} (e : G),
 Left_id L e -> IsId L e.
Proof.
intros ? ? ? ? X. split;auto.
intro.
eapply concat. apply commutative. apply _. apply X.
Defined.


Definition identity_sig : forall {G} (L : Gop G), sigT (IsId L) <~> Identity L.
Proof.
intros; issig (BuildIdentity L) (@g_id G L) (@g_idP G L).
Defined.

Instance gidPop : forall {G} {L : Gop G} {Hset : IsHSet G},
 IsHProp (Identity L).
Proof.
intros G L Hset. eapply trunc_equiv'. apply identity_sig.
apply hprop_allpath. intros [x Hx] [y Hy].
apply path_sigma with (id_unique _ _ _ _ _).
apply id_prop.
Defined.

Definition ismonoid_sig : forall {G} (L : Gop G), sigT (fun _ : IsSemigroup L =>
Identity L) <~> IsMonoid L.
Proof.
intros;issig (BuildIsMonoid L) (@monoid_is_sg G L) (@monoid_id G L).
Defined.

Instance ismonoid_prop : forall {G} {L : Gop G} {Hset : IsHSet G},
 IsHProp (IsMonoid L).
Proof.
intros.
eapply trunc_equiv'. apply ismonoid_sig.
apply @trunc_sigma. apply _.
intro. apply _.
Defined.

Lemma left_cancel_cancel : forall {G} {L : Gop G} {Hcomm : Commutative L},
forall a : G, Lcancel L a -> Cancel L a.
Proof.
intros ? ? ? ? X. split;auto.
red;intros ? ? X0.
red in X. apply X.
eapply concat. apply Hcomm. eapply concat. apply X0. apply Hcomm.
Defined.

Instance cancelling_prop : forall {G} {L : Gop G} {Hset : IsHSet G} a,
 IsHProp (Cancel L a).
Proof.
intros.
apply (@trunc_equiv' (sigT (fun _ : Lcancel L a => Rcancel L a))).
issig (BuildCancel _ a) (@Left_cancel _ _ a) (@Right_cancel _ _ a).
apply @trunc_sigma;[|intro C;clear C];apply trunc_forall.
Defined.

Instance iscmono_prop : forall {G} {L : Gop G} {Hset : IsHSet G},
 IsHProp (IsCMonoid L).
Proof.
intros.
apply (@trunc_equiv' (sigT (fun _ : IsMonoid L => forall a : G, Cancel L a))).
issig (BuildIsCMonoid L) (@cmonoid_is_monoid G L) (@cmonoid_cancel G L).
apply trunc_sigma.
Defined.

Lemma linverse_inverse : forall {G} {L : Gop G} {Hg : Commutative L} (x y : G), 
Linverse L x y -> IsInverse L x y.
Proof.
intros;split;auto.
red. apply transport with (gop x y). apply Hg.
apply _.
Defined.

Lemma linverse_eq_gid : forall {G} {L : Gop G} {Hg : IsMonoid L} 
(x y : G) {Hinv : Linverse L x y},
gop x y = gidV.
Proof.
intros. eapply id_unique;apply _.
Defined.

Lemma rinverse_eq_gid : forall {G} {L : Gop G} {Hg : IsMonoid L} 
(x y : G) {Hinv : Rinverse L x y},
gop y x = gidV.
Proof.
intros;eapply id_unique;apply _.
Defined.

Lemma isinverse_sig : forall {G} {L : Gop G} x y,
 sigT (fun _ : Linverse L x y => Rinverse L x y) <~> IsInverse L x y.
Proof.
intros.
issig (BuildIsInverse L x y) (@inverse_left G L x y) (@inverse_right G L x y).
Defined.

Instance isinverse_prop : forall {G} {L : Gop G} {Hset : IsHSet G} x y,
 IsHProp (IsInverse L x y).
Proof.
intros.
eapply trunc_equiv'. apply isinverse_sig.
apply @trunc_sigma;intros;apply id_prop.
Defined.

Instance inverse_symm : forall {G} (L : Gop G), Symmetric (IsInverse L).
Proof.
red. intros ? ? ? ? [? ?]. split;red;apply _.
Defined.

Lemma inverse_symm_rw : @IsInverse  = fun G L x y => IsInverse L y x.
Proof.
apply funext_axiom. intro G.
apply funext_axiom. intro L.
apply funext_axiom. intro x. apply funext_axiom;intro y.
apply univalence_axiom.
eapply transitive_equiv;[|apply isinverse_sig].
apply symmetric_equiv.
issig (fun H H' => BuildIsInverse L x y H' H)
 (@inverse_right G L x y) (@inverse_left G L x y).
Defined.

Instance rinverse_lcancel : forall {G} {L : Gop G} {Hassoc : Associative L},
 forall a b : G, Rinverse L a b -> Lcancel L a.
Proof.
intros ? ? ? ? ? H.
red. intros x y ?.
path_via (gop (gop b a) x). apply inverse;apply H.
path_via (gop b (gop a x)).
path_via (gop b (gop a y)). apply ap;assumption.
path_via (gop (gop b a) y).
apply H.
Defined.

Instance linverse_rcancel : forall {G} {L : Gop G} {Hassoc : Associative L},
 forall a b : G, Linverse L a b -> Rcancel L a.
Proof.
intros ? ? ? ? ? H.
red. intros x y ?.
path_via (gop x (gop a b)). apply inverse;apply H.
path_via (gop (gop x a) b).
path_via (gop (gop y a) b). apply (ap (fun g => gop g b));assumption.
path_via (gop y (gop a b)).
apply H.
Defined.

Instance isinverse_cancel : forall {G} {L : Gop G} {Hassoc : Associative L},
 forall a b : G, IsInverse L a b -> Cancel L a.
Proof.
intros;split;apply _.
Defined.

Instance inverse_cancel : forall {G} {L : Gop G} {Hassoc : Associative L}
 (a : G), Inverse L a -> Cancel L a.
Proof.
intros ? ? ? ? [b H]. apply isinverse_cancel with b.
assumption.
Defined.

Definition easyIsGroup {G} (L : Gop G) {Hg : IsMonoid L}
 (gopp : forall x : G, Inverse L x) := 
BuildIsGroup L (BuildIsCMonoid L Hg
 (fun a => inverse_cancel a (gopp a))) gopp.

Lemma inverse_unicity : forall {G} {L : Gop G} {Hassoc : Associative L},
 forall x : G,  atmost1P (IsInverse L x).
Proof.
intros ? ? ? ? y y' X X0. apply inverse_cancel with x. exists y;exact X.
eapply id_unique;apply _.
Defined.

Definition inverse_sig : forall {G} {L : Gop G} (x : G), 
sigT (IsInverse L x) <~> Inverse L x.
Proof.
intros.
issig (BuildInverse L x) (@inverse_val G L x) (@inverse_pr G L x).
Defined.

Instance inverse_prop : forall {G} {L : Gop G} {Hset : IsHSet G}
 {Ha : Associative L} (x : G), IsHProp (Inverse L x).
Proof.
intros.
eapply trunc_equiv'. apply inverse_sig.
apply hprop_allpath. intros [y H] [y' Hy'].
apply path_sigma with (inverse_unicity _ _ _ _ _). apply isinverse_prop.
Defined.

Lemma group_inverse_gopp : forall {G} {L : Gop G} {Hg : IsGroup L},
 forall x y : G, IsInverse L x y -> (goppV x) = y.
Proof.
intros. 
apply (@inverse_unicity G L _) with x.
 apply gopp.
 assumption.
Defined.

Lemma gopp_gopp : forall {G} {L : Gop G} {Hg : IsGroup L} (x : G),
 (goppV (goppV x)) = x.
Proof.
intros. apply group_inverse_gopp.
apply inverse_symm. apply gopp.
Defined.

Instance gid_isinverse : forall {G} {L : Gop G} {Hg : IsMonoid L},
 IsInverse L gidV gidV.
Proof.
intros.
split;red;(apply transport with gidV;[symmetry;apply gid|]);try apply _.
Defined.

Lemma gopp_gid : forall {G} {L : Gop G} {Hg : IsGroup L},
 (goppV gidV) = gidV.
Proof.
intros. apply group_inverse_gopp. apply _.
Defined.

Lemma linverse_gop : forall {G} {L : Gop G} {Hassoc : Associative L},
forall x x' : G, Linverse L x x' ->
forall y y' : G, Linverse L y y' ->
  Linverse L (gop x y) (gop y' x').
Proof.
intros ? ? ? ? ? Hx ? ? Hy.
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

Lemma rinverse_gop : forall {G} {L : Gop G} {Hassoc : Associative L},
forall x x' : G, Rinverse L x x' ->
forall y y' : G, Rinverse L y y' ->
  Rinverse L (gop x y) (gop y' x').
Proof.
intros ? ? ?.
change (forall x x' : G, Linverse L x' x -> forall y y' : G, Linverse L y' y ->
  Linverse L (gop y' x') (gop x y)).
intros;apply linverse_gop;assumption.
Defined.

Lemma isinverse_gop : forall {G} {L : Gop G} {Hassoc : Associative L},
forall x x' : G, IsInverse L x x' ->
forall y y' : G, IsInverse L y y' ->
  IsInverse L (gop x y) (gop y' x').
Proof.
intros;split;[apply linverse_gop|apply rinverse_gop];apply _.
Defined.

Lemma gopp_gop : forall {G} {L : Gop G} {Hg : IsGroup L}, forall x y : G,
 (goppV (gop x y)) = (gop (goppV y) (goppV x)).
Proof.
intros. apply group_inverse_gopp.
apply isinverse_gop;apply _.
Defined.

Lemma gopp_cop_comm : forall {G} {L : Gop G} {Hg : IsGroup L}, forall x y : G,
 (goppV (gop x y)) = (gop (goppV x) (goppV y)).
Proof.
intros;path_via (gop (goppV y) (goppV x)).
apply gopp_gop. apply commutative. apply _.
Defined.

Instance gopp_prop : forall {G} {L : Gop G} {Hg : Associative L}
 {Hset : IsHSet G}, IsHProp (forall x : G, Inverse L x).
Proof.
intros.
apply trunc_forall.
Defined.

Definition isgroup_sig : forall {G} {L : Gop G}, 
sigT (fun Hmon : IsCMonoid L => forall x : G, Inverse L x) <~> IsGroup L.
Proof.
intros.
issig (BuildIsGroup L) (@group_is_cmonoid G L) (@gopp G L).
Defined.

Instance isgroup_prop : forall {G} {L : Gop G} {Hset : IsHSet G},
 IsHProp (IsGroup L).
Proof.
intros;eapply trunc_equiv'. apply isgroup_sig.
apply @trunc_sigma. apply _.
intro. apply _.
Defined.

End Magma_pr.

Module Relation_pr.
Export Relation.
Import minus1Trunc.
Generalizable Variable T.

Instance trans_prop : forall {T} {r : Rel T}
 {Hprop : RelationProp r}, IsHProp (Transitive r).
Proof.
intros.
apply trunc_forall.
Defined.

Instance refl_prop : forall {T} {r : Rel T}
 {Hprop : RelationProp r}, IsHProp (Reflexive r).
Proof.
intros.
apply trunc_forall.
Defined.

Instance symm_prop : forall {T} {r : Rel T}
 {Hprop : RelationProp r}, IsHProp (Symmetric r).
Proof.
intros.
apply trunc_forall.
Defined.

Definition IsEquivalence_sig : forall {T} {r : Rel T},
sigT (fun _ : Reflexive r => sigT (fun _ : Symmetric r => Transitive r))
<~> Equivalence r.
Proof.
intros ? r. issig (BuildEquivalence _ r) (@equivalence_refl _ r)
 (@equivalence_symm _ r) (@equivalence_trans _ r).
Defined.

Instance isequivalence_prop : forall {T} {r : Rel T}
 {Hprop : RelationProp r}, IsHProp (Equivalence r).
Proof.
intros.
eapply trunc_equiv'.
apply IsEquivalence_sig.
apply @trunc_sigma. apply _.
intro. apply @trunc_sigma. apply _.
intro;apply _.
Defined.

Lemma irrefl_neq : forall {T} {r : Rel T} {Hr : Irreflexive r},
  forall x y : T, rrel x y -> neq x y.
Proof.
intros ? ? ? ? ? ?. intros H. destruct H. apply Hr with x. assumption.
Defined.

Instance antisymm_prop : forall {T} {r : Leq T} {Hset : IsHSet T},
 IsHProp (Antisymmetric r).
Proof.
intros.
apply trunc_forall.
Defined.

Instance irrefl_prop : forall {T} {r : Rel T}, IsHProp (Irreflexive r).
Proof.
intros.
apply trunc_forall.
Defined.

Definition poset_sig : forall {T} {r : Leq T}, sigT (fun _ : Transitive r => 
sigT (fun _ : Reflexive r => Antisymmetric r)) <~> Poset r.
Proof.
intros;
issig (BuildPoset _ r) (@order_trans _ r) (@order_refl _ r)
 (@order_antisymm _ r).
Defined.

Instance poset_prop : forall {T} {r : Leq T} {Hset : IsHSet T}
 {Hprop : RelationProp r}, IsHProp (Poset r).
Proof.
intros.
eapply trunc_equiv'.
apply poset_sig.
apply @trunc_sigma. apply trans_prop.
intro. apply @trunc_sigma. apply refl_prop.
intro;apply _.
Defined.

Instance cotrans_prop : forall {T} {r : Rel T}, IsHProp (Cotransitive r).
Proof.
intros.
apply trunc_forall.
Defined.

Definition apart_sig : forall {T} {r : Apart T}, sigT (fun _ : Irreflexive r =>
sigT (fun _ : Symmetric r => sigT (fun _ : Cotransitive r => 
 forall x y : T, ~ x <> y -> x=y))) <~> Apartness r.
Proof.
intros.
issig (BuildApartness _ r) (@apart_irrefl _ r) (@apart_symm _ r)
 (@apart_cotrans _ r) (@apart_tight _ r).
Defined.

Instance apart_prop : forall {T} {r : Apart T} {Hset : IsHSet T}
 {Hpr : RelationProp r}, IsHProp (Apartness r).
Proof.
intros;eapply trunc_equiv'.
apply apart_sig.
apply @trunc_sigma. apply irrefl_prop.
intro. apply @trunc_sigma. apply symm_prop.
intro. apply @trunc_sigma. apply cotrans_prop.
intro. apply trunc_forall.
Defined.

Lemma neq_not_not_apart : forall {T} {r : Apart T} {Ha : Apartness r},
 forall x y : T, ~x=y -> ~ ~ x <> y.
Proof.
intros ? ? ? ? ? H ?.
apply H;apply apart_tight. assumption.
Defined.

Lemma apart_prove_eq : forall `{r : Apart T} {Ha : Apartness r},
forall a b x y : T, (x <> y -> a=b) -> (~x=y -> a=b).
Proof.
intros ? ? ? ? ? ? ? H H'.
apply apart_tight. intro H0.
assert (Hx : ~ ~ x <> y).
apply neq_not_not_apart. assumption.
apply Hx;clear Hx;intro Hx.
apply irrefl_neq in H0. apply H0. auto.
Defined.

Instance islinear_prop : forall `{r : Leq T}, IsHProp (Linear r).
Proof.
intros.
apply trunc_forall.
Defined.

Instance constrlinear_linear : forall `{r : Leq T},
 ConstrLinear r -> Linear r.
Proof.
red;intros;apply min1;auto.
Defined.

Lemma dec_linear_constrlinear : forall `(r : Leq T) {Hdec : Decidable r}
 {Hlin : Linear r}, ConstrLinear r.
Proof.
red;intros.
destruct (Hdec x y). left;assumption.
destruct (Hdec y x). right;assumption.
apply Empty_rect. pose (H := Hlin x y). clearbody H;revert H.
apply minus1Trunc_rect_nondep;[|intros []].
intros [H|H];auto.
Defined.

Instance constrtotal_total : forall `{r : Leq T},
 ConstrTotalOrder r -> TotalOrder r.
Proof.
intros. constructor; apply _.
Defined.

Definition strictorder_sig : forall `{r : Lt T},
 sigT (fun _ : Irreflexive r => Transitive r) <~> StrictOrder r.
Proof.
intros. issig (BuildStrictOrder T r) (@strictorder_irrefl T r)
  (@strictorder_trans T r).
Defined.

Instance strictorder_prop : forall `{r : Lt T}
 {Hp : RelationProp r}, IsHProp (StrictOrder r).
Proof.
intros. eapply trunc_equiv'.
apply strictorder_sig.
apply @trunc_sigma. unfold Irreflexive. apply _. intros;apply trans_prop.
Defined.

Lemma strict_poset_antisymm : forall `(r : Lt T)
 {Hstrict : StrictOrder r}, forall x y : T, x < y /\ y < x -> Empty.
Proof.
intros ? ? ? ? ? [? ?]. destruct Hstrict as [Hirr Htrans].
apply Hirr with x;eapply Htrans;eauto.
Defined.

Instance strict_poset_disjunct_prop : forall `(r : Lt T)
 {Hp : RelationProp r} {Hstrict : StrictOrder r},
  forall x y : T, IsHProp (x < y \/ y < x).
Proof.
intros. apply hprop_allpath.
intros [Hx|Hx] [Hy|Hy];try (apply ap;apply Hp).
destruct (strict_poset_antisymm _ _ _ (Hx, Hy)).
destruct (strict_poset_antisymm _ _ _ (Hx, Hy)).
Defined.

Lemma neq_irrefl : forall `(r : Apart T), (forall x y : T, x <> y -> ~ x=y) ->
Irreflexive r.
Proof.
intros ? ? H0;intros x H.
apply H0 in H. apply H;reflexivity.
Defined.

Lemma neq_symm : forall `(r : Apart T), (forall x y : T, x <> y <-> ~x=y) -> 
Symmetric r.
Proof.
intros ? ? H ? ? H'.
apply H. apply H in H'. intro H0;apply H';symmetry;assumption.
Defined.

Lemma neq_cotrans : forall `(r : Apart T), decidable_paths T ->
(forall x y : T, x <> y <-> ~x=y) -> Cotransitive r.
Proof.
intros ? ? Hdec Hneq x y H z.
apply min1.
destruct (Hdec x z) as [[]|H']. right. assumption.
left;auto;apply Hneq;auto.
Defined.

Lemma neq_apart : forall `(r : Apart T), decidable_paths T ->
(forall x y : T, x <> y <-> ~x=y) -> Apartness r.
Proof.
intros ? ? Hdec Hneq;split.
apply neq_irrefl;intros;apply Hneq;assumption.
apply neq_symm;assumption.
apply neq_cotrans;assumption.
intros ? ? H.
destruct (Hdec x y) as [?|n]. assumption.
apply Hneq in n. destruct H;assumption.
Defined.


Section PseudoOrder.

Context T {r : ApartLt T}
 {Hpr : RelationProp (<)} {Hpo : PseudoOrder r}.

Lemma apart_total_lt (x y : T) : x <> y -> x < y \/ y < x.
Proof.
apply apart_iff_total_lt.
Defined.

Lemma pseudo_order_lt_apart (x y : T) : x < y -> x <> y.
Proof.
intros. apply apart_iff_total_lt. left;assumption.
Defined.

Lemma pseudo_order_lt_apart_flip (x y : T) : x < y -> y <> x.
Proof.
intros. apply apart_iff_total_lt. right;assumption.
Defined.

Lemma not_lt_apart_lt_flip (x y : T) : ~x < y -> x <> y -> y < x.
Proof.
intros H H'. apply apart_iff_total_lt in H'. destruct H';auto.
destruct H;assumption.
Defined.

Lemma pseudo_order_cotrans_twice (x1 y1 x2 y2 : T)
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

Lemma pseudo_order_lt_ext (x1 y1 x2 y2 : T)
 : x1 < y1 -> minus1Trunc (x2 < y2 \/ x1 <> x2 \/ y2 <> y1).
Proof.
intros E.
pose (H := pseudo_order_cotrans_twice x1 y1 x2 y2 E). clearbody H;revert H.
apply minus1Trunc_rect_nondep;[|apply minus1Trunc_is_prop].
intros [?|[?|?]];apply min1; auto using pseudo_order_lt_apart.
Defined.

Global Instance pseudo_is_strict : StrictOrder (<).
Proof.
split.
- intros x E. destruct pseudoorder_antisym with x x;assumption.
- intros x y z E1 E2.
  pose (Htmp := iscotransitive _ _ E1 z);clearbody Htmp;revert Htmp.
  apply minus1Trunc_rect_nondep;[|apply Hpr]. intros [?|?].
  assumption.
  destruct pseudoorder_antisym with y z;auto.
Defined.

Global Instance pseudo_complement_trans : Transitive (fun x y : T => ~ x<y).
Proof.
intros x y z.
intros E1 E2 E3.
pose (Htmp := iscotransitive _ _ E3 y);clearbody Htmp;revert Htmp.
apply minus1Trunc_rect_nondep;[|intros []].
intros [?|?] ; contradiction.
Defined.

Global Instance pseudo_complement_antisym
 : Antisymmetric (fun x y => ~ x < y).
Proof.
red;simpl;unfold leq.
intros x y H H0.
apply (@apart_tight T (<>) _).
intro H';apply apart_iff_total_lt in H'. destruct H' as [H'|H'];auto.
Defined.

End PseudoOrder.


Section FullPoset.

Context T {r : FullRelation T}
 {Hpr : RelationProp (<>)} {Hpo : FullPoset r}.

Lemma lt_le : forall x y : T, x < y -> x <= y.
Proof.
intros ? ? H.
apply lt_iff_le_apart in H. apply H.
Defined.

Lemma lt_apart : forall (x y : T), x < y -> x <> y.
Proof.
intros ? ? H.
apply lt_iff_le_apart in H. apply H.
Defined.

Lemma le_not_lt_flip : forall (x y : T), x <= y -> ~ y < x.
Proof.
intros ? ? H H'.
apply lt_iff_le_apart in H'.
destruct H' as [H0 H1].
apply @irrefl_neq in H1. apply H1.
apply (@antisymmetric _ (<=));try assumption. apply Hpo.
apply Hpo.
Defined.

Lemma lt_not_le_flip : forall (x y : T), x < y -> ~ y <= x.
Proof.
intros ? ? H H'.
apply lt_iff_le_apart in H.
destruct H as [H0 H1].
apply (@irrefl_neq _ _ Hpo) in H1. apply H1.
apply (@antisymmetric _ (<=));try assumption. apply Hpo.
Defined.

Lemma lt_le_trans : forall x y : T, x < y ->
 forall z, y <= z -> x < z.
Proof.
intros ? ? H ? H'.
apply lt_iff_le_apart in H. destruct H as [H0 H1].
apply lt_iff_le_apart. split.
- eapply (@transitivity T (<=)). apply Hpo. apply H0. apply H'.
- pose (H := apart_cotrans _ _ H1 z). clearbody H.
  change (minus1Trunc ((x<>z) + (z<>y))) in H.
  revert H. apply minus1Trunc_rect_nondep;[|apply Hpr].
  intros [H|H]. assumption.
  apply lt_apart. apply (@symmetry T (<>)) in H.
  apply (@transitivity _ (<) _ _ y);apply lt_iff_le_apart;split;auto.
  apply Hpo.
Defined.

Lemma le_lt_trans : forall x y : T, x <= y -> forall z, y < z -> x < z.
Proof.
intros ? ? H ? H'.
apply lt_iff_le_apart in H';apply lt_iff_le_apart.
destruct H' as [H0 H1];split.
- eapply @transitivity;[apply Hpo|apply H|apply H0].
- pose (H' := apart_cotrans _ _ H1 x).
  clearbody H'. change (minus1Trunc ((y<>x) + (x<>z))) in H'. revert H'.
  apply minus1Trunc_rect_nondep;[|apply Hpr].
  intros [H' | H'];trivial.
  apply lt_apart.
  apply (@transitivity _ (<) _ _ y);apply lt_iff_le_apart;split;auto.
  apply @symmetry. apply Hpo. assumption.
Defined.

End FullPoset.

Section FullPseudoOrder.

Context T {r : FullRelation T}
 {Hpr : RelationProp (<)} {Hpo : FullPseudoOrder r}.

Lemma not_lt_le_flip : forall x y : T, ~y<x -> x<=y.
Proof.
intros. apply le_iff_not_lt_flip. assumption.
Defined.

Instance: Poset (<=).
Proof.
split.
- intros x y z H H'.
  apply le_iff_not_lt_flip.
  apply le_iff_not_lt_flip in H.
  apply le_iff_not_lt_flip in H'.
  revert H;revert H'.
  apply pseudo_complement_trans; apply _.
- intros x. change (x <= x). apply le_iff_not_lt_flip.
  revert x. change (Irreflexive (<)). apply @strictorder_irrefl.
  apply _.
- intros x y H H'.
  apply le_iff_not_lt_flip in H;apply le_iff_not_lt_flip in H'.
  apply (@pseudo_complement_antisym _ (<> <) _);assumption.
Defined.

Global Instance fullpseudo_is_fullposet : FullPoset r.
Proof.
split;try apply _.

intros x y. split.
intro H. split. apply le_iff_not_lt_flip.
red. apply pseudoorder_antisym;assumption.
apply apart_iff_total_lt. auto.
intros [H0 H1].
apply apart_iff_total_lt in H1. destruct H1.
assumption.
apply le_iff_not_lt_flip in H0. destruct H0;assumption.
Defined.

(* since x<=y is ~y<x, the double negation is equivalent *)
Lemma le_stable : forall x y : T, ~ ~ x <= y -> x<=y.
Proof.
intros ? ? H. apply le_iff_not_lt_flip. intro.
apply H. intro H'. apply le_iff_not_lt_flip in H'. auto.
Defined.

End FullPseudoOrder.

(**TODO**)
(*
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
 {Hp : RelationProp r},
forall P m, IsHProp (IsUpper r P m).
Proof.
intros. red in Hp.
apply trunc_forall.
Defined.

Instance lower_prop : forall (r : LeqRelation)
 {Hp : RelationProp r},
forall P m, IsHProp (IsLower r P m).
Proof.
intros. red in Hp.
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
 {Hp : RelationProp r} P {Hp' : forall x, IsHProp (P x)} m,
IsHProp (IsMaximum r P m).
Proof.
intros;eapply trunc_equiv'. apply ismax_sig.
apply trunc_sigma.
Defined.

Instance isminimum_prop : forall (r : LeqRelation)
 {Hp : RelationProp r} P {Hp' : forall x, IsHProp (P x)} m,
IsHProp (IsMinimum r P m).
Proof.
intros;eapply trunc_equiv'. apply ismin_sig.
apply trunc_sigma.
Defined.

Instance issupremum_prop : forall (r : LeqRelation)
 {Hp : RelationProp r},
forall P m, IsHProp (IsSupremum r P m).
Proof.
intros. apply isminimum_prop;apply _.
Defined.

Instance isinfimum_prop : forall (r : LeqRelation)
 {Hp : RelationProp r},
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
{Hr : RelationProp r} P {Hp : forall x, IsHProp (P x)},
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
pose (@supremum_prop r _).
apply trunc_forall.
pose (@infimum_prop r _).
apply trunc_forall.
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
{Hpr : RelationProp r} {Hto : IsTotalOrder r},
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
intros;split. apply Hto.
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
{P1 P2 P' : T -> Type}
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
*)

End Relation_pr.

Module OrderedMagma_pr.
Export OrderedMagma Magma_pr Relation_pr.
Generalizable Variable T.

Lemma linvariant_invariant : forall `(G : OpRel T) {Hcomm : Commutative G},
IsLInvariant G -> IsInvariant G.
Proof.
intros;split. assumption.
red;red. intros ? ? ?.
pattern (x&z). apply transport with (z&x). apply Hcomm.
pattern (y&z);apply transport with (z&y). apply Hcomm.
apply X.
Defined.

Lemma invariant_compat : forall `(G : OpRel T) {Htrans : Transitive (~>)},
 IsInvariant G -> IsCompat G.
Proof.
red;intros ? ? ? Hinv ? ? X ? ? Y.
apply Htrans with (gop x y');[apply islinvariant | apply isrinvariant];
assumption.
Defined.

Instance compat_linvariant : forall `(G : OpRel T) {Hrefl : Reflexive (~>)},
IsCompat G -> IsLInvariant G.
Proof.
red;intros ? ? ? Hc ? ? ? ?.
apply Hc. apply Hrefl.
assumption.
Defined.

Instance compat_rinvariant : forall `(G : OpRel T) {Hrefl : Reflexive (~>)},
IsCompat G -> IsRInvariant G.
Proof.
red;intros ? ? ? Hc ? ? ? ?.
apply Hc. assumption.
apply Hrefl.
Defined.

Instance linvariant_prop : forall `(G : OpRel T)
 {Hprop : RelationProp (~>)}, IsHProp (IsLInvariant G).
Proof.
intros.
apply @trunc_forall. apply _.
intro. repeat (apply @trunc_forall;[apply _|intro]).
apply Hprop.
Defined.

Instance rinvariant_prop : forall `(G : OpRel T)
 {Hprop : RelationProp (~>)}, IsHProp (IsRInvariant G).
Proof.
intros.
apply @trunc_forall. apply _.
intro. repeat (apply @trunc_forall;[apply _|intro]).
apply Hprop.
Defined.

Definition invariant_sig : forall `(G : OpRel T),
sigT (fun _ : IsLInvariant G => IsRInvariant G) <~> IsInvariant G.
Proof.
intros.
issig (BuildIsInvariant _ G) (@isinvariant_left _ G) (@isinvariant_right _ G).
Defined.

Instance invariant_prop : forall `(G : OpRel T)
 {Hprop : RelationProp (~>)}, IsHProp (IsInvariant G).
Proof.
intros;eapply trunc_equiv'.
apply invariant_sig.
apply @trunc_sigma. apply _.
intro; apply _.
Defined.

Instance compat_prop : forall `(G : OpRel T)
 {Hprop : RelationProp (~>)}, IsHProp (IsCompat G).
Proof.
intros. red in Hprop.
apply trunc_forall.
Defined.

Lemma rinverse_lregular : forall `{G : OpRel T} {Hassoc : Associative (&)}
{Hcompat : IsLInvariant G}
(x y : T) {Hinv : Rinverse (&) x y}, IsLRegular G x.
Proof.
intros;red. intros a b H.
pattern b. apply transport with (gop y (gop x b)).
path_via (gop (gop y x) b). apply Hinv.
pattern a. apply transport with (gop y (gop x a)).
path_via (gop (gop y x) a). apply Hinv.
apply Hcompat. assumption.
Defined.

Lemma linverse_rregular : forall `{G : OpRel T} {Hassoc : Associative (&)}
{Hcompat : IsRInvariant G}
(x y : T) {Hinv : Linverse (&) x y}, IsRRegular G x.
Proof.
intros;red. intros a b H.
pattern b. apply transport with (gop (gop b x) y).
path_via (gop b (gop x y)). apply Hinv.
pattern a. apply transport with (gop (gop a x) y).
path_via (gop a (gop x y)). apply Hinv.
apply Hcompat. assumption.
Defined.

Lemma inverse_regular : forall `(G : OpRel T) {Hassoc : Associative (&)}
{Hcompat : IsInvariant G}
(x y : T) {Hinv : IsInverse (&) x y}, IsRegular G x.
Proof.
intros;split;[eapply rinverse_lregular|eapply linverse_rregular];apply Hinv.
Defined.

Lemma invariant_inverse_flip : forall `{G : OpRel T} {Hsg : IsSemigroup G}
{Hr : IsLInvariant G}, forall x x', IsInverse G x x' ->
forall y y', IsInverse G y y' -> x ~> y -> y' ~> x'.
Proof.
intros ? ? ? ? ? ? X ? ? Y ?.
pattern y';apply transport with ((x' & y') & x);[|
apply transport with ((x' & y') & y);[|apply Hr;assumption]].
path_via ((x' & x) & y').
path_via (x' & (y' & x)). symmetry;apply associative;apply _.
path_via (x' & (x & y')). apply ap. apply commutative;apply _.
apply associative;apply _.
apply X.
path_via (x' & (y' & y)). symmetry;apply associative;apply _.
apply Y.
Defined.

Lemma gopp_rrel_flip : forall `{G : OpRel T} {Hg : IsGroup G}
{Hr : IsLInvariant G}, forall x y, x ~> y -> goppV y ~> goppV x.
Proof.
intros ? ? ? ? ? ?.
apply invariant_inverse_flip;apply goppP.
Defined.

End OrderedMagma_pr.

Module Ring_pr.
Export Ring Magma_pr.
Import minus1Trunc.
Generalizable Variable T.

Instance distrib_prop : forall `{G : Prering T} {Hset : IsHSet T},
 IsHProp (Distributes G).
Proof.
intros. apply (@trunc_equiv' (sigT (fun _ : Ldistributes G => Rdistributes G))).
issig (BuildDistributes G) (@distributes_left _ G) (@distributes_right _ G).
apply @trunc_sigma;[|intro C;clear C];apply trunc_forall.
Defined.

Instance issemir_prop : forall `{G : Prering T} {Hset : IsHSet T},
 IsHProp (IsSemiring G).
Proof.
intros.
apply (@trunc_equiv' (sigT (fun _ : IsCMonoid (prering_plus G) => 
  sigT (fun _ : IsMonoid (prering_mult G) => 
    Distributes G)))).
issig (BuildIsSemiring G) (@semiring_plus _ G) (@semiring_mult _ G)
 (@semiring_distributes _ G).

repeat (apply @trunc_sigma;[|intro C;clear C]);try apply _.
apply iscmono_prop. apply ismonoid_prop.
Defined.

Instance semiring_cancel : forall `{G : Prering T} {Hg : IsSemiring G}
 (a : T), Cancel (+) a := _.

Lemma rmult_0_l : forall `{G : Prering T} {Hg : IsSemiring G},
forall x : T, ZeroV ° x = ZeroV.
Proof.
intros.
apply semiring_cancel with (ZeroV ° x).
path_via ((ZeroV + ZeroV) ° x).
symmetry. apply rdistributes. apply _.
path_via (ZeroV ° x).
apply (ap (fun g => g ° x)). apply Zero.
apply inverse;apply Zero.
Defined.

Lemma rmult_0_r : forall `{G : Prering T} {Hg : IsSemiring G},
forall x : T, x ° ZeroV = ZeroV.
Proof.
intros.
apply semiring_cancel with (x ° ZeroV).
path_via (x ° (ZeroV + ZeroV)).
symmetry;apply ldistributes;apply _.
path_via (x ° ZeroV). apply ap;apply Zero.
apply inverse;apply Zero.
Defined.

Lemma rmult_inverse_right : forall `{G : Prering T} {Hg : IsSemiring G},
 forall x y : T, IsInverse (+) x y -> 
forall z,  IsInverse (+) (z°x) (z°y).
Proof.
intros ? ? ? ? ? H ?. apply linverse_inverse.
red. apply transport with ZeroV;[|apply Zero].
path_via (z ° (x + y)).
path_via (z°ZeroV). apply inverse; apply rmult_0_r.
apply ap. apply (id_unique (+)). apply Zero. apply H.
apply ldistributes;apply _.
Defined.

Lemma rmult_inverse_left : forall `{G : Prering T} {Hg : IsSemiring G},
 forall x y : T, IsInverse (+) x y -> 
forall z,  IsInverse (+) (x°z) (y°z).
Proof.
intros ? ? ? ? ? H ?. apply linverse_inverse.
red. apply transport with ZeroV;[|apply Zero]. symmetry; path_via ((x + y)°z).
symmetry;apply rdistributes;apply _.
path_via (ZeroV°z). apply (ap (fun g => g°z)).
apply (id_unique (prering_plus G));[apply H | apply Zero].
apply rmult_0_l.
Defined.

Lemma ropp_rmult_left : forall `{G : Prering T} {Hg : IsRing G},
 forall x y : T, roppV (x°y) = (roppV x)°y.
Proof.
intros. apply (@group_inverse_gopp _ (+)).
eapply rmult_inverse_left. apply _.
Defined.

Lemma ropp_rmult_right : forall `{G : Prering T} {Hg : IsRing G},
 forall x y : T, roppV (x°y) = x°(roppV y).
Proof.
intros. apply (@group_inverse_gopp _ (+)).
eapply rmult_inverse_right. apply _.
Defined.

Lemma ropp_zero : forall `{G : Prering T} {Hg : IsRing G},
roppV ZeroV = ZeroV.
Proof.
intros;apply (@gopp_gid).
Defined.

Lemma ropp_r : forall `{G : Prering T} {Hg : IsRing G},
forall x : T, x + roppV x = ZeroV.
Proof.
intros. apply (id_unique (+)).
apply roppP. apply Zero.
Defined.

Lemma ropp_l : forall `{G : Prering T} {Hg : IsRing G},
forall x : T, roppV x + x = ZeroV.
Proof.
intros. apply (id_unique (+)).
apply roppP. apply Zero.
Defined.

Definition isring_sig : forall `{G : Prering T},
 sigT (fun semir : IsSemiring G => forall x, Inverse (+) x)
  <~> IsRing G.
Proof.
intros. issig (BuildIsRing G) (@ring_is_semir _ G) (@r_opp _ G).
Defined.

Instance isring_prop : forall `{G : Prering T} {Hset : IsHSet T},
 IsHProp (IsRing G).
Proof.
intros.
eapply trunc_equiv'. apply isring_sig.
apply @trunc_sigma. apply _.
intro. apply @trunc_forall. apply _. intros. apply @inverse_prop. apply _.
apply _.
Defined.

Definition easyIsRing `(G : Prering T) (Hgr : IsGroup (+))
 (Hmon : IsMonoid (°)) (Hdis : Distributes G) : IsRing G.
Proof.
split;[ split;apply _| apply Hgr].
Defined.

Lemma strictintegral_integral_pr : forall `{G : Prering T} {Hg : IsSemiring G}
 {Hr: IsStrictIntegral G}, forall a : T, neq ZeroV a ->
 forall b : T, neq ZeroV b -> neq ZeroV (a°b).
Proof.
intros ? ? ? ? ? Ha ? Hb H.
apply Hr in H. revert H. apply minus1Trunc_rect_nondep.
intros [H|H];auto.
intros [].
Defined.

Lemma strictintegral_intdom : forall `(G : Prering T) {Hg : IsRing G}
 {Hr : IsStrictIntegral G}, neq ZeroV OneV -> IsIntegralDomain G.
Proof.
intros. apply (BuildIsIntegralDomain _ _).
apply strictintegral_integral_pr.
assumption.
Defined.

Lemma intdom_partial_cancels_left : forall `{G : Prering T} {Hg : IsRing G}
 {Hr : IsStrictIntegral G} {Hset : IsHSet T},
 forall a : T, neq ZeroV a -> Lcancel (°) a.
Proof.
intros ? ? ? ? ? ? H. red. intros.
assert (a ° (b + (roppV c)) = ZeroV).
eapply concat.
apply (@semiring_distributes _ G _).
apply (@right_cancel _ (+) (a ° c) _).
path_via (a°b + (a° (roppV c) + a°c)).
symmetry. apply (@associative _ (+) _).
eapply concat;[|symmetry;apply gidP].
eapply concat;[|apply X].
eapply concat;[ apply ap | apply (@gidP _ (+) _)].
eapply concat. symmetry.
apply semiring_distributes;apply _.
eapply concat;[apply ap | apply rmult_0_r].
apply (@id_unique _ (+) _);try apply _.
apply roppP.

apply inverse in X0;apply Hr in X0. revert X0.
apply minus1Trunc_rect_nondep;[|apply Hset].
intros [p | p].
destruct H;auto.
assert (Hcan : forall a, Rcancel (+) a). apply _.
apply (Hcan (roppV c)).
eapply concat. symmetry. apply p.
symmetry. apply (id_unique (+)); apply _.
Defined.

Lemma intdom_partial_cancels_right :forall `{G : Prering T} {Hg : IsRing G}
 {Hr : IsStrictIntegral G} {Hset : IsHSet T},
  forall a : T, neq ZeroV a -> Rcancel (°) a.
Proof.
intros ? ? ? ? ? ? ? ? ? X. apply intdom_partial_cancels_left with a;auto.
eapply concat;[|eapply concat;[apply X|]];
apply commutative;apply _.
Defined.

Lemma intdom_partial_cancels : forall  `{G : Prering T} {Hg : IsRing G}
 {Hr : IsStrictIntegral G} {Hset : IsHSet T},
  forall a : T, neq ZeroV a -> Cancel (°) a.
Proof.
intros;split;
[apply intdom_partial_cancels_left | apply intdom_partial_cancels_right];
assumption.
Defined.

Lemma zero_inverse_prop : forall `{G : Prering T} {Hg : IsSemiring G},
 Inverse (°) ZeroV -> forall x : T, ZeroV = x.
Proof.
intros ? G ? Y x. apply inverse.
path_via (x ° ((inverse_val Y) ° ZeroV)).
apply inverse.
apply Y.
path_via (x ° ZeroV);[apply ap|];apply rmult_0_r.
Defined.


End Ring_pr.

Module RelatorInverse.
Export Relation_pr OrderedMagma_pr.
Import minus1Trunc.
Generalizable Variable T.

Definition inverseRel `(R : Rel T) : Rel T := fun x y => y ~> x.

Notation "r ^-1" := (inverseRel r).

Lemma inverse_inverse : forall `(r : Rel T), r ^-1 ^-1 = r.
Proof.
intros T r;reflexivity.
Defined.

Instance inverse_refl : forall `(r : Rel T) {Hr : Reflexive r},
 Reflexive (r ^-1) := fun _ _ => idmap.

Instance inverse_symm : forall `(r : Rel T) {Hs : Symmetric r},
 Symmetric (r ^-1).
Proof.
intros ? ? ? ? ?;apply Hs.
Defined.

Instance inverse_trans : forall `(r : Rel T) {Ht : Transitive r},
 Transitive (r ^-1).
Proof.
intros ? ? ? ? ? ? H H';apply Ht with y;assumption.
Defined.

Definition inverse_P : forall T (P : Rel T -> Prop),
(forall r, P r -> P (inverseRel r)) -> forall r, P (r ^-1) -> P r.
Proof.
intros ? ? H rel Hr.
change (P (inverseRel (inverseRel rel))). apply H. assumption.
Defined.

Instance inverse_equivalence : forall `(r : Rel T) {He : Equivalence r},
 Equivalence (r ^-1).
Proof.
intros;split;apply _.
Defined.

Instance inverse_is_prop : forall `(r : Rel T) {Hp : RelationProp r},
 RelationProp (r ^-1)
 := fun _ _ H x y => H y x.

Instance inverse_antisymm : forall `(r : Rel T) {Ha : Antisymmetric r},
 Antisymmetric (r ^-1).
Proof.
intros ? ? ? ? ? H H'. apply Ha;assumption.
Defined.

Instance inverse_irrefl : forall `(r : Rel T) {Hi : Irreflexive r},
 Irreflexive (r ^-1) := fun _ _ => idmap.

Instance inverse_poset : forall `(r : Rel T) {Hp : Poset r}, Poset (r ^-1).
Proof.
intros;split;
[ apply inverse_trans | apply inverse_refl | apply inverse_antisymm];
apply Hp.
Defined.

Instance inverse_cotrans :  forall `(r : Rel T) {Hs : Cotransitive r},
 Cotransitive (r ^-1).
Proof.
intros;intros ? ? H ?.
eapply minus1Trunc_rect_nondep;[|apply minus1Trunc_is_prop|apply Hs;apply H].
intros [H'|H'];apply min1;[right|left];apply H'.
Defined.

Instance inverse_apart : forall `(r : Rel T) {Ha : Apartness r},
 Apartness (r ^-1).
Proof.
intros;split.
apply inverse_irrefl;apply Ha. apply inverse_symm;apply Ha.
apply inverse_cotrans;apply Ha.
intros ? ? H;apply Ha. intro H'. apply H. apply Ha. assumption.
Defined.

(**TODO**)
(*
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
{P : T->Type} {m:r} {H : IsLower (r ^-1) P m},
IsUpper r P m.
Proof.
intros;apply H.
Defined.

Definition inverse_upper_lower : forall {r : Relation}
{P : T->Type} {m:r} {H : IsUpper (r ^-1) P m},
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
change ((fun (r : Relation) (P : T -> Type) (m : T) =>
 IsMaximum r (IsLower r P) m)  =
(fun (r : Relation) (P : T -> Type) (m : T) => IsMinimum r ^-1 (IsLower r P) m)).
apply (@ap _ _ (fun IS : forall r : Relation, (r -> Type) -> r -> Type
  => fun r P m => IS r (IsLower r P) m) IsMaximum (fun r => IsMinimum r^-1)).
apply inverse_ismax_rw.
Defined.

Lemma inverse_issup_rw : IsSupremum = fun r => IsInfimum (r^-1).
Proof.
change ((fun (r : Relation) (P : T -> Type) (m : T) =>
 IsMinimum r (IsUpper r P) m)  =
(fun (r : Relation) (P : T -> Type) (m : T) => IsMaximum r ^-1 (IsUpper r P) m)).
apply (@ap _ _ (fun IS : forall r : Relation, (r -> Type) -> r -> Type
  => fun r P m => IS r (IsUpper r P) m) IsMinimum (fun r => IsMaximum r^-1)).
apply inverse_ismin_rw.
Defined.
*)

End RelatorInverse.

(*
Module Lattice_pr.
Export Lattice Relation_pr RelatorInverse.
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

Instance meet_is_inf2 : forall {x y : T}, IsInfimum r (doubleton x y) (gop x y).
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
{Hmeet : forall a b : T, IsInfimum r (doubleton a b) (gop a b)}.

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
apply minimum_is_infimum. apply @singleton_min. apply _. apply Hpo.
Defined.

Lemma meet_gop_eq_pr : forall x y z : T, IsInfimum r (doubleton x y) z -> 
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
  (fun x y : T => rrel y x)).

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
apply inverse_P. apply @inverse_poset.
change (IsPoset (semil_inverse r)).
apply semilattice_meet_poset.
Defined.

Instance join_is_sup2 : forall {r : LR_sig}
{Hs : IsHSet r} {Hp : RelationProp r} {Hr : IsJoinSemiLattice r},
forall {x y : T}, IsSupremum r (doubleton x y) (gop x y).
Proof.
intros ? ? ? ?.
intros.
assert (Hr' : IsMeetSemiLattice (semil_inverse r)). apply _.
apply inverse_issup_iff.
apply (@meet_is_inf2 _ _ Hr').
Defined.

Section Order_to_join.

Context {r : LR_sig} {Hset : IsHSet r} {Hpr : RelationProp r} {Hpo : IsPoset r}
{Hjoin : forall a b : T, IsSupremum r (doubleton a b) (gop a b)}.

Lemma join_gop_eq_pr : forall x y z : T, IsSupremum r (doubleton x y) z -> 
gop x y = z.
Proof.
intros ? ? ?. apply supremum_unicity;apply _.
Defined.

Instance join_semilattice : IsJoinSemiLattice r.
Proof.
apply @inverse_semijoin.
apply @meet_semilattice. apply _. apply inverse_poset.
intros. apply inverse_issup_iff. apply _.
Defined.

End Order_to_join.

End Lattice_pr.
*)

Module Field_pr.
Export Field Ring_pr Relation_pr.
Import minus1Trunc.
Generalizable Variable F.

Lemma field_intdom_pr : forall `{L : Prefield F} {Hf : IsField L},
forall a : F, neq ZeroV a -> forall b : F, neq ZeroV b
 -> neq ZeroV (a ° b).
Proof.
intros ? ? ? ? Ha ? Hb H.
assert (Ha' : ~ ~ (ZeroV <> a)).
  intro H'. apply Ha. apply @apart_tight in H'. assumption. apply _.

destruct Ha'. intro Ha'.
apply Hb.
eapply inverse_cancel. apply finv. apply Ha'.
eapply concat. apply rmult_0_r.
assumption.
Defined.

Instance field_is_intdom : forall `{L : Prefield F} {Hf : IsField L},
 IsIntegralDomain (+ °).
Proof.
intros. apply (BuildIsIntegralDomain _ field_is_ring).
apply field_intdom_pr.
red. eapply @irrefl_neq. apply Hf. apply field_neq.
Defined.

Instance field_left_cancel : forall `{L : Prefield F} {Hf : IsField L},
forall a : F, neq ZeroV a -> Lcancel (°) a.
Proof.
intros ? ? ? ? Ha.
intros b c H.
apply (@apart_tight F _ _). intro H'.
assert (Ha' : ~ ~ (ZeroV <> a)). intro Ha'.
apply Ha. apply (@apart_tight F _ _). assumption.
destruct Ha'.
intros Ha'.
eapply (@irrefl_neq F _). apply Hf. apply H'.
eapply (@inverse_cancel _ (°) _). apply finv. apply Ha'.
assumption.
Defined.

Instance field_cancel : forall `{L : Prefield F} {Hf : IsField L},
forall a : F, neq ZeroV a -> Cancel (°) a.
Proof.
intros. apply left_cancel_cancel.
apply field_left_cancel. assumption.
Defined.

Lemma field_inverse_apart : forall `{L : Prefield F} {Hf : IsField L},
forall (a b : F), IsInverse (°) a b -> ZeroV <> b.
Proof.
intros. apply field_inv_neq. exists a. apply inverse_symm. assumption.
Defined.


Section Field_of_DecField.

Variables (F : Type) (L : Prefield F).

Hypothesis Hneq : forall x y : F, x<>y <-> neq x y.

Context {Hdec : decidable_paths F} {Hfield : IsDecField (+ °)}.

Global Instance decfield_is_field : IsField L.
Proof.
refine (BuildIsField _ _ _ decfield_is_ring _ _ _ _ _).
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
- apply Hneq. pose decfield_neq. simpl in n. apply n.
- intros. exists (dec_inv x). apply dec_inv_ok. apply Hneq;assumption.
- intros x X. apply Hneq;intro H.
  destruct H.
  apply decfield_neq.
  apply zero_inverse_prop. assumption.
Defined.

End Field_of_DecField.

End Field_pr.





