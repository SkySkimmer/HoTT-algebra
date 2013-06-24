Require Import HoTT FunextAxiom UnivalenceAxiom.
Require Import unique_choice.
Require Export structures.

Module Magma_pr.
Export Magma.

Instance law_set : forall A, IsHSet A -> IsHSet (law A).
Proof.
intros.
apply @trunc_arrow. exact _.
apply trunc_arrow.
Defined.

Definition magma_sigma : sigT class <~> magma.
Proof.
issig BuildMagma gcarr gclass.
Defined.

Definition magma_sig : sigT law <~> magma.
Proof.
pose (f := fun G : sigT law => easyMagma (G .1) (G .2)).
pose (finv := fun G : magma => existT law G (@gop G)).
pose (Hsec := fun G : sigT law => match G as G' return finv (f G') = G' with
  | existT g m => idpath end).
pose (Hinv := fun G : magma => match G as G' return f (finv G') = G' with
  | BuildMagma g (BuildClass m) => idpath end).
apply BuildEquiv with f. apply BuildIsEquiv with finv Hinv Hsec.

intros G. unfold Hinv;unfold Hsec;clear Hinv Hsec.
destruct G. simpl. reflexivity.
Defined.

Instance assoc_prop : forall {G : magma} {Hset : IsHSet G},
 IsHProp (Associative G).
Proof.
intros.
apply hprop_forall. intro;apply hprop_forall. intro;apply hprop_forall.
intro.
apply hprop_allpath. apply Hset.
Defined.

Instance comm_prop : forall {G : magma} {Hset : IsHSet G},
 IsHProp (Commutative G).
Proof.
intros.
apply hprop_forall. intro;apply hprop_forall.
intro.
apply hprop_allpath. apply Hset.
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
apply @hprop_forall. exact _. intros.
apply hprop_allpath.
apply Hset.
intro H;clear H.
apply @hprop_forall. exact _. intros.
apply hprop_allpath.
apply Hset.
Defined.

Lemma left_id_id : forall {G : semigroup} {e : G}, Left_id e -> IsId e.
Proof.
intros ? ? X. split;auto.
intro.
eapply concat. apply sg_comm. apply X.
Defined.

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
apply @trunc_sigma;[|intro C;clear C];
repeat (apply @hprop_forall;[ exact _ | intros]);
apply hprop_allpath;
apply Hset.
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
gop x y = gid.
Proof.
intros. apply id_unique;apply _.
Defined.

Lemma rinverse_eq_gid : forall {G : monoid} {x y : G} {Hinv : Rinverse x y},
gop y x = gid.
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
 @IsInverse G x y -> @paths G (gopp x) y.
Proof.
intros. 
apply (@inverse_unicity G _) with x.
 apply gopp_correct.
 assumption.
Defined.

Lemma gopp_gopp : forall {G : group} (x : G), @paths G (gopp (gopp x)) x.
Proof.
intros. apply group_inverse_gopp.
apply inverse_symm. apply gopp_correct.
Defined.

Instance gid_isinverse : forall G : monoid, @IsInverse G gid gid.
Proof.
intros.
split;red;(apply transport with gidV;[symmetry;apply gid_id|]);apply _.
Defined.

Lemma gopp_gid : forall G : group, @paths G (gopp gid) gid.
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

Instance gopp_prop : forall (G : monoid) {Hset : IsHSet G},
 IsHProp (forall x : G, Inverse x).
Proof.
intros.
apply hprop_forall. apply _.
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
Export Related.
Import minus1Trunc.

Instance istrans_prop : forall {r : relator}
 {Hprop : forall x y : r, IsHProp (rrel x y)}, IsHProp (IsTransitive r).
Proof.
intros.
repeat (apply hprop_forall;intro). apply _.
Defined.

Instance isrefl_prop : forall {r : relator}
 {Hprop : forall x y : r, IsHProp (rrel x y)}, IsHProp (IsReflexive r).
Proof.
intros.
repeat (apply hprop_forall;intro). apply _.
Defined.

Instance issymm_prop : forall {r : relator}
 {Hprop : forall x y : r, IsHProp (rrel x y)}, IsHProp (IsSymmetric r).
Proof.
intros.
repeat (apply hprop_forall;intro). apply _.
Defined.

Definition IsEquivalence_sig : forall r, 
sigT (fun _ : IsReflexive r => sigT (fun _ : IsSymmetric r => IsTransitive r))
<~> IsEquivalence r.
Proof.
intro r. issig (BuildIsEquivalence r) (@equivalence_refl r) (@equivalence_symm r)
  (@equivalence_trans r).
Defined.

Instance isequivalence_prop : forall {r : relator}
 {Hprop : forall x y : r, IsHProp (rrel x y)}, IsHProp (IsEquivalence r).
Proof.
intros.
eapply trunc_equiv'.
apply IsEquivalence_sig.
apply @trunc_sigma. apply _.
intro. apply @trunc_sigma. apply _.
intro;apply _.
Defined.

Lemma irrefl_neq : forall {R} {Hr : IsIrreflexive R}, 
  forall x y : R, rrel x y -> x = y -> Empty.
Proof.
intros ? ? ? ? ?. intros H. destruct H. apply Hr with x. assumption.
Defined.

Instance isantisymm_prop : forall {r : relator} {Hset : IsHSet r},
 IsHProp (IsAntisymmetric r).
Proof.
intros.
repeat (apply hprop_forall;intro). apply hprop_allpath;apply Hset.
Defined.

Instance isirrefl_prop : forall {r}, IsHProp (IsIrreflexive r).
Proof.
intros.
repeat (apply hprop_forall;intro). apply _.
Defined.

Definition isposet_sig : forall r, sigT (fun _ : IsTransitive r => 
sigT (fun _ : IsReflexive r => IsAntisymmetric r)) <~> IsPoset r.
Proof.
intro r;
issig (BuildIsPoset r) (@order_trans r) (@order_refl r) (@order_antisymm r).
Defined.

Instance isposet_prop : forall {r : relator} {Hset : IsHSet r}
 {Hprop : forall x y : r, IsHProp (rrel x y)}, IsHProp (IsPoset r).
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
repeat (apply hprop_forall;intro). apply minus1Trunc_is_prop.
Defined.

Definition isapart_sig : forall r, sigT (fun _ : IsIrreflexive r =>
sigT (fun _ : IsSymmetric r => IsCotransitive r)) <~> IsApartness r.
Proof.
intros.
issig (BuildIsApartness r) (@apart_irrefl r) (@apart_symm r) (@apart_cotrans r).
Defined.

Instance isapart_prop : forall {r : relator}
 {Hprop : forall x y : r, IsHProp (rrel x y)}, IsHProp (IsApartness r).
Proof.
intros;eapply trunc_equiv'.
apply isapart_sig.
apply @trunc_sigma. apply _.
intro. apply @trunc_sigma. apply _.
intro;apply _.
Defined.

Instance islinear_prop : forall {r}, IsHProp (IsLinear r).
Proof.
intro. repeat (apply hprop_forall;intro). apply minus1Trunc_is_prop.
Defined.

Definition isstrictposet_sig : forall r, sigT (fun _ : IsIrreflexive r => 
IsTransitive r) <~> IsStrictPoset r.
Proof.
intros. issig (BuildIsStrictPoset r) (@strictposet_irrefl r)
  (@strictposet_trans r).
Defined.

Instance isstrictposet_prop : forall {r : relator}
 {Hp : forall x y : r, IsHProp (rrel x y)}, IsHProp (IsStrictPoset r).
Proof.
intros. eapply trunc_equiv'.
apply isstrictposet_sig.
apply @trunc_sigma. apply _. intros;apply _.
Defined.

Lemma strict_poset_antisymm : forall (r : relator) {Hstrict : IsStrictPoset r}, 
forall x y : r, rrel x y -> rrel y x -> Empty.
Proof.
intros. destruct Hstrict as [Hirr Htrans].
apply Hirr with x;eauto.
Defined.

Instance strict_poset_disjunct_prop : forall (r : relator)
 {Hp : forall x y : r, IsHProp (rrel x y)}
 {Hstrict : IsStrictPoset r}, forall x y : r, 
  IsHProp (rrel x y \/ rrel y x).
Proof.
intros. apply hprop_allpath.
intros [Hx|Hx] [Hy|Hy];try (apply ap;apply Hp).
destruct (strict_poset_antisymm _ _ _ Hx Hy).
destruct (strict_poset_antisymm _ _ _ Hx Hy).
Defined.

Lemma apart_from_strict_poset : forall (r : relator2)
{Hstrict : IsStrictPoset (relator2_2 r)} {Hlin : IsStrictLinear (relator2_2 r)},
(forall x y : r, rrel2_1 x y <-> (rrel2_2 x y \/ rrel2_2 y x)) ->
IsApartness (relator2_1 r).
Proof.
intros ? ? ? H;split.
- intros x Hx.
  apply H in Hx. destruct Hx as [Hx|Hx];eapply strictposet_irrefl;apply Hx.
- intros x y H'. apply H in H';apply H.
  destruct H';auto.
- intros x y H' z.
  apply H in H';destruct H' as [H'|H'];
  apply Hlin in H';(eapply minus1Trunc_rect_nondep;
  [ | apply minus1Trunc_is_prop |apply (H' z)]);intros [H0|H0];apply min1;
  solve [left;apply H;auto | right;apply H;auto].
Defined.

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

Instance upper_prop : forall (r : relator)
 {Hp : forall x y : r, IsHProp (rrel x y)},
forall P m, IsHProp (IsUpper r P m).
Proof.
intros. repeat (apply hprop_forall;intros);apply _.
Defined.

Instance lower_prop : forall (r : relator)
 {Hp : forall x y : r, IsHProp (rrel x y)},
forall P m, IsHProp (IsLower r P m).
Proof.
intros. repeat (apply hprop_forall;intros);apply _.
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

Instance ismaximum_prop : forall (r : relator)
 {Hp : forall x y : r, IsHProp (rrel x y)} P {Hp' : forall x, IsHProp (P x)}  m, 
IsHProp (IsMaximum r P m).
Proof.
intros;eapply trunc_equiv'. apply ismax_sig.
apply trunc_sigma.
Defined.

Instance isminimum_prop : forall (r : relator)
 {Hp : forall x y : r, IsHProp (rrel x y)} P {Hp' : forall x, IsHProp (P x)}  m, 
IsHProp (IsMinimum r P m).
Proof.
intros;eapply trunc_equiv'. apply ismin_sig.
apply trunc_sigma.
Defined.

Instance issupremum_prop : forall (r : relator)
 {Hp : forall x y : r, IsHProp (rrel x y)},
forall P m, IsHProp (IsSupremum r P m).
Proof.
intros. apply isminimum_prop;apply _.
Defined.

Instance isinfimum_prop : forall (r : relator)
 {Hp : forall x y : r, IsHProp (rrel x y)},
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
{Hr : forall x y : r, IsHProp (rrel x y)} P {Hp : forall x, IsHProp (P x)},
IsHProp (Maximum r P).
Proof.
intros;eapply trunc_equiv'. apply maximum_sig.
apply hprop_allpath. intros [x Hx] [y Hy].
apply path_sigma with (maximum_unicity _ _ _ _ _ _).
apply ismaximum_prop;apply _.
Defined.

Instance minimum_prop : forall {r} {Ho : IsPoset r}
{Hr : forall x y : r, IsHProp (rrel x y)} P {Hp : forall x, IsHProp (P x)},
IsHProp (Minimum r P).
Proof.
intros;eapply trunc_equiv'. apply minimum_sig.
apply hprop_allpath. intros [x Hx] [y Hy].
apply path_sigma with (minimum_unicity _ _ _ _ _ _).
apply isminimum_prop;apply _.
Defined.

Instance supremum_prop : forall {r} {Ho : IsPoset r}
{Hp : forall x y : r, IsHProp (rrel x y)}, 
forall P, IsHProp (Supremum r P).
Proof.
intros.
apply minimum_prop;apply _.
Defined.

Instance infimum_prop : forall {r} {Ho : IsPoset r}
{Hp : forall x y : r, IsHProp (rrel x y)}, 
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

Instance islattice_prop : forall (r : relator)
{Hset : IsHSet r} {Hp : forall x y : r, IsHProp (rrel x y)}, 
IsHProp (IsLattice r).
Proof.
intros. eapply trunc_equiv'. apply islattice_sig.
repeat (apply @trunc_sigma;[try apply _ | intro]).
apply _.
Defined.

Lemma total_order_max2 : forall {r : relator} {Hset : IsHSet r}
{Hpr : forall x y : r, IsHProp (rrel x y)} {Hto : IsTotalOrder r},
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

Lemma total_order_min2 : forall {r : relator} {Hset : IsHSet r}
{Hpr : forall x y : r, IsHProp (rrel x y)} {Hto : IsTotalOrder r},
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

Instance total_order_lattice : forall {r : relator} {Hset : IsHSet r}
{Hpr : forall x y : r, IsHProp (rrel x y)}
{Hto : IsTotalOrder r}, IsLattice r.
Proof.
intros;split. apply _.
intros. apply maximum_supremum. apply total_order_max2.
intros. apply minimum_infimum. apply total_order_min2.
Defined.

(* Not sure if useful
Definition inverseRel (r : relator) : relator := 
  BuildRelator r (Related.BuildClass r (fun x y : r => rrel y x)).

Lemma inverse_inverse_rel : forall r, inverseRel (inverseRel r) = r.
Proof.
destruct r as [r [l]]. reflexivity.
Defined.

Instance upper_inverse_lower : forall r P m, IsUpper r P m ->
 IsLower (inverseRel r) P m.
Proof.
intros;assumption.
Defined.

Instance lower_inverse_upper : forall r P m, IsLower r P m ->
 IsUpper (inverseRel r) P m.
Proof.
intros;assumption.
Defined.

Instance ismax_inverse_ismin : forall r P m, IsMaximum r P m ->
 IsMinimum (inverseRel r) P m.
Proof.
intros ? ? ? H;split;apply H.
Defined.

Instance ismin_inverse_ismax : forall r P m, IsMinimum r P m ->
 IsMaximum (inverseRel r) P m.
Proof.
intros ? ? ? H;split;apply H.
Defined.

Lemma inverse_ismax_ismin : forall r P m, IsMaximum (inverseRel r) P m ->
 IsMinimum r P m.
Proof.
intros ? ? ? H;split;apply H.
Defined.

Lemma inverse_ismin_ismax : forall r P m, IsMinimum (inverseRel r) P m ->
 IsMaximum r P m.
Proof.
intros ? ? ? H;split;apply H.
Defined.
*)

End Related_pr.

Module OMag_pr.
Export OrderedMagma Magma_pr Related_pr.

Lemma invariant_compat : forall (G : oMag) {Htrans : IsTransitive G},
 IsInvariant G -> IsCompat G.
Proof.
red;intros ? ? Hinv ? ? X ? ? Y.
apply Htrans with (gop x y');[apply invariant_left | apply invariant_right];
assumption.
Defined.

Instance compat_linvariant : forall (G : oMag) {Hrefl : IsReflexive G}, 
IsCompat G -> IsLInvariant G.
Proof.
red;intros ? ? Hc ? ? ? ?.
apply Hc. apply Hrefl.
assumption.
Defined.

Instance compat_rinvariant : forall (G : oMag) {Hrefl : IsReflexive G}, 
IsCompat G -> IsRInvariant G.
Proof.
red;intros ? ? Hc ? ? ? ?.
apply Hc. assumption.
apply Hrefl.
Defined.

Instance linvariant_prop : forall (G : oMag)
 {Hprop : forall x y : G, IsHProp (rrel x y)}, IsHProp (IsLInvariant G).
Proof.
intros. 
repeat (apply hprop_forall;intro).
apply _.
Defined.

Instance rinvariant_prop : forall (G : oMag)
 {Hprop : forall x y : G, IsHProp (rrel x y)}, IsHProp (IsRInvariant G).
Proof.
intros. 
repeat (apply hprop_forall;intro).
apply _.
Defined.

Definition invariant_sig : forall G : oMag, 
sigT (fun _ : IsLInvariant G => IsRInvariant G) <~> IsInvariant G.
Proof.
intros.
issig (BuildIsInvariant G) (@invariant_left G) (@invariant_right G).
Defined.

Instance invariant_prop : forall (G : oMag)
 {Hprop : forall x y : G, IsHProp (rrel x y)}, IsHProp (IsInvariant G).
Proof.
intros;eapply trunc_equiv'.
apply invariant_sig.
apply @trunc_sigma. apply _.
intro; apply _.
Defined.

Instance compat_prop : forall (G : oMag)
 {Hprop : forall x y : G, IsHProp (rrel x y)}, IsHProp (IsCompat G).
Proof.
intros.
repeat (apply hprop_forall;intro).
apply _.
Defined.

Lemma rinverse_lregular : forall {G : oMag} {Hassoc : Associative G}
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

Lemma linverse_rregular : forall {G : oMag} {Hassoc : Associative G}
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

Lemma inverse_regular : forall (G : oMag) {Hassoc : Associative G}
{Hcompat : IsInvariant G}
(x y : G) {Hinv : IsInverse x y}, IsRegular G x.
Proof.
intros;split;[eapply rinverse_lregular|eapply linverse_rregular];apply Hinv.
Defined.

End OMag_pr.

Module Ring_pr.
Export Ring Magma_pr.
Import minus1Trunc.

Definition prering_sigma : sigT (fun carr => sigT (fun _ : Magma.class carr => 
  Magma.class carr)) <~> prering.
Proof.
issig BuildPrering rcarr raddC rmultC.
Defined.

Instance distrib_prop : forall {G : prering} {Hset : IsHSet G},
 IsHProp (Distributes G).
Proof.
intros. apply (@trunc_equiv' (sigT (fun _ : Ldistributes G => Rdistributes G))).
issig (BuildDistributes G) (@distrib_left G) (@distrib_right G).
apply @trunc_sigma;[|intro C;clear C];
repeat (apply hprop_forall;intro);
apply hprop_allpath; apply Hset.
Defined.

Instance issemir_prop : forall {G : prering} {Hset : IsHSet G},
 IsHProp (IsSemiring G).
Proof.
intros.
apply (@trunc_equiv' (sigT (fun _ : IsCMonoid (prering_add G) => 
  sigT (fun _ : IsMonoid (prering_mult G) => 
    Distributes G)))).
issig (BuildIsSemiring G) (@semiring_add G) (@semiring_mult G)
 (@semiring_distributes G).

repeat (apply @trunc_sigma;[|intro C;clear C]);apply _.
Defined.

Instance semiring_cancel : forall {G : semiring} (a : prering_add G), Cancel a
 := fun _ _ => _.

Lemma rmult_0_l : forall {G : semiring}, 
forall x : G, ZeroV ° x = ZeroV.
Proof.
intros.
apply semiring_cancel with (ZeroV ° x).
path_via ((ZeroV + ZeroV) ° x).
symmetry. apply semiring_distributes.
path_via (ZeroV ° x).
apply (ap (fun g => g ° x)). apply gid_id.
apply inverse;apply gid_id.
Defined.

Lemma rmult_0_r : forall {G : semiring}, 
forall x : G, x ° ZeroV = ZeroV.
Proof.
intros.
apply semiring_cancel with (x ° ZeroV).
path_via (x ° (ZeroV + ZeroV)).
symmetry;apply semiring_distributes.
path_via (x ° ZeroV). apply ap;apply gid_id.
apply inverse;apply gid_id.
Defined.

Lemma rmult_inverse_right : forall G : semiring, forall x y : G,
 @IsInverse (semiring_add_cmonoid G) x y -> 
forall z,  @IsInverse (semiring_add_cmonoid G) (z°x) (z°y).
Proof.
intros ? ? ? H ?. apply linverse_inverse.
red. apply transport with gidV;[|apply gid_id].
path_via (z ° (x + y)).
path_via (z°ZeroV). symmetry; apply rmult_0_r.
apply ap. apply id_unique; apply _.
apply semiring_distributes.
Defined.

Lemma rmult_inverse_left : forall G : semiring, forall x y : G,
 @IsInverse (semiring_add_cmonoid G) x y -> 
forall z,  @IsInverse (semiring_add_cmonoid G) (x°z) (y°z).
Proof.
intros ? ? ? H ?. apply linverse_inverse.
red. apply transport with gidV;[|apply gid_id]. symmetry; path_via ((x + y)°z).
symmetry;apply semiring_distributes.
path_via (ZeroV°z). apply (ap (fun g => g°z)). apply id_unique;apply _.
apply rmult_0_l.
Defined.

Lemma ropp_rmult_left : forall G : ring, forall x y : G, 
roppV (x°y) = (roppV x)°y.
Proof.
intros. apply group_inverse_gopp.
eapply rmult_inverse_left. apply _.
Defined.

Lemma ropp_rmult_right : forall G : ring, forall x y : G, 
roppV (x°y) = x°(roppV y).
Proof.
intros. apply group_inverse_gopp.
eapply rmult_inverse_right. apply _.
Defined.

Definition isring_sig : forall G : prering, sigT (fun semir : IsSemiring G =>
 forall x : prering_add G, Inverse x) <~> IsRing G.
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

Definition easyIsRing (G : prering) {Hgr : IsGroup (prering_add G)}
 {Hmon : IsMonoid (prering_mult G)} {Hdis : Distributes G} : IsRing G.
Proof.
apply BuildIsRing. apply BuildIsSemiring;apply _.
apply gopp.
Defined.

Lemma intdom_partial_cancels_left : forall {G : integralDomain}
 {Hset : IsHSet G}, forall a : G, ~ a = ZeroV ->
  @Lcancel (prering_mult G) a.
Proof.
intros ? ? ? H. red. fold (@rmult G). intros.
assert (a ° (b + (roppV c)) = ZeroV).
eapply concat.
apply (@semiring_distributes G _). 
pose (@semiring_cancel G). 
apply (@Right_cancel _ _ (c0 (a ° c))).
apply (@concat _ _ (a°b + (a° (roppV c) + a°c))).
simpl. symmetry. apply (@sg_assoc (prering_add G) _).
eapply concat;[|symmetry;apply gid_id].
eapply concat;[|apply X].
eapply concat;[ apply ap | apply gid_id].
eapply concat. symmetry.
apply semiring_distributes.
eapply concat;[apply ap | apply rmult_0_r].
apply id_unique;apply _.
apply (@integral_pr G G) in X0.
eapply minus1Trunc_rect_nondep;[|apply Hset|apply X0];clear X0.
intros [p | p].
destruct H;auto.
assert (Hcan : forall a : prering_add G, Rcancel a). apply _.
apply (Hcan (ropp' c)).
eapply concat. apply p.
symmetry. apply id_unique;apply _.
Defined.

Lemma intdom_partial_cancels_right :forall {G : integralDomain}
 {Hset : IsHSet G}, forall a : G, ~ a = ZeroV ->
  @Rcancel (prering_mult G) a.
Proof.
intros ? ? ? ? ? ? X. apply intdom_partial_cancels_left with a;auto.
eapply concat;[|eapply concat;[apply X|]];apply (@sg_comm (prering_mult G) _).
Defined.

Lemma intdom_partial_cancels : forall {G : integralDomain}
 {Hset : IsHSet G}, forall a : G, ~ a = ZeroV ->
  @Cancel (prering_mult G) a.
Proof.
intros;split;
[apply intdom_partial_cancels_left | apply intdom_partial_cancels_right];
assumption.
Defined.

End Ring_pr.

