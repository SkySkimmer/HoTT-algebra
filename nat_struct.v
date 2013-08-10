Require Import HoTT.
Require Import structures basics.

Export Ring_pr Relation_pr OrderedMagma_pr.

Open Scope nat_scope.

Section InstanceScope.

Fixpoint nplus (n m : nat) : nat := match n with
  | S k => S (nplus k m)
  | 0 => m
  end.

Definition npred (n : nat) : nat := match n with
  | S k => k
  | _ => 0
  end.

Lemma S_0_neq : forall n, S n = 0 -> Empty.
Proof.
intros. exact (transport (fun s => match s with
  | 0 => Empty | _ => Unit end) H tt).
Defined.

Definition eq_nat_dec : decidable_paths nat.
Proof.
red.
induction x,y.

- left;reflexivity.

- right. exact (fun H => transport (fun s => match s with
 | 0 => Unit | _ => Empty end) H tt).

- right. exact (fun H => transport (fun s => match s with
 | 0 => Empty | _ => Unit end) H tt).

- destruct (IHx y). left. apply ap;assumption.
  right. intro;apply n.
  exact (ap npred H).
Defined.

Global Instance nat_set : IsHSet nat.
Proof.
apply hset_decidable. exact eq_nat_dec.
Defined.

Canonical Structure nat_add : PlusMagma := BuildMagma nat nplus.

Lemma nplus_0_l : forall n, 0 + n = n.
Proof.
reflexivity.
Defined.

Lemma nplus_S_l : forall n m, (S n) + m = S (n + m).
Proof.
intros;reflexivity.
Defined.

Lemma nplus_0_r : forall n, n + 0 = n.
Proof.
induction n.
reflexivity.
apply (ap S). assumption.
Defined.

Lemma nplus_S_r : forall n m, n + (S m) = S (n + m).
Proof.
induction n;intros. reflexivity.
apply (ap S). apply IHn.
Defined.

Instance nplus_comm : Commutative nat_add.
Proof.
red. induction y. apply nplus_0_r.
unfold gop;simpl. eapply concat;[| apply ap; apply IHy].
apply nplus_S_r.
Defined.

Instance nplus_assoc : Associative nat_add.
Proof.
red. induction x. intros;reflexivity.
intros;unfold gop;simpl. apply ap;apply IHx.
Defined.

Instance nat_add_issg : IsSemigroup nat_add := BuildIsSemigroup _ _ _.

Canonical Structure nat_add_sg : semigroup :=
 BuildSemigroup nat_add _.

Instance n0_is_id : IsId 0.
Proof.
split. intro;reflexivity.
exact nplus_0_r.
Defined.

Canonical Structure nplus_identity : Identity nat_add := BuildIdentity _ _ _.

Instance nat_add_ismono : IsMonoid nat_add := BuildIsMonoid _ _ nplus_identity.

Canonical Structure nat_add_monoid : monoid := 
 BuildMonoid nat_add _.

Instance nplus_left_cancel : forall n : nat, Lcancel n.
Proof.
induction n;red;intros.
assumption.
unfold gop in H;simpl in H. apply IHn.
apply (ap npred H).
Defined.

Instance nplus_right_cancel : forall n : nat, Rcancel n.
Proof.
induction n;red;intros.
eapply concat;[|eapply concat;[apply H|]].
apply inverse;apply nplus_0_r. apply nplus_0_r.
apply IHn.
assert (S (gop b n) = S (gop c n)).
eapply concat. symmetry. apply nplus_S_r. eapply concat. apply H.
apply nplus_S_r.
apply (ap npred X).
Defined.

Instance nplus_cancel : forall n : nat, Cancel n.
Proof.
intros. split;apply _.
Defined.

Instance nat_add_cmono : IsCMonoid nat_add := BuildIsCMonoid _ _ _.

Canonical Structure nat_cmonoid : Cmonoid := 
 BuildCMonoid nat_add _.

Fixpoint nmult (n m : nat) : nat := match n with
  | S k => m + (nmult k m)
  | 0 => 0
  end.

Canonical Structure nat_mult : MultMagma := BuildMagma nat nmult.

Canonical Structure nat_prering : prering :=
 BuildLL_sig nat (BuildLL_Class _ nplus nmult).

Definition nmult_0_l : forall m, 0 ° m = 0 := fun _ => idpath.

Lemma nmult_0_r : forall n, n ° 0 = 0.
Proof.
induction n.
reflexivity.
assumption.
Defined.

Lemma nmult_S_l : forall n m, (S n) ° m = m + (n ° m).
Proof.
intros;reflexivity.
Defined.

Lemma nmult_S_r : forall n m, n ° (S m) = (n ° m) + n.
Proof.
induction n;intros.
reflexivity.
eapply concat;[|symmetry;apply nplus_S_r].
eapply concat;[apply nmult_S_l|].
eapply concat;[apply nplus_S_l|].
apply ap.
eapply concat;[|apply nplus_assoc]. apply ap.
apply IHn.
Defined.

Instance nmult_comm : Commutative nat_mult.
Proof.
red. induction y.
- simpl. apply nmult_0_r.
- simpl. eapply concat. apply nmult_S_r. eapply concat. apply nplus_comm.
  eapply concat;[|symmetry;apply nmult_S_l]. apply ap. assumption.
Defined.

Instance nat_distrib_left : Ldistributes nat_prering.
Proof.
red. induction a;intros.
reflexivity.

eapply concat;[apply nmult_S_l|].
pattern (a ° (b+c)). eapply transport. symmetry;apply IHa.
transitivity (b + (c + (a°b + a°c))).
eapply concat;[ apply nplus_assoc |].
eapply concat;[| symmetry;apply nplus_assoc].
symmetry;apply nplus_assoc.

eapply concat;[| apply nplus_assoc]. apply ap.
eapply concat;[| apply nplus_comm].
eapply concat;[| apply nplus_assoc]. apply ap.
apply nplus_comm.
Defined.

Instance nat_distrib_right : Rdistributes nat_prering.
Proof.
red. intros.
simpl.
eapply concat. apply nmult_comm.
eapply concat. apply nat_distrib_left.
apply ap11;[ apply ap |];apply nmult_comm.
Defined.

Instance nat_distrib : Distributes nat_prering.
Proof.
split;apply _.
Defined.

Instance nmult_assoc : Associative nat_mult.
Proof.
red. induction x;intros;simpl.
reflexivity.
unfold gop;simpl.
eapply concat;[| symmetry;apply nat_distrib].
apply ap. apply IHx.
Defined.


Instance nmult_issg : IsSemigroup nat_mult := BuildIsSemigroup _ _ _.

Canonical Structure nat_mult_sg : semigroup := BuildSemigroup nat_mult _.

Instance nmult_1_l : @Left_id nat_mult 1.
Proof.
red. simpl. apply nplus_0_r.
Defined.

Instance nmult_1_r : @Right_id nat_mult 1.
Proof.
red. intros. eapply concat. apply nmult_comm.
apply nmult_1_l.
Defined.

Instance nmult_1_id : @IsId nat_mult 1.
Proof.
split;apply _.
Defined.

Canonical Structure nmult_identity : Identity nat_mult := BuildIdentity _ _ _.

Instance nmult_ismono : IsMonoid nat_mult := BuildIsMonoid _ _ nmult_identity.

Canonical Structure nat_mult_mono : monoid := BuildMonoid nat_mult _.

Global Instance nat_issemiring : IsSemiring nat_prering.
Proof.
apply BuildIsSemiring;apply _.
Defined.

Canonical Structure nat_semiring : semiring := BuildSemiring nat_prering _.

Lemma nplus_0_0_back : forall n m, n + m = 0 -> (n = 0) * (m = 0).
Proof.
intros.
destruct n. destruct m.
split;reflexivity.
apply Empty_rect.
exact (transport (fun s : nat => match s with
                                  | 0 => Empty
                                  | S _ => Unit
                                  end) H tt).
apply Empty_rect.
exact (transport (fun s : nat => match s with
                                  | 0 => Empty
                                  | S _ => Unit
                                  end) H tt).
Defined.

Lemma nmult_S_0_back : forall n m, mult (S n) m = 0 -> m = 0.
Proof.
intros.
compute in H. apply nplus_0_0_back in H. apply H.
Defined.

Lemma nmult_integral : forall n m, mult n m = 0 -> 
(n = 0) + (m = 0).
Proof.
intros. destruct n. 
- left;reflexivity.
- right;eapply nmult_S_0_back. apply H.
Defined.

Instance nmult_left_cancel : forall n, @Lcancel (prering_mult _) (S n).
Proof.
intros n m;induction m;simpl in *;intros m' H.
assert (X:m' + (n°m') = 0). eapply concat. symmetry;apply H.
apply nmult_0_r.
apply nplus_0_0_back in X. symmetry;apply X.

destruct m'.
assert (X:(S n) ° (S m) = 0). eapply concat. apply H. apply nmult_0_r.
apply nmult_integral in X.
destruct X as [X | X];apply S_0_neq in X;destruct X.

apply ap. apply IHm.
apply nplus_right_cancel with (S n).
simpl.
eapply concat;[|eapply concat;[apply H|]].
symmetry. apply nmult_S_r. apply nmult_S_r.
Defined.

Global Instance nmult_cancel : forall n, @Cancel (prering_mult _) (S n).
Proof.
intro;apply left_cancel_cancel. apply _.
Defined.

Inductive nle (n : nat) : nat -> Type :=
  | nle_n : nle n n
  | nle_S : forall m : nat, nle n m -> nle n (S m).

Definition nlt n := nle (S n).

Canonical Structure nat_RRR : RRR_sig := makeRRR_sig nat neq nle nlt.

Definition nLeq := RRR_to_R2 nat_RRR.
Definition nLt := RRR_to_R3 nat_RRR.

Canonical Structure nat_LLRRR : LLRRR_sig
 := makeLLRRR_sig nat nplus nmult neq nle nlt.

Instance le_refl : IsReflexive nLeq := nle_n.

Lemma le_exists : forall n m : nat, n <= m -> exists k, k + n = m.
Proof.
intros n m H;induction H.
exists 0;reflexivity.
exists (S (projT1 IHnle)).
apply (ap S).
apply projT2.
Defined.

Lemma plus_le : forall n k : nat, n <= k + n.
Proof.
induction k.
apply nle_n.
simpl. apply nle_S. assumption.
Defined.

Definition exists_le : forall n m : nat, (exists k, k + n = m) -> n <= m.
Proof.
intros.
destruct H as [k []].
apply plus_le.
Defined.

Lemma le_exists_le : forall n m H, le_exists n m (exists_le n m H) = H.
Proof.
intros n m H. destruct H as [k []].
simpl. clear m. induction k.
reflexivity.
path_via (le_exists n (S (k + n)) (plus_le n (S k))).
simpl. fold nplus.
change (nplus k n) with (k + n).
rewrite IHk.
simpl. reflexivity.
Defined.

Instance le_antisymm : IsAntisymmetric nLeq.
Proof.
intros n m H H0.
apply le_exists in H. apply le_exists in H0.
destruct H as [k Hk];destruct H0 as [k' Hk'].
destruct k. apply Hk.
destruct k'. symmetry;apply Hk'.
simpl in *.
assert (H : S (k + S (k' + m)) = m).
pattern (S (k' + m)). eapply transport. symmetry;apply Hk'. apply Hk.
assert (H' : (S (S (k+ k'))) + m = 0 + m).
simpl. eapply concat;[|apply H].
unfold rplus;unfold gop;simpl.
apply (ap S). symmetry. eapply concat;[apply nplus_S_r|]. apply ap.
apply nplus_assoc.
apply nplus_right_cancel in H'.
apply S_0_neq in H'. destruct H'.
Defined.

Lemma le_n_back : forall n (H : n <= n), H = nle_n n.
Proof.
assert (H: forall n m (H : n <= m) (p : m = n), transport _ p H = nle_n n).
induction H.
intros. assert (X : p = idpath). apply axiomK_hset. apply _.
pattern p. eapply transport. symmetry. apply X.
simpl. reflexivity.
intros.
assert (H' : n = m). apply le_antisymm. assumption.
destruct p. apply nle_S. apply nle_n.
assert (H0 : 1 + m = 0 + m). simpl. path_via n.
clear H'. apply nplus_right_cancel in H0. apply S_0_neq in H0. destruct H0.

intros. apply (H n n H0 idpath).
Defined.

Lemma le_S_n_n_not : forall n, ~ (S n) <= n.
Proof.
red;intros.
assert (H' : 1 + n = 0 + n).
simpl. apply le_antisymm. assumption.
apply nle_S;apply nle_n.
apply nplus_right_cancel in H'. eapply S_0_neq;apply H'.
Defined.

Lemma le_S_back : forall n m, n <= m -> forall H : n <= S m,
 exists H', H = nle_S _ _ H'.
Proof.
assert (X :forall n m (H : n <= m) m0 (p : m = S m0) (H0 : n <= m0), 
 exists H' : n <= m0, transport _ p H = nle_S _ _ H').
induction H;intros.
apply Empty_rect. apply S_0_neq with 0.
apply nplus_right_cancel with m0. unfold gop;simpl.
apply le_antisymm. pattern (S m0);eapply transport. apply p. assumption.
apply nle_S;apply nle_n.
assert (p' : m = m0). apply (ap npred p). destruct p'.
pattern p. eapply transport. symmetry. apply axiomK_hset. apply _.
simpl. exists H;reflexivity.

intros. apply (X n (S m) H0 m idpath H).
Defined.

Lemma exists_le_exists : forall n m H, exists_le n m (le_exists n m H) = H.
Proof.
intros.
destruct (le_exists n m H).
destruct p.
simpl.
induction x.
simpl.
symmetry;apply le_n_back.
simpl.
simpl in H.

destruct (le_S_back n (x+n) (plus_le _ _) H).
 pattern (plus_le n x). eapply transport. symmetry. apply IHx.
symmetry. apply p.
Defined.

Instance le_exists_isequiv : forall n m, IsEquiv (le_exists n m).
Proof.
intros. apply isequiv_adjointify with (exists_le n m).
red;apply le_exists_le.
red;apply exists_le_exists.
Defined.

Lemma le_equiv_plus : forall n m : nat, (n <= m) <~> (exists k, k + n = m).
Proof.
intros. eapply BuildEquiv. apply _.
Defined.

Instance le_prop : forall n m : nat, IsHProp (n <= m).
Proof.
intros. eapply trunc_equiv'. apply symmetric_equiv.
apply le_equiv_plus.
apply hprop_inhabited_contr. intro X.
apply BuildContr with X. intro Y.
destruct X as [k Hk];destruct Y as [k' Hk'].
assert (p : k = k').
apply nplus_right_cancel with n. path_via m.
apply path_sigma with p.
apply nat_set.
Defined.

Lemma le_0 : forall n, 0 <= n.
Proof.
induction n;constructor;auto.
Defined.

Lemma le_S_S_back : forall n m, S n <= S m -> n <= m.
Proof.
intros. apply le_exists in H. apply exists_le.
destruct H as [k H]. exists k.
assert (X : S (k + n) = S m). path_via (k + S n). symmetry. apply nplus_S_r.
apply (ap npred X).
Defined.

Instance le_trans : IsTransitive nLeq.
Proof.
intros x y z H;revert z;induction H;intros. assumption.
destruct z.
refine (Empty_rect _ (S_0_neq m _)). apply le_antisymm. assumption. apply le_0.
apply le_S_S_back in H0. apply IHnle. apply nle_S. assumption.
Defined.

Lemma lt_not_le : forall n m : nat, n < m -> ~ m <= n.
Proof.
red;intros.
red in H. apply S_0_neq with 0. apply nplus_right_cancel with n.
simpl. apply le_antisymm. eapply le_trans. apply H. assumption.
apply nle_S;apply nle_n.
Defined.

Lemma le_S_S : forall n m, n <= m -> (S n) <= (S m).
Proof.
intros n m H;induction H.
apply nle_n.
apply nle_S;assumption.
Defined.

Definition le_lt_dec : forall n m : nat, (n <= m) + (m < n).
Proof.
  intros n m.
  induction n in m |- *.
  left. apply le_0.
  destruct m.
  right. apply le_S_S. apply le_0.
  destruct (IHn m).
  left. apply le_S_S;assumption.
  right. apply le_S_S;assumption.
Defined.

Lemma not_le_lt : forall n m : nat, ~ m <= n -> n < m.
Proof.
intros.
destruct (le_lt_dec m n). apply Empty_rect;auto.
assumption.
Defined.

Instance le_dec : IsDecidable nLeq.
Proof.
intros n m;destruct (le_lt_dec n m).
left;assumption.
right;apply lt_not_le;assumption.
Defined.

Instance le_linear : IsConstrLinear nLeq.
Proof.
intros n m. destruct (le_lt_dec n m). left;assumption.
right. apply le_trans with (S m). apply nle_S;apply nle_n.
assumption.
Defined.

Global Instance le_total_order : IsConstrTotalOrder nLeq.
Proof.
constructor;[constructor|];apply _.
Defined.

Lemma nlt_iff_nle_neq : forall n m : nat, n<m <-> (n<=m /\ neq n m).
Proof.
intros;split;intros H.
change (nlt n m) in H. apply le_exists in H.
destruct H as [k H].
assert (H' : (S k) + n = m). path_via (k + S n).
path_via (S (k+n)). symmetry. apply nplus_S_r. clear H. destruct H'.
split. apply plus_le.
intro H. change (O+n = S k + n) in H.
apply nplus_right_cancel in H.
eapply S_0_neq. apply inverse;apply H.
destruct H as [H H0].
apply le_exists in H. destruct H as [k H].
destruct k. destruct H0.
assumption.
apply exists_le. exists k.
path_via (S k + n). path_via (S (k+n)). apply nplus_S_r.
Defined.

Lemma nle_iff_nlt_eq : forall n m : nat, n<=m <-> (n<m \/ n=m).
Proof.
intros;split;intros H.
destruct H. right;reflexivity.
left. apply le_S_S. assumption.
destruct H. apply istrans with (S n). apply nle_S. apply nle_n.
assumption.
destruct p;apply nle_n.
Defined.

Lemma nle_iff_not_nlt_flip : forall n m:nat, n<=m <-> ~m<n.
Proof.
intros;split;intro H.
intro H'. eapply lt_not_le;[apply H'|apply H].
destruct (le_lt_dec n m). assumption.
destruct H;assumption.
Defined.







End InstanceScope.

Section nat_to_semiring.

Variable (G : semiring).

Fixpoint nat_embed (n : nat) : prering_plus G := match n with
  | S k => @OneV G + (nat_embed k)
  | 0 => ZeroV
  end.

Instance nat_embed_add_morph : Magma.IsMorphism nat_embed.
Proof.
red. simpl. fold (@rplus G).
induction x;intros.
- symmetry. apply Zero.
- simpl. eapply concat.
  apply ap. apply IHx.
  apply (@associative (prering_plus G) _).
Defined.

Instance nat_embed_mult_morph : @Magma.IsMorphism nat_mult (prering_mult G)
 nat_embed.
Proof.
red. simpl. fold (@rmult G).
unfold gop. simpl.
induction x.
- intros. simpl.
  apply inverse. apply rmult_0_l.
- intros. simpl.
  eapply concat. apply nat_embed_add_morph.
  fold (@rplus G).
  eapply concat. apply ap. apply IHx.
  path_via ((OneV ° nat_embed y) + nat_embed x ° nat_embed y).
  apply (ap (fun g => g + _)).
  apply inverse. apply One.
  apply inverse. apply right_distributes.
Defined.

End nat_to_semiring.




