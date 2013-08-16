Require Import HoTT.
Require Import structures basics.

Export Ring_pr Relation_pr OrderedMagma_pr.
Import minus1Trunc.

Open Scope nat_scope.

(* used to avoid polluting with extra instances
eg left_cancel, right_cancel and cancel when just cancel suffices *)
Section LocalInstances.

Fixpoint nplus (n m : nat) : nat := match n with
  | S k => S (nplus k m)
  | 0 => m
  end.

Definition npred (n : nat) : nat := match n with
  | S k => k
  | _ => 0
  end.

Fixpoint nmult (n m : nat) : nat := match n with
  | S k => nplus m (nmult k m)
  | 0 => 0
  end.

Inductive nle (n : nat) : nat -> Type :=
  | nle_n : nle n n
  | nle_S : forall m : nat, nle n m -> nle n (S m).

Definition nlt n := nle (S n).

Canonical Structure nat_LLRRR : PreringFull nat
 := BuildLLRRR_Class nat nplus nmult neq nle nlt.
Global Existing Instance nat_LLRRR.

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

Instance nplus_comm : Commutative (+).
Proof.
red. induction y. apply nplus_0_r.
unfold gop in *. change (x + S y = S (y+x)).
eapply concat;[| apply ap; apply IHy].
apply nplus_S_r.
Defined.

Instance nplus_assoc : Associative (+).
Proof.
red. induction x. intros;reflexivity.
intros;unfold gop. apply (ap S);apply IHx.
Defined.

Instance nplus_is_sg : IsSemigroup (+). split;apply _. Defined.

Instance n0_is_id : IsId (+) 0.
Proof.
split. intro;reflexivity.
exact nplus_0_r.
Defined.

Canonical Structure nplus_identity : Identity (+) := BuildIdentity _ _ _.
Existing Instance nplus_identity.

Instance nplus_ismono : IsMonoid (+)
 := BuildIsMonoid _ _ nplus_identity.

Instance nplus_left_cancel : forall n : nat, Lcancel (+) n.
Proof.
induction n;red;intros.
assumption.
unfold gop in H;simpl in H. apply IHn.
apply (ap npred H).
Defined.

Instance nplus_right_cancel : forall n : nat, Rcancel (+) n.
Proof.
induction n;red;intros.
eapply concat;[|eapply concat;[apply H|]].
apply inverse;apply nplus_0_r. apply nplus_0_r.
apply IHn.
assert (S (b + n) = S (c + n)).
eapply concat. symmetry. apply nplus_S_r. eapply concat. apply H.
apply nplus_S_r.
apply (ap npred X).
Defined.

Instance nplus_cancel : forall n : nat, Cancel (+) n.
Proof.
intros. split;apply _.
Defined.

Instance nplus_cmono : IsCMonoid (+) := BuildIsCMonoid _ _ _.


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

Instance nmult_comm : Commutative (°).
Proof.
red. induction y.
- simpl. apply nmult_0_r.
- simpl. eapply concat. apply nmult_S_r. eapply concat. apply nplus_comm.
  eapply concat;[|symmetry;apply nmult_S_l]. apply ap. assumption.
Defined.

Instance nat_distrib_left : Ldistributes nat_LLRRR.
Proof.
red. induction a;intros.
reflexivity.

eapply concat;[apply nmult_S_l|].
pattern (a ° (b+c)). eapply transport. symmetry;apply IHa.
path_via (b + (c + (a°b + a°c))).
eapply concat;[ symmetry;apply nplus_assoc |]. apply ap;apply ap.
apply IHa.

eapply concat;[| apply nplus_assoc]. fold nmult. apply ap.
eapply concat;[| apply nplus_comm].
eapply concat;[| apply nplus_assoc]. apply ap.
apply nplus_comm.
Defined.

Instance nat_distrib_right : Rdistributes nat_LLRRR.
Proof.
red. intros.
simpl.
eapply concat. apply nmult_comm.
eapply concat. apply nat_distrib_left.
apply ap11;[ apply ap |];apply nmult_comm.
Defined.

Instance nat_distrib : Distributes nat_LLRRR.
Proof.
split;apply _.
Defined.

Instance nmult_assoc : Associative (°).
Proof.
red. unfold gop. induction x;intros.
reflexivity.
eapply concat;[apply nmult_S_l|].
eapply concat;[| symmetry;apply nat_distrib]. fold nmult.
change nmult with mult.
apply ap. apply IHx.
Defined.


Instance nmult_issg : IsSemigroup (°) := BuildIsSemigroup _ _ _.

Instance nmult_1_l : Left_id (°) 1.
Proof.
red. simpl. apply nplus_0_r.
Defined.

Instance nmult_1_r : Right_id (°) 1.
Proof.
red. intros. eapply concat. apply nmult_comm.
apply nmult_1_l.
Defined.

Instance nmult_1_id : IsId (°) 1.
Proof.
split;apply _.
Defined.

Canonical Structure nmult_identity : Identity (°) := BuildIdentity _ _ _.
Existing Instance nmult_identity.

Instance nmult_ismono : IsMonoid (°) := BuildIsMonoid _ _ nmult_identity.

Global Instance nat_issemiring : IsSemiring nat_LLRRR.
Proof.
apply BuildIsSemiring;apply _.
Defined.

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

Lemma nmult_integral : forall n m, 0 = mult n m ->
(0 = n) + (0 = m).
Proof.
intros n m;intros. destruct n. 
- left;reflexivity.
- right;symmetry;eapply nmult_S_0_back. symmetry;apply H.
Defined.

Instance nmult_strict_integral : IsStrictIntegral nat_LLRRR.
Proof.
red;intros;apply min1;apply nmult_integral;assumption.
Defined.

Instance nmult_left_cancel : forall n, Lcancel (°) (S n).
Proof.
intros n m;induction m;simpl in *;intros m' H.
assert (X:m' + (n°m') = 0). eapply concat. symmetry;apply H.
apply nmult_0_r.
apply nplus_0_0_back in X. symmetry;apply X.

destruct m'.
assert (X:(S n) ° (S m)=0). eapply concat. apply H. apply nmult_0_r.
apply inverse in X;apply nmult_integral in X.
destruct X as [X | X];apply inverse in X;apply S_0_neq in X;destruct X.

apply ap. apply IHm. unfold gop in *.
apply nplus_right_cancel with (S n). unfold gop.
eapply concat;[|eapply concat;[apply H|]].
unfold mult;simpl. change nmult with mult. change nplus with plus.
symmetry. eapply concat. apply ap. apply ap. apply nmult_S_r.
symmetry;eapply concat. apply nplus_S_r. apply (ap S).
symmetry;apply (associative (+) _).
eapply concat. unfold mult;simpl;apply ap;apply ap. apply nmult_S_r.
unfold mult;simpl.
change nplus with plus;change nmult with mult.
eapply concat;[|symmetry;apply nplus_S_r]. apply ap.
apply associative;apply _.
Defined.

Global Instance nmult_cancel : forall n, Cancel ((°)) (S n).
Proof.
intro;apply left_cancel_cancel. apply _.
Defined.

Instance nle_refl : Reflexive (<=) := nle_n.

Lemma nle_exists : forall n m : nat, n <= m -> exists k, k + n = m.
Proof.
intros n m H;induction H.
exists 0;reflexivity.
exists (S (projT1 IHnle)).
apply (ap S).
apply projT2.
Defined.

Lemma nplus_nle : forall n k : nat, n <= k + n.
Proof.
induction k.
apply nle_n.
simpl. apply nle_S. assumption.
Defined.

Definition exists_nle : forall n m : nat, (exists k, k + n = m) -> n <= m.
Proof.
intros.
destruct H as [k []].
apply nplus_nle.
Defined.

Lemma nle_exists_nle : forall n m H, nle_exists n m (exists_nle n m H) = H.
Proof.
intros n m H. destruct H as [k []].
simpl. clear m. induction k.
reflexivity.
path_via (nle_exists n (S (k + n)) (nplus_nle n (S k))).
simpl. fold nplus.
change nplus with plus;simpl.
rewrite IHk.
reflexivity.
Defined.

Instance nle_antisymm : Antisymmetric (<=).
Proof.
intros n m H H0.
apply nle_exists in H. apply nle_exists in H0.
destruct H as [k Hk];destruct H0 as [k' Hk'].
destruct k. apply Hk.
destruct k'. symmetry;apply Hk'.
simpl in *.
assert (H : S (k + S (k' + m)) = m).
pattern (S (k' + m)). eapply transport. symmetry;apply Hk'. apply Hk.
assert (H' : (S (S (k+ k'))) + m = 0 + m).
simpl. eapply concat;[|apply H].
apply (ap S). symmetry. eapply concat;[apply nplus_S_r|]. apply ap.
apply nplus_assoc.
apply nplus_right_cancel in H'.
apply S_0_neq in H'. destruct H'.
Defined.

Lemma nle_n_back : forall n (H : n <= n), H = nle_n n.
Proof.
assert (H: forall n m (H : n <= m) (p : m = n), transport _ p H = nle_n n).
induction H.
intros. assert (X : p = idpath). apply axiomK_hset. apply _.
pattern p. eapply transport. symmetry. apply X.
simpl. reflexivity.
intros.
assert (H' : n = m). apply nle_antisymm. assumption.
destruct p. apply nle_S. apply nle_n.
assert (H0 : 1 + m = 0 + m). simpl. path_via n.
clear H'. apply nplus_right_cancel in H0. apply S_0_neq in H0. destruct H0.

intros. apply (H n n H0 idpath).
Defined.

Lemma nle_S_n_n_not : forall n, ~ (S n) <= n.
Proof.
red;intros.
assert (H' : 1 + n = 0 + n).
simpl. apply nle_antisymm. assumption.
apply nle_S;apply nle_n.
apply nplus_right_cancel in H'. eapply S_0_neq;apply H'.
Defined.

Lemma nle_S_back : forall n m, n <= m -> forall H : n <= S m,
 exists H', H = nle_S _ _ H'.
Proof.
assert (X :forall n m (H : n <= m) m0 (p : m = S m0) (H0 : n <= m0), 
 exists H' : n <= m0, transport _ p H = nle_S _ _ H').
induction H;intros.
apply Empty_rect. apply S_0_neq with 0.
apply nplus_right_cancel with m0. unfold gop.
apply nle_antisymm. pattern (1 + m0);eapply transport. apply p. assumption.
apply nle_S;apply nle_n.
assert (p' : m = m0). apply (ap npred p). destruct p'.
pattern p. eapply transport. symmetry. apply axiomK_hset. apply _.
simpl. exists H;reflexivity.

intros. apply (X n (S m) H0 m idpath H).
Defined.

Lemma exists_nle_exists : forall n m H, exists_nle n m (nle_exists n m H) = H.
Proof.
intros.
destruct (nle_exists n m H).
destruct p.
simpl.
induction x.
simpl.
symmetry;apply nle_n_back.
simpl.
simpl in H.

destruct (nle_S_back n (x+n) (nplus_nle _ _) H).
 pattern (nplus_nle n x). eapply transport. symmetry. apply IHx.
symmetry. apply p.
Defined.

Instance nle_exists_isequiv : forall n m, IsEquiv (nle_exists n m).
Proof.
intros. apply isequiv_adjointify with (exists_nle n m).
red;apply nle_exists_nle.
red;apply exists_nle_exists.
Defined.

Lemma nle_equiv_nplus : forall n m : nat, (n <= m) <~> (exists k, k + n = m).
Proof.
intros. eapply BuildEquiv. apply _.
Defined.

Instance nle_prop : forall n m : nat, IsHProp (n <= m).
Proof.
intros. eapply trunc_equiv'. apply symmetric_equiv.
apply nle_equiv_nplus.
apply hprop_inhabited_contr. intro X.
apply BuildContr with X. intro Y.
destruct X as [k Hk];destruct Y as [k' Hk'].
assert (p : k = k').
apply nplus_right_cancel with n. path_via m.
apply path_sigma with p.
apply nat_set.
Defined.

Lemma nle_0 : forall n, 0 <= n.
Proof.
induction n;constructor;auto.
Defined.

Lemma nle_S_S_back : forall n m, S n <= S m -> n <= m.
Proof.
intros. apply nle_exists in H. apply exists_nle.
destruct H as [k H]. exists k.
assert (X : S (k + n) = S m). path_via (k + S n). symmetry. apply nplus_S_r.
apply (ap npred X).
Defined.

Instance nle_trans : Transitive (<=).
Proof.
intros x y z H;revert z;induction H;intros. assumption.
destruct z.
refine (Empty_rect _ (S_0_neq m _)). apply nle_antisymm. assumption.
apply nle_0.
apply nle_S_S_back in H0. apply IHnle. apply nle_S. assumption.
Defined.

Lemma nlt_not_nle : forall n m : nat, n < m -> ~ m <= n.
Proof.
red;intros.
red in H. apply S_0_neq with 0. apply nplus_right_cancel with n.
simpl. apply nle_antisymm. eapply nle_trans. apply H. assumption.
apply nle_S;apply nle_n.
Defined.

Lemma nle_S_S : forall n m, n <= m -> (S n) <= (S m).
Proof.
intros n m H;induction H.
apply nle_n.
apply nle_S;assumption.
Defined.

Definition nle_nlt_dec : forall n m : nat, (n <= m) + (m < n).
Proof.
  intros n m.
  induction n in m |- *.
  left. apply nle_0.
  destruct m.
  right. apply nle_S_S. apply nle_0.
  destruct (IHn m).
  left. apply nle_S_S;assumption.
  right. apply nle_S_S;assumption.
Defined.

Lemma not_nle_nlt : forall n m : nat, ~ m <= n -> n < m.
Proof.
intros.
destruct (nle_nlt_dec m n). apply Empty_rect;auto.
assumption.
Defined.

Instance nle_dec : Decidable (<=).
Proof.
intros n m;destruct (nle_nlt_dec n m).
left;assumption.
right;apply nlt_not_nle;assumption.
Defined.

Instance nle_linear : ConstrLinear (<=).
Proof.
intros n m. destruct (nle_nlt_dec n m). left;assumption.
right. apply nle_trans with (S m). apply nle_S;apply nle_n.
assumption.
Defined.

Global Instance nle_total_order : ConstrTotalOrder (<=).
Proof.
constructor;[constructor|];apply _.
Defined.

Lemma nlt_iff_nle_neq : forall n m : nat, n<m <-> (n<=m /\ neq n m).
Proof.
intros;split;intros H.
change (nlt n m) in H. apply nle_exists in H.
destruct H as [k H].
assert (H' : (S k) + n = m). path_via (k + S n).
path_via (S (k+n)). symmetry. apply nplus_S_r. clear H. destruct H'.
split. apply nplus_nle.
intro H. change (O+n = S k + n) in H.
apply nplus_right_cancel in H.
eapply S_0_neq. apply inverse;apply H.
destruct H as [H H0].
apply nle_exists in H. destruct H as [k H].
destruct k. destruct H0.
assumption.
apply exists_nle. exists k.
path_via (S k + n). path_via (S (k+n)). apply nplus_S_r.
Defined.

Lemma nle_iff_nlt_eq : forall n m : nat, n<=m <-> (n<m \/ n=m).
Proof.
intros;split;intros H.
destruct H. right;reflexivity.
left. apply nle_S_S. assumption.
destruct H. apply transitivity with (S n). apply nle_S. apply nle_n.
assumption.
destruct p;apply nle_n.
Defined.

Lemma nle_iff_not_nlt_flip : forall n m:nat, n<=m <-> ~m<n.
Proof.
intros;split;intro H.
intro H'. eapply nlt_not_nle;[apply H'|apply H].
destruct (nle_nlt_dec n m). assumption.
destruct H;assumption.
Defined.

Instance nle_nplus_linvariant : IsLInvariant (+ <=).
Proof.
red;red. unfold gop;unfold rrel. simpl.
simpl.
intros. apply exists_nle. apply nle_exists in H.
destruct H as [k []]. exists k.
path_via ((k+z)+x). apply associative;apply _.
path_via ((z+k)+x). apply (ap (fun g => g + _)). apply commutative;apply _.
symmetry;apply associative;apply _.
Defined.

Global Instance nplus_nle_invariant : IsInvariant (+ <=).
Proof.
apply linvariant_invariant; apply _.
Defined.

Global Instance nplus_nle_compat : IsCompat (+ <=).
Proof.
apply invariant_compat; apply _.
Defined.

Global Instance nplus_nle_regular : forall z, IsRegular (+ <=) z.
Proof.
assert (forall z, IsLRegular (+ <=) z). red;red.
unfold rrel;unfold gop;simpl.
intros ? ? ? H.
apply nle_exists in H;apply exists_nle.
destruct H as [k H].
exists k. apply nplus_cancel with z.
path_via (k + (z+x)).
path_via ((z+k)+x). apply associative;apply _.
path_via ((k+z)+x). apply (ap (fun g => g + _)). apply commutative;apply _.
symmetry;apply associative;apply _.

intros;split. apply _.
red;red.
intros. apply H with z.
unfold gop;simpl.
apply (@transport _ (fun k => k ~> z+y) (x+z)).
apply commutative;apply _.
apply (@transport _ (fun k => _ ~> k) (y+z)).
apply commutative;apply _.
assumption.
Defined.

Lemma not_nlt_nle : forall n m : nat, ~ n < m -> m <= n.
Proof.
intros.
destruct (nle_nlt_dec m n). assumption.
destruct X;assumption.
Defined.

Lemma nlt_nle : forall n m : nat, n < m -> n <= m.
Proof.
intros. apply nle_trans with (S n). apply nle_S;apply nle_n.
assumption.
Defined.

Global Instance nat_trichotomic : Trichotomic nat_LLRRR.
Proof.
red. intros.
destruct (nle_nlt_dec y x). right. destruct (nle_nlt_dec x y).
left. apply nle_antisymm;assumption.
right;assumption.
left;assumption.
Defined.

Global Instance nat_fullpseudoorder : FullPseudoOrder nat_LLRRR.
Proof.
split.
split.
apply neq_apart. apply eq_nat_dec.
intros;apply iff_refl.
intros. apply nlt_not_nle in H0. apply H0.
apply nlt_nle. assumption.

red. unfold rrel. intros. apply min1.
destruct (nle_nlt_dec z x).
destruct (nle_nlt_dec y z).
apply nlt_not_nle in H. destruct H. apply nle_trans with z;assumption.
right;assumption.
left;assumption.

intros. split;intro H.
destruct (nat_trichotomic x y) as [H' | [H' | H']];auto.
destruct H;assumption.
intro H'. destruct H'.
destruct H as [H|H];apply nlt_iff_nle_neq in H;apply H;reflexivity.

intros. split.
intros H H';eapply nlt_not_nle;eauto.
apply not_nlt_nle.
Defined.

Lemma nle_not_nlt : forall n m : nat, n <= m -> ~ m < n.
Proof.
intros ? ? H H'. eapply nlt_not_nle.
apply H'. apply H.
Defined.

Lemma nle_n_S_n : forall n : nat, n <= S n.
Proof.
intros;apply nle_S;apply nle_n.
Defined.

Global Instance nat_fullpseudo : FullPseudoOrder nat_LLRRR.
Proof.
split;try apply _.

split. apply nle_not_nlt.
apply not_nlt_nle.
Defined.

End LocalInstances.

Section nat_to_semiring.

Context {A:Type}.
Variable (L : Prering A).
Context {Hg : IsSemiring L}.

Fixpoint nat_embed (n : nat) : A := match n with
  | S k => OneV + (nat_embed k)
  | 0 => ZeroV
  end.

Global Instance nat_embed_add_morph : Magma.IsMorphism (+) (+) nat_embed.
Proof.
red.
induction x;intros.
- symmetry. apply Zero.
- simpl. eapply concat.
  apply ap. apply IHx.
  apply (@associative _ (+) _).
Defined.

Global Instance nat_embed_mult_morph : Magma.IsMorphism (°) (°) nat_embed.
Proof.
red.
induction x.
- intros. simpl.
  apply inverse. apply rmult_0_l.
- intros. unfold gop. simpl.
  eapply concat. apply nat_embed_add_morph.
  eapply concat. apply ap. apply IHx.
  path_via ((OneV ° nat_embed y) + nat_embed x ° nat_embed y).
  unfold gop.
  apply (@ap _ _ (fun g => g + (nat_embed x ° nat_embed y)) (nat_embed y)).
  apply inverse. apply One.
  apply inverse. apply rdistributes;apply _.
Defined.

End nat_to_semiring.




