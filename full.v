Require Import HoTT minus1Trunc.
Require Export basics nat_struct.
Require Import syntax.
Import Distributive.

(** This file: various results which apply to Q, for use in constructing R **)
(** Later, should split in order to require weaker hypotheses when possible **)

Module FullDecField.
Export Field_pr OrderedMagma_pr OrderedRing.

Section VarSec.

Context {T : Type}.
Variable L : PreringFull T.
Context {Hset : IsHSet T} {Hpr1 : RelationProp (#)}
{Hpr2 : RelationProp (<=)} {Hpr3 : RelationProp (<)}.
Context {Hl : IsFullDecField L}.
Context {Hdec : @Decidable T paths}.

Global Instance fullpseudo : FullPseudoOrder L.
Proof.
split;apply Hl.
Defined.

Global Instance fullposet : FullPoset L.
Proof.
apply fullpseudo_is_fullposet;apply _.
Defined.

Global Instance plus_lt_invariant : IsInvariant (+ <).
Proof.
apply linvariant_invariant. apply _.
red. apply _.
Defined.

Global Instance lt_trans : Transitive (<).
Proof.
apply fullposet.
Defined.

Global Instance plus_lt_compat : IsCompat (+ <).
Proof.
apply invariant_compat;apply _.
Defined.

Global Instance plus_lt_regular : forall z, IsRegular (+ <) z.
Proof.
intros. apply inverse_regular with (roppV z).
unfold gop;apply _. apply _. apply roppP.
Defined.

Global Instance strict_srorder : IsStrictSemiringOrder L.
Proof.
split;try apply Hl.
apply (@pseudo_is_strict T L _). apply _.
intros. apply Hl.
red. apply Hl. assumption.
Defined.

Global Instance plus_apart_invariant : IsInvariant (+ #).
Proof.
apply linvariant_invariant. apply _.
intros z x y. unfold rrel,gop. simpl. intros.
apply (@apart_iff_total_lt T L _).
apply (@apart_iff_total_lt T L _) in X. destruct X;[left|right];
apply plus_lt_invariant;assumption.
Defined.

Global Instance plus_leq_invariant : IsInvariant (+ <=).
Proof.
apply linvariant_invariant. apply _.
hnf. intros z x y.
unfold rrel,gop. simpl.
intros. apply (@le_iff_not_lt_flip T L _). intro H.
apply (@le_iff_not_lt_flip T L _) in X. apply X.
apply plus_lt_regular with z. assumption.
Defined.

Global Instance plus_leq_compat : IsCompat (+ <=).
Proof.
apply invariant_compat.
apply fullposet.
apply _.
Defined.

Lemma plus_lt_leq_lt : forall a b, a < b -> forall c d, c <= d ->
a + c < b+d.
Proof.
intros.
apply (@lt_le_trans T L _) with (b+c).
apply _.
apply plus_lt_invariant. assumption.
apply plus_leq_invariant. assumption.
Defined.

Lemma plus_leq_lt_lt : forall a b, a <= b -> forall c d, c < d ->
a+c < b+d.
Proof.
intros.
apply (@le_lt_trans T L _) with (b+c).
apply _.
(*NB:this simpl makes it go faster*)
simpl;apply plus_leq_invariant. assumption.
apply plus_lt_invariant. assumption.
Defined.

Lemma ropp_lt_flip : forall a b, a < b -> roppV b < roppV a.
Proof.
pose (H := @gopp_rrel_flip T (+ <) _).
simpl in H. unfold rrel in H.
change goppV with roppV in H. apply H. apply plus_lt_invariant.
Defined.

Lemma ropp_apart_flip : forall a b, a # b -> roppV b # roppV a.
Proof.
intros. apply (@apart_iff_total_lt T L _).
apply (@apart_iff_total_lt T L _) in X.
destruct X;[left|right];apply ropp_lt_flip;assumption.
Defined.

Lemma ropp_lt_flip_back : forall a b, roppV b < roppV a -> a < b.
Proof.
intros. pattern a;apply transport with (roppV (roppV a));[|
apply transport with (roppV (roppV b));[|apply ropp_lt_flip;assumption]];
apply gopp_gopp.
Defined.

Lemma ropp_leq_flip : forall a b, a <= b -> roppV b <= roppV a.
Proof.
intros. simpl;apply Hl.
intro H;simpl in X;apply Hl in X. apply X.
apply ropp_lt_flip_back;assumption.
Defined.

Lemma ropp_leq_flip_back : forall a b, roppV b <= roppV a -> a <= b.
Proof.
intros. simpl;apply Hl.
intro H;simpl in X;apply Hl in X. apply X.
apply ropp_lt_flip;assumption.
Defined.

Global Instance plus_leq_regular : forall z, IsRegular (+ <=) z.
Proof.
intros;apply inverse_regular with (roppV z).
unfold gop;apply _.
apply _.
apply roppP.
Defined.

Lemma lt_flip : forall {x y : T}, x < y -> y < x -> Empty.
Proof.
apply Hl.
Defined.

Lemma not_lt_apart_lt_flip : forall {x y : T}, ~ x < y -> x # y -> y < x.
Proof.
intros. apply (@apart_iff_total_lt T L _) in X0.
destruct X0;auto. destruct X;auto.
Defined.

Global Instance pospreserving : IsPosPreserving (+ ° <):= _.

Lemma mult_apart_embed : forall z, ZeroV # z ->
IsEmbedding (#) (#) (mult z).
Proof.
intros z Hz;split.
- hnf;unfold rrel. intros.
  assert (Hb : IsBinRegular (° #)). apply _.
  hnf in Hb. unfold rrel,gop in Hb. simpl in Hb.
  assert (dec_inv z ° (z°x) # dec_inv z ° (z°y)).
  pattern (dec_inv z ° (z°x)). apply transport with x.
  path_via ((dec_inv z ° z) ° x). apply inverse. apply dec_inv_ok.
  intros H;destruct H;apply (@irrefl T (#)) in Hz. assumption.
  apply Hl.
  apply inverse. apply associative. apply Hl.
  apply transport with y.
  path_via ((dec_inv z ° z) ° y). apply inverse. apply dec_inv_ok.
  intros H;destruct H;apply (@irrefl T (#)) in Hz. assumption.
  apply Hl.
  apply inverse. apply associative. apply Hl.
  assumption.
  apply Hb in X0. clear Hb. revert X0.
  apply minus1Trunc_rect_nondep;[|apply Hpr1].
  intros. destruct X0 as [H|H].
  apply (@irrefl T (#) Hl) in H. destruct H.
  assumption.
- hnf. unfold rrel.
  intros.
  assert (Hb : IsBinRegular (° #)). apply _.
  apply Hb in X.
  clear Hb;revert X.
  apply minus1Trunc_rect_nondep;[|apply Hpr1].
  unfold rrel. simpl. intros [H|H].
  apply (@irrefl T (#) Hl) in H. destruct H.
  assumption.
Defined.

Lemma mult_lt_embed_pos : forall z, ZeroV < z ->
IsEmbedding (<) (<) (mult z).
Proof.
assert (forall z : T, ZeroV < z -> IsMorphism lt lt (mult z)).
- intros z Hz;red;unfold gop,rrel;simpl;intros ? ? H.
  apply plus_lt_regular with (roppV (z ° x)).
  unfold gop,rrel. simpl.
  set (X := roppV (z°x) + z°x). pattern X;apply transport with ZeroV;
  unfold X;clear X.
  apply inverse.
  apply (@ropp_l T L _).
  set (X := roppV (z ° x) + z ° y). apply transport with (z ° ((roppV x) + y));
  unfold X;clear X.
  eapply concat. apply ldistributes. apply _.
  apply (@ap T T (fun k:T => k + _)).
  apply inverse. apply (@ropp_rmult_right T L _).
  apply pospreserving. assumption.
  apply plus_lt_regular with x.
  apply transport with y. unfold gop;simpl.
  path_via ((x+roppV x)+y).
  apply inverse. apply roppP.
  apply inverse;apply associative. apply Hl.
  unfold gop,rrel; simpl.
  set (X := x+ZeroV);pattern X;apply transport with x;unfold X;clear X.
  apply inverse;apply (@ZeroP T L _).
  assumption.

- intros z Hz;split. apply X;assumption.
  hnf;unfold rrel.
  intros ? ? H. apply not_lt_apart_lt_flip.
  intros H'. apply (lt_flip H).
  apply X. assumption.
  assumption.
  apply mult_apart_embed with z.
  apply (@apart_iff_total_lt T L _). left;assumption.
  unfold rrel. apply (@apart_iff_total_lt T L _). right;assumption.
Defined.

Lemma ropp_inv : forall x, roppV (dec_inv x) = dec_inv (roppV x).
Proof.
intros. destruct (Hdec ZeroV x) as [H|H];unfold rrel in H.
- destruct H.
  path_via ZeroV.
  eapply concat. apply ap. apply dec_inv0.
  apply ropp_zero.
  apply inverse. eapply concat. apply ap.
  apply ropp_zero. apply dec_inv0.
- apply (@inverse_unicity T (°) _ (roppV x)).
  apply linverse_inverse. red.
  unfold gop. apply transport with OneV.
  eapply concat;[|apply ropp_rmult_right].
  eapply concat;[|apply ap;apply ropp_rmult_left].
  apply inverse. eapply concat. apply gopp_gopp.
  apply (id_unique (°)).
  apply dec_inv_ok. assumption.
  apply One. apply One.

  apply dec_inv_ok. intro H'.
  pose (H0 := ap roppV H'). clearbody H0.
  apply H. eapply concat;[|eapply concat;[apply H0|]].
  symmetry. apply ropp_zero.
  apply gopp_gopp.
Defined.

Lemma mult_lt_embed_neg : forall z, z < ZeroV ->
IsEmbedding (<) (fun x y => y < x) (mult z).
Proof.
split;red; unfold rrel.
- intros.
  apply plus_lt_regular with (roppV (z ° y)).
  unfold gop,rrel;simpl.
  set (Y := roppV (z°y) + z°y). pattern Y;apply transport with ZeroV;unfold Y;
  clear Y.
  apply (id_unique (+)). apply Zero. apply inverse_right. exact (roppP (z°y)).
  apply transport with (roppV z ° (y + roppV x)).
  eapply concat. apply ldistributes. apply _.
  apply ap11;[apply ap|].
  apply inverse;exact (ropp_rmult_left z y).
  eapply concat;[symmetry;apply ropp_rmult_right|].
  eapply concat;[symmetry;apply ap;apply ropp_rmult_left|].
  apply gopp_gopp.

  apply pospreserving;change rrel with lt.
  pattern ZeroV. apply transport with (roppV ZeroV).
  apply ropp_zero.
  apply ropp_lt_flip. assumption.
  apply plus_lt_regular with x.
  unfold gop,rrel. simpl.
  set (Y := x+ZeroV). pattern Y;apply transport with x;unfold Y.
  apply inverse. apply (@Zero T L _).
  apply transport with y.
  path_via ((x + roppV x) + y).
  apply inverse. apply roppP.
  eapply concat. symmetry;apply associative. apply Hl.
  unfold gop;simpl.
  apply ap. apply commutative. apply Hl.
  assumption.

- intros.
  apply ropp_lt_flip in X0.
  rewrite ropp_rmult_left in X0. (* !! rewrite *)
  rewrite ropp_rmult_left in X0.
  apply mult_lt_embed_pos with (roppV z).
  apply ropp_lt_flip_back.
  rewrite ropp_zero;change roppV with goppV. rewrite gopp_gopp.
  assumption.
  assumption.
Qed.

Lemma mult_lt_pos_inverse_pos : forall x, ZeroV < x -> ZeroV < dec_inv x.
Proof.
intros.
apply mult_lt_embed_pos with (x°x).
apply pospreserving;assumption.
unfold rrel.
apply transport with x.
path_via (x °  (x ° dec_inv x)).
apply inverse. apply dec_inv_ok.
intros H;destruct H;apply Hl in X;assumption.
apply associative. apply Hl.
pattern (x ° x ° ZeroV). apply transport with ZeroV.
apply inverse. apply rmult_0_r.
assumption.
Defined.

Lemma mult_lt_neg_inverse_neg : forall x, x < ZeroV -> dec_inv x < ZeroV.
Proof.
intros. apply ropp_lt_flip_back.
pattern (roppV ZeroV). apply transport with ZeroV.
apply inverse. apply ropp_zero.
eapply transport.
symmetry;apply ropp_inv.
apply mult_lt_pos_inverse_pos.
apply ropp_lt_flip_back.
pattern (roppV (roppV x)). apply transport with x.
apply inverse. apply gopp_gopp.
eapply transport. symmetry. apply ropp_zero.
assumption.
Defined.

Lemma dec_inv_neq : forall x, ZeroV != x -> ZeroV != dec_inv x.
Proof.
intros x Hx H'.
generalize (ap (mult (x°x)) H').
intro Hx'.
apply Hx. eapply concat;[|eapply concat;[apply Hx'|]].
apply inverse. apply rmult_0_r.
path_via (x ° (x ° dec_inv x)).
apply inverse. apply associative;apply Hl.
apply dec_inv_ok. assumption.
Defined.

Lemma inv_inv : forall x, dec_inv (dec_inv x) = x.
Proof.
intros.
destruct (Hdec ZeroV x) as [Hx|Hx].
destruct Hx.
eapply concat;[apply ap|];apply dec_inv0.
unfold rrel in Hx.
apply (@inverse_unicity T (°) _ (dec_inv x)).
apply dec_inv_ok. apply dec_inv_neq. assumption.
apply inverse_symm. apply dec_inv_ok. assumption.
Defined.

Global Instance nat_embed_lt : IsEmbedding (<) (<) (nat_embed L).
Proof.
assert (IsMorphism (<) (<) (nat_embed L)).
red. unfold rrel.
assert (forall n, nat_embed L n < nat_embed L (S n)).
intros. pattern (nat_embed L n). apply transport with (ZeroV + nat_embed L n).
apply Zero.
simpl. apply plus_lt_leq_lt. apply fulldecfield_zero_lt_one.
apply fullposet.
intros n m H.
induction H. auto.

apply transitivity with (nat_embed L m).
assumption. apply X.

split;try assumption. red. unfold rrel.
intros. destruct (nat_trichotomic x y) as [?|H]. assumption.
destruct H as [H|H].
destruct H. apply (@irrefl T (<) _) in X0. destruct X0.
apply X in H. unfold rrel in H.
destruct (@pseudoorder_antisym T L _ _ _ X0 H).
Defined.

Global Instance nat_embed_inj : IsReflecting (paths) (paths) (nat_embed L).
Proof.
red;unfold rrel. intros.
destruct (nat_trichotomic x y) as [H|[H|H]];auto;
apply nat_embed_lt in H;unfold rrel in H;destruct X;
apply (@irrefl T (<) _) in H;destruct H.
Defined.

Global Instance nat_embed_apart : IsEmbedding (#) (#) (nat_embed L).
Proof.
split;red;unfold rrel.
intros. apply (@apart_iff_total_lt T L _).
destruct (nat_trichotomic x y) as [H|[H|H]];[left|destruct X;assumption|right];
apply nat_embed_lt;assumption.

intros. intro H. destruct H. apply (@irrefl T (#) Hl) in X. assumption.
Defined.

Global Instance nat_embed_leq : IsEmbedding (<=) (<=) (nat_embed L).
Proof.
split;red;unfold rrel.
intros. induction H.
apply fullposet.
simpl. eapply fullposet. apply IHnle.
change ((fun k => k <= OneV + nat_embed L m) (nat_embed L m)).
apply transport with (ZeroV + nat_embed L m).
apply Zero.
apply plus_leq_compat. apply (@lt_le T L _). apply fulldecfield_zero_lt_one.
apply fullposet.

intros. destruct x. apply nle_0.
change (x < y). apply nat_embed_lt.
unfold rrel.
eapply (@lt_le_trans T L _ _).
apply nat_embed_lt. apply nle_n.
assumption.
Defined.

Global Instance nat_embed_plus : Magma.IsMorphism (+) (+) (nat_embed L).
Proof.
apply _.
Defined.

Global Instance nat_embed_mult : Magma.IsMorphism (°) (°) (nat_embed L).
Proof.
apply _.
Defined.

Lemma mult_cancel : forall x : T, ZeroV != x -> Cancel (°) x.
Proof.
apply @intdom_partial_cancels.
red. intros.
apply min1. destruct (Hdec ZeroV a). left;assumption.
right.
apply (ap (fun k => dec_inv a ° k)) in X.
path_via (dec_inv a ° ZeroV).
apply inverse;apply rmult_0_r.
path_via (dec_inv a ° (a°b)).
path_via ((dec_inv a ° a) ° b).
apply associative. change (Associative (°)). apply _.
apply dec_inv_ok. assumption.
assumption.
Defined.

Section Average.

Definition avg_at (a b : T) (n m : nat) := a +
 nat_embed L m ° ((b + roppV a) ° (dec_inv (nat_embed L n))).

(*
avg_at a b n m := a + m (b-a) / n = (m b + (n-m) a) / n
 = b + ((n-m)a - (n-m)b)/n
 = avg_at b a n (n-m)
NB: only when n-m >= 0: n = m+k
*)

Lemma avg_comm : forall a b : T,
forall m k, 0 != k+m -> avg_at a b (k+m) m = avg_at b a (k+m) k.
Proof.
intros;unfold avg_at.
apply (@right_cancel T (°) (nat_embed L (k+m))).
apply mult_cancel.
apply nat_embed_apart in X. unfold rrel in X.
intro H;destruct H. apply @irrefl in X. assumption. apply fullposet.

unfold gop.
set (K := nat_embed L (k+m)).
path_via (a ° K + nat_embed L m ° (b + roppV a) ° (dec_inv K ° K)).
ssrapply (@ast2_full_semiring T L _); reflexivity.
path_via (a° K + nat_embed L m ° (b + roppV a)).
apply ap. apply dec_inv_ok.
change ZeroV with (nat_embed L 0);unfold K;clear K;intro H.
apply nat_embed_inj in H. auto.
path_via (b ° K + nat_embed L k ° (a + roppV b)).
pattern K. apply transport with (nat_embed L k + nat_embed L m).
unfold K. apply inverse. apply nat_embed_plus.
ssrapply (@ast2_full_semiring T L _). simpl. unfold gop.
apply ap.
path_via (ZeroV + nat_embed L m ° b).
path_via ((a + roppV a) ° nat_embed L m + nat_embed L m ° b).
ssrapply (@ast2_full_semiring T L _);reflexivity.
apply (@ap _ _ (fun k => k + _)).
path_via (ZeroV ° nat_embed L m).
apply (@ap _ _ (fun k : T => k ° _)).
apply ropp_r.
apply rmult_0_l.

apply inverse. path_via ((b + roppV b) ° nat_embed L k + nat_embed L m ° b).
ssrapply (@ast2_full_semiring T L _);reflexivity.
apply (@ap _ _ (fun k => k + _)).
path_via (ZeroV ° nat_embed L k).
apply (@ap _ _ (fun k => k ° _)). apply ropp_r.
apply rmult_0_l.

path_via (b ° K + (nat_embed L k ° (a + roppV b)) ° (dec_inv K ° K)).
apply inverse. apply ap. apply dec_inv_ok.
unfold K;change ZeroV with (nat_embed L 0);intro H.
apply nat_embed_inj in H. auto.
ssrapply (@ast2_full_semiring T L _);reflexivity.
Qed.

Lemma avg_gt : forall a b : T, a < b ->
forall n m, 0 < n -> 0 < m -> a < avg_at a b n m.
Proof.
unfold avg_at.
intros.
Defined.



End Average.


End VarSec.

End FullDecField.
