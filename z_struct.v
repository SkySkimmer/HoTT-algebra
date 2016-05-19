Require Import HoTT.

Require Import quotient.
Require Import syntax.
Require Import nat_struct.
Require Import cmono_group.
Require Import hit.minus1Trunc.
Require Import hit.unique_choice.

Import Distributive.

Lemma prod_eq_dec : forall A (Ha : DecidablePaths A) B (Hb : DecidablePaths B),
DecidablePaths (A*B).
Proof.
intros.
intros [a b] [c d].
destruct (Ha a c) as [? | H]. destruct (Hb b d) as [? | H].
left. apply ap11;[apply ap|];assumption.
right;intro Hn. apply H;apply (ap snd Hn).
right;intro Hn. apply H;apply (ap fst Hn).
Defined.



Module Relative.
Import GroupOfCMono.

Definition Z := @quotU nat (+).
Instance ZPrering : PreringFull Z.
Proof.
split.
apply (@quotOp nat plus _).
apply (LL_L2 _ (quotPrering nat_LLRRR)).
apply (@quotRel nat (nat_LLRRR:(PlusApart nat))).
apply (@quotRel nat (nat_LLRRR:(PlusLeq nat))).
apply (@quotRel nat (nat_LLRRR:(PlusLt nat))).
Defined.

Instance ZRing : IsRing ZPrering.
Proof.
unfold ZPrering.
change (IsRing (quotPrering nat_LLRRR)).
apply _.
Defined.

Definition z0 := (@ZeroV Z ZPrering ZRing).
Definition z1 := (@OneV Z ZPrering ZRing).

Instance zLeq_prop : @RelationProp Z (<=).
Proof.
red;apply _.
Defined.

Instance zLeq_dec : @Decidable Z (<=).
Proof.
unfold ZPrering. unfold leq. simpl.
apply (@quotrel_dec _ (nat_LLRRR:(PlusLeq nat)));try apply _;simpl.
exact nle_prop.
apply nplus_nle_invariant.
apply nplus_nle_regular.
apply nle_dec.
Defined.

Instance zLeq_total_order : @ConstrTotalOrder Z (<=).
Proof.
split.
apply (@quotrel_poset _ (nat_LLRRR:PlusLeq nat));try apply _.
exact nle_prop. apply nplus_nle_invariant.
apply nplus_nle_regular.
apply nle_total_order.
apply dec_linear_constrlinear. apply _.
apply (@quotrel_linear _ (nat_LLRRR:PlusLeq nat)).
apply constrlinear_linear. apply nle_total_order.
Defined.

Definition zIn : nat*nat -> Z := quotIn (+).

Definition zEquiv : Rel (nat*nat) := equivU (+).

Instance ZRing_set : IsHSet Z := _.

Instance zEquiv_prop : RelationProp zEquiv.
Proof.
red;apply _.
Defined.

Definition z_rect : forall (P : Z -> Type) 
(dclass : forall m n, P (zIn (m, n))),
(forall a b a' b' (Hequiv : zEquiv (a,b) (a',b')),
 transport _ (@related_classes_eq _ zEquiv _ _ Hequiv) (dclass a b)
   = (dclass a' b')) ->
forall z, P z.
Proof.
intros P dclass H.
apply quotU_rect with (fun p => match p as p' return (P (quotIn (+) p'))
 with | (a,b) => dclass a b end).
intros.
destruct x, y.
apply H.
Defined.

Definition z_rect' : forall (P : Z -> Type) 
(dclass : forall x, P (zIn x)),
(forall a b (Hequiv : zEquiv a b),
 transport _ (@related_classes_eq _ zEquiv _ _ Hequiv) (dclass a)
   = (dclass b)) ->
forall z, P z.
Proof.
apply quotU_rect.
Defined.

Definition z_ind : forall (P : Z -> Type),
(forall a b, IsHProp (P (zIn (a, b)))) ->
(forall a b, P (zIn (a, b))) ->
forall z, P z.
Proof.
intros P Hp Hd. apply quotU_ind.
apply quotU_ind. intros;apply _.
intros [a b]. apply Hp.
simpl. intros [a b];apply Hd.
Defined.

Definition z_ind' : forall P : Z -> Type,
(forall x, IsHProp (P (zIn x))) ->
(forall x, P (zIn x)) ->
forall z, P z.
Proof.
intros P Hp Hd. apply quotU_ind.
apply quotU_ind. intros;apply _.
apply _.
apply Hd.
Defined.

Definition z_ind_contr : forall (P : Z -> Type),
(forall a b, Contr (P (zIn (a, b)))) ->
forall z, Contr (P z).
Proof.
intros P Hd. apply quotU_rect with
 (fun p => match p as p' return (Contr (P (quotIn (+) p'))) with
   | (a,b) => Hd a b end).
intros.
apply hprop_contr.
Defined.

Lemma z_rect_compute : forall (P : Z -> Type)
(dclass : forall m n, P (zIn (m, n))) H a b,
 z_rect P dclass H (zIn (a, b)) = dclass a b.
Proof.
intros. reflexivity.
Defined.

Section NotaSec.
Notation "[ a , b ]" := (zIn (a, b)).

Definition z0_class : [0, 0] = z0 := idpath.
Definition z1_class : [S 0, 0] = z1 := idpath.

Lemma zEquiv_eval : forall a b c d, zEquiv (a,b) (c,d) = (a+d = c+b).
Proof.
intros;reflexivity.
Defined.

Definition zplus_eval : forall a b c d, 
[a,b] + [c,d] = [a+c, b+d].
Proof.
intros. reflexivity.
Defined.

Definition zmult_eval : forall a b c d, 
[a,b] ° [c,d] = [a°c + b°d, a°d + c°b].
Proof.
intros;reflexivity.
Defined.

Definition zOpp : forall x : Z, Inverse (+) x := ropp.
Definition zOppV : Z -> Z := fun x => inverse_val (zOpp x).
Global Instance zOppP : forall x : Z, IsInverse (+) x (zOppV x) := _.

Lemma zOpp_eval : forall a b, zOppV [a, b] = [b, a].
Proof.
intros;reflexivity.
Defined.

Lemma z_related_classes_eq : forall a b c d, zEquiv (a,b) (c,d) -> 
[a, b] = [c, d].
Proof.
intros ? ? ? ?. apply related_classes_eq.
Defined.

Lemma z_classes_eq_related : forall a b, zIn a = zIn b -> 
zEquiv a b.
Proof.
apply classes_eq_related.
Defined.

(*
Definition zCanon (z : Z) (x : nat*nat) :=
 (z = zIn x) * minus1Trunc (fst x = 0 \/ snd x = 0).

Definition is_zCanon : forall x, (fst x = 0 \/ snd x = 0) ->
 zCanon (zIn x) x := fun x H => (idpath , min1 H).

Definition zCanon_or : forall z x, zCanon z x -> (fst x = 0 \/ snd x = 0).
Proof.
intros ? ? H.
destruct (eq_nat_dec (fst x) 0) as [? | H']. left. assumption.
right.
eapply minus1Trunc_rect_nondep;[| |apply H].
intros H0. destruct H0. destruct H';assumption. assumption.
apply nat_set.
Defined.

Global Instance zCanon_prop : forall z x, IsHProp (zCanon z x).
Proof.
intros. apply @trunc_prod. apply hprop_allpath;apply quotient_is_set.
apply minus1Trunc_is_prop.
Defined.

Lemma zCanon_atmost : forall z, atmost1P (zCanon z).
Proof.
intros. red. intros [xa xb] [ya yb] Hx Hy.
assert (Heq : quotIn (+) (xa, xb) = quotIn (+) (ya, yb)). path_via z.
symmetry;apply Hx. apply Hy.
apply zCanon_or in Hx;apply zCanon_or in Hy.
simpl in Hx,Hy.
clear z.
apply z_classes_eq_related in Heq. red in Heq;red in Heq;simpl in Heq.
destruct Hx as [Hx | Hx];destruct Hy as [Hy | Hy];
apply inverse in Hx;apply inverse in Hy;destruct Hx,Hy.
apply ap. symmetry. assumption.
symmetry in Heq.
apply nplus_0_0_back in Heq;destruct Heq as [[] []];reflexivity.
apply nplus_0_0_back in Heq;destruct Heq as [[] []];reflexivity.
apply (ap (fun g => (g, 0))).
path_via (xa + 0). apply inverse. apply nplus_0_r.
path_via (ya + 0). apply nplus_0_r.
Defined.

Global Instance zCanonT_prop : forall z, IsHProp (sigT (zCanon z)).
Proof.
intros. apply hprop_inhabited_contr.
intro X. exists X. intro Y.
destruct X as [x Hx];destruct Y as [y Hy].
apply path_sigma with (zCanon_atmost _ _ _ Hx Hy).
apply zCanon_prop.
Defined.

Definition canonT : forall z, sigT (zCanon z).
Proof.
apply z_ind. apply _.
intros.
destruct (nle_linear a b) as [H | H];apply nle_exists in H;destruct H as [k []].
exists (0, k). split.
apply z_related_classes_eq. red;red. simpl.
path_via (k + a). apply commutative;apply nat_issemiring.
apply min1. left;reflexivity.
exists (k,0). split.
apply z_related_classes_eq;red;red;simpl. apply nplus_0_r.
apply min1;right;reflexivity.
Defined.

(*
!!Does not compute!!
Because canonT uses the axiom z_related_classes_eq
*)
Definition z_canon_rect : forall P : Z -> Type,
(forall a, P [a, 0]) -> 
(forall b, P [0, b]) ->
forall z, P z.
Proof.
intros ? H H' ?.
destruct (canonT z) as [x Hc].
eapply transport. symmetry;apply (fst Hc).
apply zCanon_or in Hc. destruct x as [a b];simpl in Hc;destruct Hc as [He | He];
apply inverse in He;destruct He;eauto.
Defined.

Lemma Z_repr : forall x : Z, exists p, zIn p = x.
Proof.
apply z_canon_rect;intros;econstructor;reflexivity.
Defined.

*)

Definition eq_z_dec : DecidablePaths Z.
Proof.
red.
assert (forall x y : Z, IsHProp ((x=y) \/ ~ x=y)).
intros. apply hprop_sum. intros;auto.
apply (z_ind' (fun x => forall y, _) _).
intro x. apply z_ind'. apply _.
intro y.

destruct (eq_nat_dec (fst x + snd y) (fst y + snd x)) as [H|H].
left. apply related_classes_eq. assumption.
right;intro H'. apply H.
apply classes_eq_related in H'. assumption.
Defined.

Lemma zLeq_repr : forall x y, zIn x <= zIn y -> quotRelU (+ <=) x y.
Proof.
apply quotRel_repr;try apply _.
exact nle_prop.
apply nplus_nle_invariant.
apply nplus_nle_regular.
Defined.

Lemma repr_zLeq : forall x y, quotRelU (+ <=) x y -> zIn x <= zIn y.
Proof.
apply repr_quotRel.
Defined.


Lemma zApart_repr : forall x y, zIn x # zIn y ->
 quotRelU (+ #) x y.
Proof.
apply quotRel_repr;try apply _.
red;red. unfold rrel;unfold gop;simpl.
intros ? ? ? H H'.
apply H. apply nplus_cancel with z. assumption.
red;red. unfold rrel;unfold gop;simpl.
intros z x y H H'. apply H. destruct H'. reflexivity.
Defined.

Global Instance zApart_prop : @RelationProp Z (#).
Proof.
red;apply _.
Defined.

Global Instance zApart_trivial : @TrivialApart Z (#).
Proof.
red.
assert (forall x y : Z, x#y -> x!=y).
apply (z_ind (fun x => forall y, _ -> _) _).
intros a b. apply (z_ind (fun y => _->_) _).
intros c d.
intros H.
red in H;simpl in H. apply zApart_repr in H.
simpl in H. unfold gop in H.
intro H'.
apply z_classes_eq_related in H'. red in H';red in H';simpl in H'.
auto.

assert (forall x y : Z, x!=y -> x#y).
apply (z_ind (fun x => forall y, _ -> _) _).
intros a b;apply (z_ind (fun y => _ -> _) _).
intros c d.
intros H.
apply repr_quotRel. simpl.
unfold gop;simpl;intro H'.
apply H. apply related_classes_eq. assumption.

intros;split;auto.
Defined.

Global Instance zApart_apart : @Apartness Z apart.
Proof.
apply neq_apart. apply eq_z_dec.
apply zApart_trivial.
Defined.


Lemma zLt_repr : forall x y, (zIn x) < (zIn y) -> 
 quotRelU (+ <) x y.
Proof.
apply quotRel_repr;try apply _.
intros x y. apply nle_prop.
red;red. unfold rrel. simpl. unfold gop. change lt with (fun x => leq (S x)).
simpl.
intros z x y H. pattern (S (@plus nat nplus z x)).
apply transport with (z + (S x)). apply nplus_S_r.
apply nplus_nle_invariant;assumption.
red;red. unfold gop;unfold rrel. simpl.
intros z x y H. apply (nplus_nle_regular z). unfold gop;unfold rrel.
simpl. pattern (@plus _ nplus z (S x)). eapply transport;[|apply H].
symmetry. apply nplus_S_r.
Defined.

Lemma repr_zLt : forall x y, quotRelU (+ <) x y -> (zIn x) < (zIn y).
Proof.
apply repr_quotRel.
Defined.

Global Instance zApart_dec : @Decidable Z (#).
Proof.
intros x y.
destruct (eq_z_dec x y).
right. intro H'.
apply zApart_trivial in H'. auto.
left. apply zApart_trivial. assumption.
Defined.


Lemma zLt_iff_not_zLeq : forall x y : Z, x < y <-> ~ y <= x.
Proof.
split;revert y;revert x;
apply (z_ind' (fun x => forall y, _ -> _) _);
intro x;apply (z_ind' (fun y => _ -> _) _);
intro y;
intros H.

- intros H'.
  apply zLt_repr in H;apply zLeq_repr in H'.
  simpl in H,H'.
  eapply nlt_not_nle;[apply H|apply H'].

- apply repr_zLt. apply not_nle_nlt. intro H'.
  apply H;apply repr_zLeq. assumption.
Defined.

Lemma zLeq_by_not : forall {x y : Z}, ~ y <= x -> x <= y.
Proof.
intros. destruct (isconstrlinear x y). assumption. destruct X;assumption.
Defined.

Instance zLt_trans : Transitive (<).
Proof.
apply (@quotrel_trans nat (+ <));try apply _.
intros x y. apply nle_prop.
red;red. unfold rrel. simpl. unfold gop. change lt with (fun x => leq (S x)).
simpl.
intros z x y H. pattern (S (@plus nat nplus z x)).
apply transport with (z + (S x)). apply nplus_S_r.
apply nplus_nle_invariant;assumption.
red;red. unfold gop;unfold rrel. simpl.
intros z x y H. apply (nplus_nle_regular z). unfold gop;unfold rrel.
simpl. pattern (@plus _ nplus z (S x)). eapply transport;[|apply H].
symmetry. apply nplus_S_r.

unfold rrel. simpl.
assert (@RelationProp nat lt). intros x y. apply nle_prop.
apply (@fullpseudo_is_fullposet _ _ _ nat_fullpseudo).
Defined.

Instance zLt_irrefl : Irreflexive (<).
Proof.
red. apply (z_ind (fun x => _ -> _) _).
intros a b. intros. apply zLt_repr in H.
apply nlt_not_nle in H. apply H. apply nle_n.
Defined.

Global Instance zLt_trichotomic : @Trichotomic Z (<).
Proof.
apply quotrel_trichotomic;try apply _.

intros x y. apply nle_prop.
red;red. unfold rrel. simpl. unfold gop. change lt with (fun x => leq (S x)).
simpl.
intros z x y H. pattern (S (@plus nat nplus z x)).
apply transport with (z + (S x)). apply nplus_S_r.
apply nplus_nle_invariant;assumption.
red;red. unfold gop;unfold rrel. simpl.
intros z x y H. apply (nplus_nle_regular z). unfold gop;unfold rrel.
simpl. pattern (@plus _ nplus z (S x)). eapply transport;[|apply H].
symmetry. apply nplus_S_r.

apply (@pseudo_is_strict nat nat_LLRRR). intros x y;apply nle_prop.
apply nat_fullpseudo.
Defined.

Global Instance z_fullpseudoorder : FullPseudoOrder ZPrering.
Proof.
split. split.
apply _.
intros. apply zLt_irrefl with x.
apply zLt_trans with y;assumption.

red. unfold rrel.
intros ? ? H ?.
apply min1. destruct (zLt_trichotomic x z) as [?|[p|H']].
left;assumption. right; destruct p;assumption.
right;eapply zLt_trans. apply H'. apply H.

split;intro H.
destruct (zLt_trichotomic x y) as [H'|H'].
left;assumption.
right. destruct H'. destruct p. apply zApart_apart in H. destruct H.
assumption.
apply zApart_trivial. intro H';destruct H';destruct H as [H|H];
eapply zLt_irrefl;apply H.

split;revert y;revert x.
apply (z_ind' (fun x => forall y, _ -> _) _).
intro x. apply (z_ind' (fun y => _ -> _) _).
intro y.
intros H H';apply zLeq_repr in H;apply zLt_repr in H'.
eapply nle_not_nlt;[apply H|apply H'].

apply (z_ind' (fun x => forall y, _ -> _) _).
intro x. apply (z_ind' (fun y => _ -> _) _).
intro y.
intros H. apply repr_zLeq. apply not_nlt_nle. intro H'.
apply H. apply repr_zLt. assumption.
Defined.

Definition zNat : nat -> Z := fun n => zIn (n, 0).

Definition zNat_quotEmbed : zNat = quotEmbed _ := idpath.

Global Instance zNat_leq_embedding : IsEmbedding (<=) (<=) zNat.
Proof.
split.
red. unfold rrel.
intros;apply repr_quotRel. simpl. change (@gidV nat _ _) with (@ZeroV nat _ _).
unfold gop.
pattern (@plus _ nplus x 0). apply transport with x.
apply inverse. apply nplus_0_r.
apply transport with y.
apply inverse. apply nplus_0_r.
assumption.

red. unfold rrel.
intros. apply zLeq_repr in H.
red in H. simpl in H. unfold gop,rrel in H.
pattern x;apply transport with (x+0).
apply nplus_0_r.
apply transport with (y+0).
apply nplus_0_r.
assumption.
Defined.

(*Nb: means zNat is injective*)
Global Instance zNat_eq_embedding : IsEmbedding (paths) (paths) zNat.
Proof.
split.
red. unfold rrel.
apply ap.

red. unfold rrel.
intros. apply classes_eq_related in H.
red in H. simpl in H.
path_via (x+0). apply inverse;apply nplus_0_r.
path_via (y+0). apply nplus_0_r.
Defined.

Global Instance zNat_neq_embedding : IsEmbedding (#) (#) zNat.
Proof.
split;red;unfold rrel.
intros. apply zApart_trivial. intro H.
apply X. apply zNat_eq_embedding. assumption.

intros;intro H.
apply zApart_repr in X. apply X.
simpl. path_via x.
apply nplus_0_r.
path_via y. apply inverse;apply nplus_0_r.
Defined.

Lemma zLt_iff_zLeq_S : forall x y : Z, x < y <-> z1+x <= y.
Proof.
split;revert y;revert x.
apply (z_ind' (fun x => forall y, _ -> _) _).
intro x. apply (z_ind' (fun y => _ -> _) _).
intro y.
intros H.
change (z1 + zIn x) with (zIn (1%nat + fst x, snd x)).
apply repr_zLeq.
red. simpl. unfold rrel,gop.
change (fst x + snd y < fst y + snd x).
apply zLt_repr in H. assumption.

apply (z_ind' (fun x => forall y, _ -> _) _).
intro x. apply (z_ind' (fun y => _ -> _) _).
intro y.
intros H.
apply repr_zLt. red. unfold gop,rrel.
change (fst (1%nat + fst x, snd x) + snd y <= fst y + snd (1%nat + fst x, snd x)).
apply zLeq_repr.
apply H.
Defined.

Global Instance zNat_lt_embedding : IsEmbedding (<) (<) zNat.
Proof.
split;red;unfold rrel,gop.
intros ? ? H. apply zLt_iff_zLeq_S. change (zNat (1%nat+x) <= zNat y).
apply zNat_leq_embedding. assumption.

intros. apply zLt_iff_zLeq_S in H.
change (1%nat+x <= y). apply zNat_leq_embedding. assumption.
Defined.

Global Instance zNat_plus_morphism : Magma.IsMorphism (+) (+) zNat.
Proof.
eapply transport. symmetry;apply zNat_quotEmbed.
apply quotEmbed_morphism.
Defined.

Global Instance zNat_mult_morphism : Magma.IsMorphism (°) (°) zNat.
Proof.
red;unfold gop.
intros.
apply (ap (class_of _)).
unfold multU. simpl.
change (0 ° 0) with 0.
apply path_prod';apply inverse.
apply nplus_0_r.
path_via (0+0).
apply ap11;[apply ap|];apply nmult_0_r.
Defined.

Global Instance exists_zNat_is_prop : forall z, IsHProp (exists n, zNat n = z).
Proof.
intros. apply hprop_allpath.
intros [n Hn] [m Hm].
destruct Hn.
assert (p:m = n). apply zNat_eq_embedding. assumption.
apply path_sigma' with (inverse p).
apply ZRing_set.
Defined.

Lemma zPlus_0_r : forall x, x + z0 = x.
Proof.
apply right_id. apply id_is_right. apply (@ZeroP Z ZPrering ZRing).
Defined.

Lemma zLeq_exists : forall x y : Z, x <= y <~> exists n, zNat n = y + (zOppV x).
Proof.
intros;apply equiv_iff_hprop;revert y;revert x;
apply (z_ind' (fun x => forall y, _ -> _) _);intro x;
apply (z_ind' (fun y => _ -> _) _);intro y;intro H.

apply zLeq_repr in H. simpl in H. apply nle_exists in H.
exists (H.1). destruct H as [k H].
unfold gop in H. simpl.
apply (@right_cancel Z (+) (zIn x) _). unfold gop.
path_via (zIn y).
apply related_classes_eq. red. simpl. unfold gop.
change (0 + snd x) with (snd x).
eapply concat;[|apply H]. apply inverse;apply associative.
 apply nat_issemiring.
path_via (zIn y + (zOppV (zIn x) + zIn x)).
path_via (zIn y + z0).
apply inverse. apply zPlus_0_r.
apply ap.
apply (id_unique (+)). apply Zero.
apply (zOppP (zIn x)).
apply associative. apply ZRing.

apply repr_zLeq. red;simpl. unfold gop,rrel.
apply exists_nle. exists (H.1).
destruct H as [k H].
simpl.
change (zNat k = zIn (fst y + snd x, snd y + fst x)) in H.
apply classes_eq_related in H.
red in H. simpl in H. unfold gop in H.
path_via (k + (snd y + fst x)).
apply ap. apply commutative. apply nat_issemiring.
etransitivity. apply H.
apply nplus_0_r.
Defined.

Lemma z0_z1_apart : z0 # z1.
Proof.
apply repr_quotRel.
red;simpl. unfold rrel.
intro H;apply inverse in H;apply S_0_neq in H;assumption.
Defined.

Lemma z0_z1_neq : z0 != z1.
Proof.
apply zApart_trivial. apply z0_z1_apart.
Defined.


Definition zAbs : Z -> nat.
Proof.
intros z.
destruct (isconstrlinear z0 z) as [H|H];
exact ((zLeq_exists _ _ H).1).
Defined.

Lemma zAbs_pos_eval : forall n, zAbs (zIn (n, 0)) = n.
Proof.
intros. unfold zAbs.
destruct (isconstrlinear z0 [n, 0]).
destruct (zLeq_exists z0 [n, 0] l).
simpl.
change (zNat x = zNat (n + 0)) in p.
apply zNat_eq_embedding in p.
path_via (n+0). apply nplus_0_r.

destruct (zLeq_exists [n, 0] z0 l).
simpl. change (zNat x = [0, n]) in p.
apply classes_eq_related in p. red in p;simpl in p.
apply nplus_0_0_back in p;destruct p.
path_via 0.
Defined.

Lemma zAbs_neg_eval : forall n, zAbs (zIn (0, n)) = n.
Proof.
intros. unfold zAbs.
destruct (isconstrlinear z0 [0, n]).
destruct (zLeq_exists z0 [0, n] l).
simpl.
change (zNat x = [0, n+0]) in p.
apply classes_eq_related in p. red in p;simpl in p.
apply nplus_0_0_back in p. destruct p.
path_via 0. path_via (n+0). apply nplus_0_r.

destruct (zLeq_exists [0, n] z0 l).
simpl.
change (zNat x = zNat n) in p.
apply zNat_eq_embedding in p. assumption.
Defined.

(*NB: related_classes_eq means it doesn't compute well, so only use it for hprops*)
Lemma z_posneg_ind : forall P : Z -> Type,
(forall z, IsHProp (P z)) ->
(forall n, P [n, 0]) -> (forall n, P [0, n]) ->
forall z, P z.
Proof.
intros ? Hp Hv Hv'.
apply z_ind'. apply _.
intros x.
destruct (isconstrlinear (snd x) (fst x));
apply nle_exists in l;destruct l as [k H].
apply transport with [k, 0].
apply related_classes_eq. red. simpl. path_via (fst x).
apply inverse;apply nplus_0_r.
apply Hv.
apply transport with [0, k].
apply related_classes_eq. red. simpl. path_via (snd x).
path_via (k + fst x). apply commutative. apply nat_issemiring.
apply Hv'.
Defined.

Lemma zAbs_0_back : forall x : Z, 0 = zAbs x -> z0 = x.
Proof.
apply (z_posneg_ind (fun x => _ -> _) _).
intros.
assert (0 = n). path_via (zAbs [n, 0]). apply zAbs_pos_eval.
apply (ap (fun k => [k, 0])). assumption.

intros.
assert (0 = n). path_via (zAbs [0, n]). apply zAbs_neg_eval.
apply (ap (fun k => [0, k])). assumption.
Defined.

Lemma zAbs_zMult : forall a b, zAbs (a°b) = zAbs a ° zAbs b.
Proof.
apply (z_posneg_ind (fun x => forall y, _) _);intro n;
apply (z_posneg_ind (fun y => _) _);intro m;apply (@concat _ _ (n°m)).

- transitivity (zAbs [n°m, 0]).
  apply (ap (fun x => zAbs (class_of _ x))).
  unfold multU. simpl.
  apply path_prod'.
  apply nplus_0_r.
  change (n°0 + m°0 = 0 + 0).
  apply ap11;[apply ap|];apply nmult_0_r.
  apply zAbs_pos_eval.
- apply inverse;apply ap11;[apply ap|];apply zAbs_pos_eval.

- transitivity (zAbs [0, n°m]).
  apply (ap (fun x => zAbs (class_of _ x))).
  unfold multU;simpl.
  apply path_prod'.
  apply (@concat _ _ (n°0)).
  apply nplus_0_r. apply nmult_0_r.
  apply nplus_0_r.
  apply zAbs_neg_eval.
- apply inverse;apply ap11;[apply ap|].
  apply zAbs_pos_eval.
  apply zAbs_neg_eval.

- apply (@concat _ _ (zAbs [0, n°m])).
  apply (ap (fun x => zAbs (class_of _ x))).
  unfold multU;simpl.
  apply path_prod'.
  change (n°0 = 0). apply nmult_0_r.
  change (m°n = n°m). apply nmult_comm.
  apply zAbs_neg_eval.
- apply inverse;apply ap11;[apply ap|].
  apply zAbs_neg_eval.
  apply zAbs_pos_eval.

- apply(@concat _ _ (zAbs [n°m, 0])).
  apply (ap (fun x => zAbs (class_of _ x))).
  unfold multU;simpl;apply path_prod'.
  reflexivity.
  reflexivity.
  apply zAbs_pos_eval.
- apply inverse;apply ap11;[apply ap|];apply zAbs_neg_eval.
Qed.

Global Instance Z_strict_integral : IsStrictIntegral ZPrering.
Proof.
red.
change ZeroV with [0, 0].
intros. apply min1.
apply (ap zAbs) in H.
assert (H' : 0 = zAbs a ° zAbs b).
apply (@concat _ _(zAbs (a°b))).
apply (@concat _ _ (zAbs [0, 0])).
apply inverse;apply zAbs_pos_eval.
apply H.

apply zAbs_zMult.
apply nmult_integral in H'.
clear H. destruct H' as [H|H];[left|right];apply zAbs_0_back;assumption.
Defined.

End NotaSec.

End Relative.



