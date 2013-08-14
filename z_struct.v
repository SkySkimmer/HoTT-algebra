Require Import HoTT.

Require Import quotient.
Require Import syntax.
Require Import nat_struct.
Require Import cmono_group.
Require Import hit.minus1Trunc.
Require Import hit.unique_choice.


Lemma prod_eq_dec : forall A (Ha : decidable_paths A) B (Hb : decidable_paths B),
decidable_paths (A*B).
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
Instance ZPrering : Prering Z := quotPrering _.
Instance ZRing : IsRing ZPrering := quot_ring _.

Definition z_class : nat*nat -> Z := quotIn (+).

Definition zEquiv : Rel (nat*nat) := equivU (+).

Instance ZRing_set : IsHSet Z := _.

Instance zEquiv_prop : RelationProp zEquiv.
Proof.
red;apply _.
Defined.

Definition z_rect : forall (P : Z -> Type) 
(dclass : forall m n, P (z_class (m, n))),
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

Definition z_ind : forall (P : Z -> Type), 
(forall a b, IsHProp (P (z_class (a, b)))) -> 
(forall a b, P (z_class (a, b))) ->
forall z, P z.
Proof.
intros P Hp Hd. apply quotU_ind.
apply quotU_ind. intros;apply _.
intros [a b]. apply Hp.
simpl. intros [a b];apply Hd.
Defined.

Definition z_ind_contr : forall (P : Z -> Type),
(forall a b, Contr (P (z_class (a, b)))) ->
forall z, Contr (P z).
Proof.
intros P Hd. apply quotU_rect with
 (fun p => match p as p' return (Contr (P (quotIn (+) p'))) with
   | (a,b) => Hd a b end).
intros.
apply hprop_contr.
Defined.

Lemma z_rect_compute : forall (P : Z -> Type)
(dclass : forall m n, P (z_class (m, n))) H a b,
 z_rect P dclass H (z_class (a, b)) = dclass a b.
Proof.
intros. reflexivity.
Defined.

Section NotaSec.
Notation "[ a , b ]" := (z_class (a, b)).

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
Instance zOppP : forall x : Z, IsInverse (+) x (zOppV x) := _.

Definition zero_class : ZeroV = [0,0] := idpath.
Definition one_class : OneV = [1%nat,0] := idpath.

Lemma zOpp_eval : forall a b, zOppV [a, b] = [b, a].
Proof.
intros;reflexivity.
Defined.

Lemma z_related_classes_eq : forall a b c d, zEquiv (a,b) (c,d) -> 
[a, b] = [c, d].
Proof.
intros ? ? ? ?. apply related_classes_eq.
Defined.

Lemma z_classes_eq_related : forall a b, z_class a = z_class b -> 
zEquiv a b.
Proof.
apply classes_eq_related.
Defined.

Definition zEmbed : nat -> Z := quotEmbed (+).

Lemma zEmbed_injective : forall n m, zEmbed n = zEmbed m -> n=m.
Proof.
unfold zEmbed. intros ? ? H.
eapply quotEmbed_injective. apply _.
apply H.
Defined.

Definition zEmbed_eval : forall n, zEmbed n = [n,0] := fun _ => idpath.

Definition zCanon (z : Z) (x : nat*nat) :=
 (z = z_class x) * minus1Trunc (fst x = 0 \/ snd x = 0).

Definition is_zCanon : forall x, (fst x = 0 \/ snd x = 0) ->
 zCanon (z_class x) x := fun x H => (idpath , min1 H).

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
destruct (le_linear a b) as [H | H];apply le_exists in H;destruct H as [k []].
exists (0, k). split.
apply z_related_classes_eq. red;red. simpl.
path_via (k + a). apply commutative;apply nat_issemiring.
apply min1. left;reflexivity.
exists (k,0). split.
apply z_related_classes_eq;red;red;simpl. apply nplus_0_r.
apply min1;right;reflexivity.
Defined.

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

Definition eq_z_dec : decidable_paths Z.
Proof.
red.
intros.
destruct (canonT x) as [rx Hx].
destruct (canonT y) as [ry Hy].
destruct (prod_eq_dec _ eq_nat_dec _ eq_nat_dec rx ry).
- left. path_via (quotIn (+) rx). apply Hx.
  path_via (quotIn (+) ry). apply ap;assumption.
  symmetry;apply Hy.
- right. intro Hn. destruct Hn. apply n. eapply zCanon_atmost;eauto.
Defined.


End NotaSec.

Notation z0 := (@ZeroV Z ZPrering ZRing).
Notation z1 := (@OneV Z ZPrering ZRing).

End Relative.



