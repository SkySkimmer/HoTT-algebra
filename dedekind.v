Require Import HoTT FunextAxiom UnivalenceAxiom.

Require Import basics syntax quotient minus1Trunc.

Module Dedekind.
Import Distributive.
Export Field_pr OrderedRing OrderedMagma_pr.

Section VarSec.

Context {T : Type}.
Variable L : PreringFull T.
Context {Hdec : @Decidable T paths} {HpropLt : RelationProp (<)}
 {Hfield : IsDecField L}
 {Hfo : FullPseudoSemiringOrder L} {Htri : Trichotomic (<)}.

Let Hset : IsHSet T := hset_decidable Hdec.

Class IsCut (L U : T -> Type) := BuildIsCut {
cut_prop_l :> forall x, IsHProp (L x);
cut_prop_u :> forall x, IsHProp (U x);
cut_inhab_l : minus1Trunc (sigT L);
cut_inhab_u : minus1Trunc (sigT U);
cut_round_l : forall q, L q <-> minus1Trunc (exists r, q < r /\ L r);
cut_round_u : forall r, U r <-> minus1Trunc (exists q, q < r /\ U q);
cut_disjoint : forall q, L q -> U q -> Empty;
cut_locat : forall q r, q < r -> minus1Trunc (L q \/ U r)
}.

Record Real := BuildReal {
real_l : T -> Type;
real_u : T -> Type;
real_cut : IsCut real_l real_u
}.

Existing Instance real_cut.
Coercion real_cut : Real >-> IsCut.

Global Instance IsCut_is_prop : forall L U, IsHProp (IsCut L U).
Admitted.

Global Instance Real_is_set : IsHSet Real.
Admitted.

Lemma cut_order : forall L U, IsCut L U ->
forall a b, L a -> U b -> a < b.
Proof.
intros.
destruct (Htri a b). assumption.
destruct s. destruct p.
edestruct cut_disjoint. apply X0. apply X1.
edestruct cut_disjoint. apply X0.
apply cut_round_u. apply min1.
exists b. split. assumption. assumption.
Defined.

Instance lt_compat : IsCompat (+ <).
Proof.
apply invariant_compat.
apply (@fullpseudo_is_fullposet _ L);try apply _.
split; apply Hfo.
apply linvariant_invariant. apply _.
red;apply _.
Defined.

Let Hfullpo : FullPoset L.
Proof.
apply fullpseudo_is_fullposet.
apply HpropLt. split.
apply Hfo. apply Hfo.
Defined.
Existing Instance Hfullpo.

Instance leq_compat : IsCompat (+ <=).
Proof.
admit. (** fuck it **)
Defined.

Lemma lt_plus_leq : forall a b : T, a < b -> forall c d : T, c <= d -> 
a + c < b + d.
Proof.
intros.
apply (@lt_iff_le_apart _ _ Hfullpo).
split. apply leq_compat;unfold rrel;simpl.
apply (@lt_iff_le_apart T L _) in X. apply X.
assumption.
admit. (**arghwhy**)
Defined.

Lemma embed_justify : forall t : T, IsCut (fun t' => t' < t) (lt t).
Proof.
split.
- intros;apply HpropLt.
- apply HpropLt.

- apply min1. exists (t + roppV OneV).
  apply transport with (t + ZeroV).
  apply Zero.
  apply Hfo. unfold rrel.
  admit. (** roppV OneV < ZeroV **)

- apply min1. exists (t + OneV).
  change ((fun t' => t' < t + OneV) t). apply transport with (t + ZeroV).
  apply Zero.
  apply Hfo. unfold rrel.
  admit. (** ZeroV < OneV **)

- split.
  intros H.
  admit. (** q < t -> (q+t)/2 between q and t **)
  apply minus1Trunc_rect_nondep;[|apply HpropLt].
  intros [r [Hr Hr']].
  apply @transitivity with r;try assumption.
  admit. (** fullpseudo -> < trans, already proven **)

- split.
  admit. (** q < t -> (q+t)/2 between q and t **)
  apply minus1Trunc_rect_nondep;[|apply HpropLt].
  intros [q [Hq Hq']].
  apply @transitivity with q;try assumption.
  admit. (** fullpseudo -> < trans, already proven **)

- intro. apply Hfo.

- intros.
  admit. (** q < t -> (q+t)/2 between q and t **)
Qed.

Definition embed (t : T) : Real.
Proof.
apply (BuildReal (fun t' => t' < t) (lt t)).
apply embed_justify.
Defined.

Lemma rplus_justify : forall X Y : Real,
IsCut (fun q => minus1Trunc
     (exists r s : T, real_l X r /\ real_l Y s /\ r+s = q))
      (fun q => minus1Trunc
     (exists r s : T, real_u X r /\ real_u Y s /\ r+s = q)).
Proof.
split;try apply _.

- generalize (@cut_inhab_l (real_l X) _ _).
  apply minus1Trunc_rect_nondep;[|apply minus1Trunc_is_prop].
  intros Hx.
  generalize (@cut_inhab_l (real_l Y) _ _).
  apply minus1Trunc_rect_nondep;[|apply minus1Trunc_is_prop].
  intros Hy.
  apply min1.
  exists (Hx.1 + Hy.1).
  apply min1. exists (Hx.1). exists (Hy.1).
  split. apply (Hx.2).
  split. apply (Hy.2).
  reflexivity.

- generalize (@cut_inhab_u (real_l X) _ _).
  apply minus1Trunc_rect_nondep;[|apply minus1Trunc_is_prop].
  intros Hx.
  generalize (@cut_inhab_u (real_l Y) _ _).
  apply minus1Trunc_rect_nondep;[|apply minus1Trunc_is_prop].
  intros Hy.
  apply min1.
  exists (Hx.1 + Hy.1).
  apply min1. exists (Hx.1). exists (Hy.1).
  split. apply (Hx.2).
  split. apply (Hy.2).
  reflexivity.

- split. apply minus1Trunc_rect_nondep;[|apply minus1Trunc_is_prop].
  intros H.
  destruct H as [r [s [H [H' H'']]]]. destruct H''.
  apply cut_round_l in H. revert H.
  apply minus1Trunc_rect_nondep;[|apply minus1Trunc_is_prop].
  intros [r' Hr'].
  apply cut_round_l in H'. revert H'.
  apply minus1Trunc_rect_nondep;[|apply minus1Trunc_is_prop].
  intros [s' Hs'].
  apply min1. exists (r' + s'). destruct Hr',Hs'.
  split.
  apply lt_compat; assumption.
  apply min1. exists r';exists s'.
  repeat (split;auto).

  apply minus1Trunc_rect_nondep;[|apply minus1Trunc_is_prop].
  intros [r [Hr Hr']]. revert Hr'.
  apply minus1Trunc_rect_nondep;[|apply minus1Trunc_is_prop].
  intros [r' [s [Hr' [Hs He]]]]. destruct He.
  (* q < r'+s, r' < X, s < Y -> exists r s', r < X, s' < Y, r + s' = q *)
  (* let r := r', s' := q-r' < s < Y *)
  apply min1. exists r'. exists (q + (roppV r')). split. assumption.
  split. apply cut_round_l. apply min1. exists s.
  split;[|assumption].
  apply transport with ((r'+s)+(roppV r')).
  path_via (s + ZeroV).
  path_via (s + (r' + roppV r')).
  ssrapply (@ast_use T (+) _). reflexivity.
  apply ap. apply ropp_r.
  apply Zero.
  apply lt_plus_leq. assumption.
  apply Hfullpo.
  path_via (q + (r' + roppV r')).
  ssrapply (@ast_use T (+) _). reflexivity.
  apply roppP.

- admit. (* basically same as above *)

- intros q H. apply minus1Trunc_rect_nondep;[|intros []].
  intro H'. revert H. apply minus1Trunc_rect_nondep;[|intros []].
  intro H.
  destruct H as [r [s [Hr [Hs He]]]].
  destruct H' as [r' [s' [Hr' [Hs' He']]]].
  destruct He'.
  (* r' > X, s' > Y, r < X, s < Y, r+s = r'+s' -> Empty *)
  (* r = r'+s'-s < X *)
  (* r'+s'-s > X -> absurd *)
  admit.

- intros.
  (* goal: forall q < r, q < X+Y or X+Y < r *)
  admit. (* dunno how to prove *)
Qed.

Definition rPlus : Plus Real.
Proof.
intros X Y.
apply (BuildReal
 (fun q => minus1Trunc (exists r s : T, real_l X r /\ real_l Y s /\ r+s = q))
 (fun q => minus1Trunc (exists r s : T, real_u X r /\ real_u Y s /\ r+s = q))).
apply rplus_justify.
Defined.

(*
forall q X, q < -X <-> X < -q and -X < q <-> -q < X
*)
Lemma ropp_justify : forall X : Real, IsCut
(fun q => real_u X (roppV q))
(fun q => real_l X (roppV q)).
Proof.
intros.
split;try apply _.
- generalize (@cut_inhab_u _ _ X).
  apply minus1Trunc_rect_nondep;[|apply minus1Trunc_is_prop].
  intros H.
  apply min1. destruct H as [x Hx].
  exists (roppV x).
  eapply transport;[|apply Hx].
  apply inverse;apply gopp_gopp.

- generalize (@cut_inhab_l _ _ X).
  apply minus1Trunc_rect_nondep;[|apply minus1Trunc_is_prop].
  intros H.
  apply min1. destruct H as [x Hx].
  exists (roppV x).
  eapply transport;[|apply Hx].
  apply inverse;apply gopp_gopp.

- intros. eapply iff_trans.
  apply cut_round_u.
  split;(apply minus1Trunc_rect_nondep;[|apply minus1Trunc_is_prop]);
  intros H;apply min1;
  destruct H as [r [Hr Hr']];
  exists (roppV r); (split;[admit|]). (* forall a < b -> -b < -a *)
  eapply transport;[|apply Hr'].
  apply inverse;apply gopp_gopp.
  assumption.

- intros. eapply iff_trans.
  apply cut_round_l.
  split;(apply minus1Trunc_rect_nondep;[|apply minus1Trunc_is_prop]);
  intros H;apply min1;
  destruct H as [q [Hq Hq']];
  exists (roppV q); (split;[admit|]). (* forall a < b -> -b < -a *)
  eapply transport;[|apply Hq'].
  apply inverse;apply gopp_gopp.
  assumption.

- intros q H H';revert H;revert H'. apply cut_disjoint.

- intros.
  assert (H:roppV r < roppV q). admit. clear X0.
  apply (@cut_locat _ _ X) in H. revert H.
  apply minus1Trunc_rect_nondep;[|apply minus1Trunc_is_prop].
  intros H;apply min1;destruct H as [H|H];[right|left];assumption.
Qed.

Definition rOpp : forall X : Real, Real.
Proof.
intros. econstructor.
apply (ropp_justify X).
Defined.

Definition r0 : Real := embed ZeroV.

Definition mult_lower (X Y : Real) : T -> Type
 := fun q => minus1Trunc (exists a b c d : T, real_l X a /\ real_u X b
   /\ real_l Y c /\ real_u Y d /\ q < a°c /\ q < a°d /\ q < b°c /\ q < b°d).

Definition mult_upper (X Y : Real) : T -> Type
 := fun q => minus1Trunc (exists a b c d : T, real_l X a /\ real_u X b
   /\ real_l Y c /\ real_u Y d /\ a°c < q /\ a°d < q /\ b°c < q /\ b°d < q).

Lemma mult_justify : forall X Y : Real, IsCut (mult_lower X Y) (mult_upper X Y).
Proof.
intros;split;try apply _;
admit. (* later *)
Qed.

Definition rMult : Mult Real.
Proof.
intros X Y. econstructor.
exact (mult_justify X Y).
Defined.

Definition r1 : Real := embed OneV.

Definition rLeq : Leq Real := fun X Y =>
forall q : T, real_l X q -> real_l Y q.
Definition rLt : Lt Real := fun X Y =>
minus1Trunc (exists q : T, real_u X q /\ real_l Y q).
Definition rApart : Apart Real := fun X Y =>
rLt X Y \/ rLt Y X.

Instance rFull : PreringFull Real
 := BuildLLRRR_Class Real rPlus rMult rApart rLeq rLt.

Lemma real_eq : forall X Y : Real,
(forall q, real_l X q <-> real_l Y q) ->
(forall q, real_u X q <-> real_u Y q) ->
X=Y.
Proof.
admit. (* etc *)
Defined.

Instance rplus_comm : @Commutative Real (+).
Proof.
red;unfold gop.
assert (Hl : forall X Y : Real, forall q, real_l (X+Y) q -> real_l (Y+X) q).
simpl. intros X Y q.
apply minus1Trunc_rect_nondep;[|apply minus1Trunc_is_prop].
intro H;apply min1;destruct H as [r [s [H [H0 H1]]]].
exists s;exists r;repeat (split;try assumption).
path_via (r+s).
apply commutative. apply Hfield.

assert (Hu : forall X Y : Real, forall q, real_u (X+Y) q -> real_u (Y+X) q).
simpl. intros X Y q.
apply minus1Trunc_rect_nondep;[|apply minus1Trunc_is_prop].
intro H;apply min1;destruct H as [r [s [H [H0 H1]]]].
exists s;exists r;repeat (split;try assumption).
path_via (r+s).
apply commutative. apply Hfield.

intros. apply real_eq;
intros;split;auto.
Defined.

Instance rplus_assoc : @Associative Real (+).
Proof.
red;unfold gop.
intros X Y Z.
apply real_eq;simpl;intros q;(split;
(apply minus1Trunc_rect_nondep;[|apply minus1Trunc_is_prop]);intro H;
[destruct H as [r [s [H [H' H0]]]]|destruct H as [r[s[H' [H H0]]]]]);
revert H';(apply minus1Trunc_rect_nondep;[|apply minus1Trunc_is_prop]);
intro H';destruct H' as [r'[s' [H1 [H2 H3]]]];apply min1;
destruct H0;destruct H3;repeat first
   [econstructor | apply min1 | apply H1 | apply H2 | apply H];
first [apply associative | apply inverse;apply associative];apply Hfield.
Defined.

Instance rplus_sg : @IsSemigroup Real (+). split;apply _. Defined.

Instance r0_is_id : IsId (+) r0.
Proof.
apply left_id_id.
red. unfold gop.
intro X.
unfold r0. apply real_eq; simpl;
(split;[apply minus1Trunc_rect_nondep;[|
    first [apply cut_prop_l | apply cut_prop_u]];
        intros H;destruct H as [r [s [H [H0 H1]]]];destruct H1 |]).

apply cut_round_l. apply min1. exists s. split;auto.
apply transport with (ZeroV + s). apply Zero.
admit. (* plus_lt_leq_lt *)

intros H.
apply cut_round_l in H. revert H.
apply minus1Trunc_rect_nondep;[|apply minus1Trunc_is_prop].
intros H;apply min1. destruct H as [r [H H']].
exists (q + roppV r). exists r.
split. admit. (* q < r -> q - r < 0 *)
split. assumption. path_via (q + (roppV r + r)).
apply inverse;apply associative;apply Hfield.
apply (roppP r). (* bit slow, change for other? *)

apply cut_round_u. apply min1. exists s. split;auto.
change ((fun k => k < r + s) s). apply transport with (ZeroV + s).
apply Zero.
admit. (* plus_lt_leq_lt *)

intros H. apply cut_round_u in H. revert H.
apply minus1Trunc_rect_nondep;[|apply minus1Trunc_is_prop].
intros H;apply min1. destruct H as [r [H H']].
exists (q + roppV r). exists r.
split. admit. (* r < q -> 0 < q - r *)
split. assumption. path_via (q + (roppV r + r)).
apply inverse;apply associative;apply Hfield.
apply (roppP r). (* bit slow, change for other? *)
Defined.

Instance rplus_monoid : @IsMonoid Real (+).
Proof. split;try apply _;econstructor;apply _. Defined.


Instance rLeq_poset : @Poset Real (<=).
Proof.
split.
- red. unfold leq. simpl. unfold rLeq.
  intros;eauto.

- intro. hnf. auto.

- hnf. intros. hnf in X,X0.
  apply real_eq. split;auto.

  split;intro H.
  pose (H' := H);clearbody H'.
  apply cut_round_u in H'.
  revert H';apply minus1Trunc_rect_nondep;[|apply cut_prop_u].
  intros H'. destruct H' as [q' [H' Hq']].
  apply (@cut_locat _ _ y) in H'. revert H'.
  apply minus1Trunc_rect_nondep;[|apply cut_prop_u].
  intros H'. destruct H' as [H'|H'];try assumption.
  apply X0 in H'.
  destruct (@cut_disjoint _ _ x _ H' Hq').

  pose (H' := H);clearbody H'.
  apply cut_round_u in H'.
  revert H';apply minus1Trunc_rect_nondep;[|apply cut_prop_u].
  intros H'. destruct H' as [q' [H' Hq']].
  apply (@cut_locat _ _ x) in H'. revert H'.
  apply minus1Trunc_rect_nondep;[|apply cut_prop_u].
  intros H'. destruct H' as [H'|H'];try assumption.
  apply X in H'.
  destruct (@cut_disjoint _ _ y _ H' Hq').
Defined.


Lemma rlt_embed_l : forall X q, real_l X q <-> embed q < X.
Proof.
intros X. apply cut_round_l.
Defined.

Lemma prod_comm_rw : prod = fun A B => B*A.
Proof.
repeat (apply funext_axiom;intro).
apply univalence_axiom.
apply equiv_prod_symm.
Defined.

Lemma rlt_embed_u : forall X q, real_u X q <-> X < embed q.
Proof.
intros X.
unfold lt;simpl;unfold rLt. simpl.
rewrite prod_comm_rw. apply cut_round_u.
Qed. (* because lel *)

Instance embed_plus_morph : Magma.IsMorphism (+) (+) embed.
Proof.
red. unfold gop.
intros X Y.
apply rLeq_poset;hnf;simpl.
- admit.

- intros q.


 apply minus1Trunc_rect_nondep
Defined.



Instance ropp_inverse : forall X : Real, IsInverse (+) X (rOpp X).
Proof.
intros. apply linverse_inverse.
red. unfold gop. apply transport with r0;[|apply _].
unfold r0. apply real_eq;simpl;intros q;(split;[intros H|
  apply minus1Trunc_rect_nondep;[|apply HpropLt];intros [r [s [H [H0 H1]]]]]).

- (* needs archimedean ?? *)
Defined.




