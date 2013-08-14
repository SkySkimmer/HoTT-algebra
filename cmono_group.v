Require Import HoTT hit.unique_choice.
Require Export structures basics.
Require Import quotient.
Require Import syntax.

Open Scope path_scope.

Import BinOpTree.
Import Distributive.
Import Ring_pr.
Import OrderedMagma_pr.
Import ListNotations.

Module GroupOfCMono.
Import minus1Trunc.

Section VarSec.

Context {G:Type}.
Variable (L : Gop G).

Definition equivU (x y : G*G) : Type := 
  gop (fst x) (snd y) = gop (fst y) (snd x).

Definition gopU : Gop (G*G) :=
fun x y => (gop (fst x) (fst y), gop (snd x) (snd y)).

Definition quotU := quotient equivU.

Instance quotU_set : IsHSet quotU := _.

Definition quotIn : G*G -> quotU := class_of _.

Instance equiv_prop : forall {Hset : IsHSet G}
 (x y : G*G), IsHProp (equivU x y).
Proof.
intros.
red;simpl;apply Hset.
Defined.

Lemma gopU_respects : forall {Hsg : IsSemigroup L},
 forall x x' : G*G, equivU x x' ->
 forall y y', equivU y y' -> 
equivU (gopU x y) (gopU x' y').
Proof.
intros Hsg ? ? Hx ? ? Hy.
unfold equivU in *. simpl.
set (xa:=fst x) in *. set (xb:=snd x) in *.
set (xa':=fst x') in *. set (xb':=snd x') in *.
set (ya:=fst y) in *. set (yb:=snd y) in *.
set (ya':=fst y') in *. set (yb':=snd y') in *.
path_via (gop (gop xa xb') (gop ya yb')).
eapply concat;[apply sg_assoc;apply _|].
eapply concat;[|symmetry;apply sg_assoc;apply _]. apply ap10.
apply ap.
eapply concat;[symmetry;apply sg_assoc;apply _|].
eapply concat;[|apply sg_assoc;apply _]. apply ap. apply sg_comm;apply _.
path_via (gop (gop xa' xb) (gop ya' yb)).
apply ap11;[apply ap|];assumption.
eapply concat;[apply sg_assoc;apply _|].
eapply concat;[|symmetry;apply sg_assoc;apply _]. apply ap10.
apply ap.
eapply concat;[symmetry;apply sg_assoc;apply _|].
eapply concat;[|apply sg_assoc;apply _]. apply ap. apply sg_comm;apply _.
Defined.

Instance equivU_refl : Reflexive equivU.
Proof.
intros ?. reflexivity.
Defined.

Instance equivU_trans : forall {Hsg : IsSemigroup L}
{Hcan : forall a : G, Cancel L a}, Transitive equivU.
Proof.
intros ? ? [x x'] [y y'] [z z'] H H'.
unfold equivU in *. simpl in *.
apply (@left_cancel _ L y' _).
path_via (gop (gop x y') z').
eapply concat;[apply associative;apply _|]. apply ap10. apply ap.
 apply commutative;apply _.
path_via (gop (gop y x') z'). apply ap10. apply ap. apply H.
path_via (gop (gop y z') x').
eapply concat;[symmetry;apply sg_assoc;apply _|].
eapply concat;[|apply sg_assoc;apply _]. apply ap. apply sg_comm;apply _.
path_via (gop (gop z y') x'). apply ap10. apply ap. apply H'.
eapply concat;[|symmetry;apply sg_assoc;apply _]. apply ap10.
apply ap;apply sg_comm;apply _.
Defined.

Instance equivU_symm : Symmetric equivU.
Proof.
intros x y. apply inverse.
Defined.

Definition quotU_rec2 : forall dclass : G * G -> G * G -> quotU,
       (forall x x' : G * G,
        equivU x x' ->
        forall y y' : G * G, equivU y y' -> dclass x y = dclass x' y') ->
       quotU -> quotU -> quotU := quotient_rec2.

Instance quotOp : forall {Hsg : IsSemigroup L}, Gop quotU.
Proof.
intros ?. red;red. apply (quotU_rec2 (fun x y => class_of equivU (gopU x y))).
intros. apply related_classes_eq. apply gopU_respects;assumption.
Defined.

Definition quotU_rect := @quotient_rect _ equivU.
Definition quotU_ind := @quotient_rect_prop _ equivU.

Instance quotAssoc : forall {Hsg : IsSemigroup L}, Associative (quotOp).
Proof.
intros. red. unfold gop.
apply (quotU_ind (fun x => forall y z, _)).
apply _.

intro. apply (quotU_ind (fun y => forall z, _)).
apply _.

intro y.
apply quotU_ind.
apply _.

intro z. simpl.
apply related_classes_eq.
unfold gopU;unfold equivU;simpl.
apply ap11;[apply ap|].
 apply sg_assoc;apply _.
 symmetry;apply sg_assoc;apply _.
Defined.

Instance quotComm : forall {Hsg : IsSemigroup L}, Commutative quotOp.
Proof.
intros. red. unfold gop.

apply (quotU_ind (fun x => forall y, _)).
apply _.

intro x.
apply quotU_ind.
apply _.

intro y. simpl.
apply related_classes_eq.
apply ap11;[apply ap|];apply sg_comm;apply _.
Defined.

Instance quotIsSg : forall {Hsg : IsSemigroup L}, IsSemigroup quotOp
 := fun _ => BuildIsSemigroup _ _ _.

Definition quotE {Hg : IsMonoid L} : quotU := quotIn (gidV, gidV).

Instance quotE_left : forall {Hg : IsMonoid L}, Left_id quotOp quotE.
Proof.
intros;red. apply quotU_ind.
apply _.

intros [a b]. unfold gop;simpl.
apply ap. apply path_prod';apply gid.
Defined.

Instance quotE_right : forall {Hg : IsMonoid L}, Right_id quotOp quotE.
Proof.
intros;red. apply quotU_ind.
apply _.
intros [a b]. unfold gop;simpl.
apply ap. apply path_prod';apply gid.
Defined.

Instance quotE_id : forall {Hg : IsMonoid L}, IsId quotOp quotE
 := fun _ => BuildIsId _ _ _ _.

Instance quotId : forall {Hg : IsMonoid L}, Identity quotOp
:= fun _ => BuildIdentity _ _ _.

Instance quotU_ismonoid : forall {Hg : IsMonoid L}, IsMonoid quotOp
 := fun G => BuildIsMonoid _ _ quotId.

Definition quotOppV : forall {Hsg : IsSemigroup L},
 quotU -> quotU.
Proof.
intros ?.
apply (quotU_rect (fun _ => quotU) (fun x => match x with
  | (a,b) => quotIn (b,a) end)).
intros [xa xb] [ya yb] H.
path_via (quotIn (xb, xa)).
apply transport_const.
apply related_classes_eq.
unfold equivU in *. simpl in *.
path_via (gop ya xb). apply sg_comm;apply _. eapply concat. symmetry;apply H.
apply sg_comm;apply _.
Defined.

Instance quotOppV_correct : forall {Hg : IsMonoid L},
 forall x : quotU, IsInverse quotOp x (quotOppV x).
Proof.
intros ?. apply quotU_ind.
apply _.
intros [xa xb];apply linverse_inverse. red.
simpl. apply transport with quotE. symmetry.
apply related_classes_eq. red. simpl.
eapply concat. apply sg_comm;apply _. apply ap. apply sg_comm;apply _.
apply _.
Defined.

Definition quotOpp : forall {Hg : IsMonoid L}, forall x : quotU,
 Inverse quotOp x.
Proof.
intros;exists (quotOppV x). apply _.
Defined.

Global Instance quotU_group : forall {Hg : IsMonoid L}, IsGroup quotOp
 := fun _ => easyIsGroup quotOp quotOpp.

Definition quotEmbed : forall {Hg : IsMonoid L},
G -> quotU := fun _ x => quotIn (x, gidV).

Global Instance quotEmbed_morphism : forall {Hg : IsMonoid L},
Magma.IsMorphism (&) (&) quotEmbed.
Proof.
red;intros. unfold quotEmbed. unfold gop;simpl.
apply ap.
unfold gopU;simpl. apply ap. apply inverse;apply gid.
Defined.

Lemma quotIn_lcancel : forall {Hsg : IsSemigroup L},
 forall x a b : G, quotIn (gop x a, gop x b) = quotIn (a, b).
Proof.
intros. apply related_classes_eq. red. simpl.
ssrapply (@ast_use G L). reflexivity.
Defined.

(*
Note: this is the only place where we use the cancellation hypothesis
(more precisely, cancellation -> equivU transitive which is used to define the in_class predicate used in classes_eq_related)
(we can't skip this as classes_eq_related and related_classes_eq together imply that the quotienting relation is an equivalence)
The Hset hypothesis is also used to define in_class as we need that if R x y then R x z = R y z.
*)
Lemma quotOp_eq_related : forall {Hset : IsHSet G} 
{Hg : IsCMonoid L}, forall x y : G*G, quotIn x = quotIn y -> equivU x y.
Proof.
intros ? ?. apply classes_eq_related.
Defined.

Lemma quotEmbed_injective : forall {Hset : IsHSet G} {Hmon : IsCMonoid L},
 forall x y : G, 
quotEmbed x = quotEmbed y -> x = y.
Proof.
unfold quotEmbed.
intros ? ? ? ? H.
apply quotOp_eq_related in H.
red in H. simpl in H.
path_via (gop x gidV). apply inverse;apply gid.
path_via (gop y gidV). apply gid.
Defined.

Lemma quotEmbed_mere_surjective : forall {Hg : IsGroup L},
forall y : quotU, minus1Trunc (exists x : G, quotEmbed x = y).
Proof.
intros ?.
apply quotU_ind. apply _.
intros. apply min1.
exists (gop (fst x) (goppV (snd x))).
apply related_classes_eq.
red;simpl. path_via (gop (fst x) (gop (goppV (snd x)) (snd x))).
symmetry;apply sg_assoc;apply _.
apply ap. eapply id_unique;apply _.
Defined.

Lemma quotEmbed_surjective : forall {Hset : IsHSet G} 
{Hg : IsGroup L}, forall y : quotU, exists x : G, quotEmbed x = y.
Proof.
intros. apply iota.
apply _.
split. apply quotEmbed_mere_surjective.
red. intros.
apply quotEmbed_injective.
path_via y.
Defined.

(*
With structure invariance property we can then prove that if G is a group and its carrier is a set
  then G = quotOp G
*)
End VarSec.

Section Semir.

Context {G : Type}.
Variable L : Prering G.
Context {Hg : IsSemiring L}.

(* (a-b)*(a'-b') = (a*a' + b*b' - (a*b' + b*a')) *)
Definition multU : law (G*G) := fun x y => 
((fst x)°(fst y) + (snd x)°(snd y), (fst x)°(snd y) + (fst y)°(snd x)).

Instance multU_comm : Commutative multU.
Proof.
red;intros. unfold gop. unfold multU.
apply ap11;[apply ap|].
apply ap11;[apply ap|];apply (@commutative _ (°) _).
apply (@commutative _ (+) _).
Defined.

Lemma multU_respects : compatible (equivU (+)) (equivU (+)) (equivU (+)) multU.
Proof.
assert (H : lcompat (equivU (+)) (equivU (+)) multU).
Focus 2.
apply transitive_lr_compat.
apply (equivU_trans (+)).
assumption.
red;intros.
pattern (multU x y').
eapply transport. apply multU_comm.
pattern (multU x y).
eapply transport. apply multU_comm.
apply H. assumption.

red. unfold equivU;simpl.
intros ? ? H ?;
destruct x as [xa xb];destruct x' as [ya yb]; destruct y as [za zb];simpl in *.
unfold gop in *.
path_via (((xa + yb) ° za) + ((xb + ya) ° zb)).
ssrapply (@ast2_full_semiring G L Hg);
reflexivity.

pattern (xa + yb). eapply transport. symmetry. apply H.
pattern (xb + ya). apply transport with (xa + yb).
path_via (ya + xb). apply (@commutative _ (+) _).
ssrapply (@ast2_full_semiring G _);reflexivity.
Defined.

Definition multR : Mult (quotU (+)).
Proof.
red;red;red. apply (quotU_rec2 (+)
   (fun x y => class_of _ (multU x y)));simpl.
intros;apply related_classes_eq;apply multU_respects;assumption.
Defined.

Instance quotPrering : Prering (quotU (+)) :=
 BuildLL_Class (quotU (+)) (quotOp (+)) multR.

Context {Hset : IsHSet G}.

Instance quotMult_comm : @Commutative (quotU (+)) (°).
Proof.
red. unfold gop.
apply (quotU_ind _
 (fun x => forall y, _)).
apply _.

intro x.
apply quotU_ind.
apply _.
intro y.

apply (ap (class_of _)). apply multU_comm.
Defined.

Instance quotMult_assoc : @Associative (quotU (+)) (°).
Proof.
red. unfold gop.

apply (quotU_ind _
 (fun x => forall y z, _) _).

intro x.
apply (quotU_ind _ (fun y => forall z, _) _).

intro y.
apply quotU_ind. apply _.
intro z.
apply (ap (class_of _)).
unfold multU;simpl.
apply ap11;[apply ap|];ssrapply (@ast2_full_semiring G L Hg);reflexivity.
Defined.

Instance quotMult_sg : @IsSemigroup (quotU (+)) (°) := BuildIsSemigroup _ _ _.

Definition quotOneV : @quotU G (+) := quotIn (+) (OneV, ZeroV).

Instance quotOne_left : Left_id (°) quotOneV.
Proof.
red. apply quotU_ind. apply _.
unfold gop. intros.
apply (ap (class_of _));destruct x as [x y].
unfold multU;simpl;apply ap11;[apply ap|].
eapply concat;[|apply (@id_is_right _ _ _ ZeroP)].
apply ap11;[apply ap|]. apply OneP.
apply rmult_0_l.
eapply concat;[|apply (@id_is_right _ _ _ ZeroP)].
apply ap11;[apply ap|]. apply OneP.
apply rmult_0_r.
Defined.

Instance quotOne_right : Right_id (°) quotOneV.
Proof.
red. apply quotU_ind. apply _.
unfold gop. intros.
apply (ap (class_of _));destruct x as [x y].
unfold multU;simpl;apply ap11;[apply ap|].
eapply concat;[|apply (@id_is_right _ _ _ ZeroP)].
apply ap11;[apply ap|]. apply OneP.
apply rmult_0_r.
eapply concat;[|apply (@id_is_left _ _ _ ZeroP)].
apply ap11;[apply ap|]. apply rmult_0_r.
apply OneP.
Defined.

Instance quotOne_id : IsId (°) quotOneV := BuildIsId _ _ _ _.

Definition quotOne : @Identity (quotU (+)) (°) := BuildIdentity _ _ _.

Instance quotMult_monoid : @IsMonoid (quotU (+)) (°)
 := BuildIsMonoid _ _ quotOne.

Instance quot_l_distrib : Ldistributes quotPrering.
Proof.
red.
apply (quotU_ind (+) (fun a => forall b c, _) _).
intro a.
apply (quotU_ind (+) (fun b => forall c, _) _).
intro b.
apply quotU_ind. apply _.
intro c.

apply (ap (quotIn (+))).
apply path_prod';
ssrapply (@ast2_full_semiring G _);
reflexivity.
Defined.

Instance quot_r_distrib : Rdistributes quotPrering.
Proof.
red. intros.
eapply concat. apply quotMult_comm.
eapply concat. apply quot_l_distrib.
apply ap11;[apply ap|];apply quotMult_comm.
Defined.

Instance quot_distrib : Distributes quotPrering := BuildDistributes _ _ _.

Instance quot_semiring : IsSemiring quotPrering := BuildIsSemiring _ _ _ _.

Global Instance quot_ring : IsRing quotPrering := BuildIsRing _ _ _.
Proof.
apply quotOpp.
Defined.

(* result : any semiring can be embedded into a ring *)

End Semir.

Section WithRel.

Context {G : Type}.
Variable L : OpRel G.

Definition quotRelU : Rel (G*G) := fun x y => 
rrel (gop (fst x) (snd y)) (gop (fst y) (snd x)).

Inductive quotRelT : Rel (quotU (&)) :=
  | repr_quotRelT : forall x y, quotRelU x y
                             -> quotRelT (quotIn (&) x) (quotIn (&) y)
.

Lemma quotRelT_repr : forall {Hset : IsHSet G} {Hmon : IsCMonoid L}
{Hcompat : IsLInvariant L} {Hreg : forall x, IsLRegular L x},
forall x y, quotRelT (quotIn L x) (quotIn L y) -> quotRelU x y.
Proof.
intros ? ? ? ?.
assert (H : forall x0 y0, quotRelT x0 y0 ->
 forall x y, x0 = quotIn (&) x -> y0 = quotIn (&) y -> quotRelU x y).
Focus 2. intros ? ? H'. eapply H;[apply H'| |];reflexivity.

intros ? ? H;destruct H as [[xa0 xb0] [ya0 yb0] H].
intros [xa xb] [ya yb] Hx Hy.
apply quotOp_eq_related in Hx;auto.
apply quotOp_eq_related in Hy;auto.
red in Hx,Hy,H;simpl in Hx,Hy,H.
red. simpl.
apply Hreg with (gop xb0 yb0).
pattern (gop (gop xb0 yb0) (gop xa yb)). apply transport with
(gop (gop xb yb) (gop xa0 yb0)).
path_via (gop (gop xa0 xb) (gop yb0 yb)).
ssrapply (@ast_use G (&));try reflexivity. apply Hmon.
path_via (gop (gop xa xb0) (gop yb0 yb)).
apply (@ap _ _ (fun g => gop g _) (xa0 & xb)). assumption.
ssrapply (@ast_use G (&));try reflexivity. apply Hmon.
pattern (gop (gop xb0 yb0) (gop ya xb)). apply transport with
(gop (gop xb yb) (gop ya0 xb0)).
path_via (gop (gop xb0 xb) (gop ya0 yb)).
ssrapply (@ast_use G (&));try reflexivity. apply Hmon.
path_via (gop (gop xb0 xb) (gop ya yb0)).
apply ap. assumption.
ssrapply (@ast_use G (&));try reflexivity. apply Hmon.

apply Hcompat. assumption.
Defined.

Definition quotRel : Rel (quotU L) :=
fun x y => minus1Trunc (quotRelT x y).

Global Instance quotRel_prop : forall x y, IsHProp (quotRel x y).
Proof.
intros. apply minus1Trunc_is_prop.
Defined.

Definition repr_quotRel : forall x y, quotRelU x y ->
 quotRel (quotIn L x) (quotIn L y) := 
fun x y H => min1 (repr_quotRelT x y H).

Lemma quotRel_repr : forall {Hset : IsHSet G}
{Hprop : RelationProp L}
{Hmon : IsCMonoid L} {Hcompat : IsLInvariant L}
{Hreg : forall x, IsLRegular L x},
forall x y, quotRel (quotIn L x) (quotIn L y) -> quotRelU x y.
Proof.
intros ? ? ? ? ? ? ?. apply minus1Trunc_rect_nondep.
apply quotRelT_repr.
apply Hprop.
Defined.

Context {Hset : IsHSet G} {Hprop : RelationProp L}
{Hmon : IsCMonoid L}
{Hcompat : IsLInvariant L} {Hreg : forall x, IsLRegular L x}.

Instance quotOpRel : OpRel (quotU L)
 := BuildLR_Class _ (quotOp L) quotRel.

Instance quot_lcompat : IsLInvariant quotOpRel.
Proof.
red.
apply quotU_ind.
intros;apply trunc_forall.
intros z. red.
apply (quotU_ind L (fun x => forall y, _ -> _) _).
intros x. apply (quotU_ind L (fun y => _ -> _) _).
intros y H.

destruct x as [xa xb];destruct y as [ya yb];destruct z as [za zb].
unfold rrel in H; simpl in H. unfold rrel;simpl.
apply quotRel_repr in H. apply repr_quotRel.
unfold gopU;simpl. red;red in H;simpl;simpl in H.
pattern (gop (gop za xa) (gop zb yb)). apply transport with
(gop (gop za zb) (gop xa yb)). ssrapply (@ast_use G L);reflexivity.
pattern (gop (gop za ya) (gop zb xb)). apply transport with
(gop (gop za zb) (gop ya xb)). ssrapply (@ast_use G L);reflexivity.
apply Hcompat. assumption.
Defined.

Global Instance quotrel_invariant : IsInvariant quotOpRel.
Proof.
split. apply _.
red;red. intros.
pattern (x & z);apply transport with (z & x);[apply commutative;apply _|].
pattern (y & z);apply transport with (z & y);[apply commutative;apply _|].
apply quot_lcompat. assumption.
Defined.

Global Instance quot_regular : forall x, IsRegular quotOpRel x.
Proof.
intros. eapply inverse_regular;try apply _.
unfold gop; apply _.
apply gopp.
Defined.

Lemma embed_rel : forall x y : G, rrel x y ->
 (quotEmbed L x) ~> (quotEmbed L y).
Proof.
intros. unfold quotEmbed. apply repr_quotRel. red;simpl.
apply transport with y. apply inverse. apply gid.
pattern (gop x gidV). apply transport with x. apply inverse. apply gid.
assumption.
Defined.

Lemma embed_rel_back : forall x y : G, (quotEmbed L x) ~> (quotEmbed L y)
 -> x ~> y.
Proof.
intros ? ? H. unfold quotEmbed in H.
apply quotRel_repr in H.
apply transport with (gop y gidV). apply gid.
pattern x;apply transport with (gop x gidV). apply gid.
apply H.
Defined.

End WithRel.

End GroupOfCMono.


