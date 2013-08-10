Require Import HoTT hit.unique_choice.
Require Export structures basics.
Require Import quotient.
Require Import syntax.

Open Scope path_scope.

Import BinOpTree.
Import Distributive.
Import Ring_pr.
Import OrderedMagma_pr.

Module GroupOfCMono.
Import minus1Trunc.

Definition equivU {G : magma} (x y : G*G) : Type := 
  gop (fst x) (snd y) = gop (fst y) (snd x).

Definition addU {G : magma} : law (G*G) :=
fun x y => (gop (fst x) (fst y), gop (snd x) (snd y)).

Definition quotU G := quotient (@equivU G).

Instance quotU_set : forall G, IsHSet (quotU G).
Proof.
intros;apply quotient_is_set.
Defined.

Definition quotIn : forall {G : magma}, G*G -> quotU G.
Proof.
intros G. apply class_of.
Defined.

Instance equiv_prop : forall {G : magma} {Hset : IsHSet G}
 (x y : G*G), IsHProp (equivU x y).
Proof.
intros.
red;simpl;apply Hset.
Defined.

Lemma addU_respects : forall G : magma, forall {Hsg : IsSemigroup G},
 forall x x' : G*G, equivU x x' ->
 forall y y', equivU y y' -> 
equivU (addU x y) (addU x' y').
Proof.
intros G Hsg ? ? Hx ? ? Hy.
unfold equivU in *. simpl.
set (xa:=fst x) in *. set (xb:=snd x) in *.
set (xa':=fst x') in *. set (xb':=snd x') in *.
set (ya:=fst y) in *. set (yb:=snd y) in *.
set (ya':=fst y') in *. set (yb':=snd y') in *.
path_via (gop (gop xa xb') (gop ya yb')).
eapply concat;[apply sg_assoc|].
eapply concat;[|symmetry;apply sg_assoc]. apply ap10.
apply ap.
eapply concat;[symmetry;apply sg_assoc|].
eapply concat;[|apply sg_assoc]. apply ap. apply sg_comm.
path_via (gop (gop xa' xb) (gop ya' yb)).
apply ap11;[apply ap|];assumption.
eapply concat;[apply sg_assoc|].
eapply concat;[|symmetry;apply sg_assoc]. apply ap10.
apply ap.
eapply concat;[symmetry;apply sg_assoc|].
eapply concat;[|apply sg_assoc]. apply ap. apply sg_comm.
Defined.

Instance equivU_refl : forall {G}, Reflexive (@equivU G).
Proof.
intros ? ?. reflexivity.
Defined.

Instance equivU_trans : forall {G} {Hsg : IsSemigroup G}
{Hcan : forall a : G, Cancel a}, Transitive (@equivU G).
Proof.
intros ? ? ? [x x'] [y y'] [z z'] H H'.
unfold equivU in *. simpl in *.
assert (Hleft : forall a, @Lcancel G a). apply _.
apply Hleft with y'.
path_via (gop (gop x y') z').
eapply concat;[apply sg_assoc|]. apply ap10. apply ap. apply sg_comm.
path_via (gop (gop y x') z'). apply ap10. apply ap. apply H.
path_via (gop (gop y z') x').
eapply concat;[symmetry;apply sg_assoc|].
eapply concat;[|apply sg_assoc]. apply ap. apply sg_comm.
path_via (gop (gop z y') x'). apply ap10. apply ap. apply H'.
eapply concat;[|symmetry;apply sg_assoc]. apply ap10.
apply ap;apply sg_comm.
Defined.

Instance equivU_symm : forall G, Symmetric (@equivU G).
Proof.
intros ? x y. apply inverse.
Defined.

Definition quotU_rec2 : forall G : magma, 
forall dclass : G * G -> G * G -> @quotU G,
       (forall x x' : G * G,
        equivU x x' ->
        forall y y' : G * G, equivU y y' -> dclass x y = dclass x' y') ->
       @quotU G -> @quotU G -> @quotU G := fun G => quotient_rec2.

Definition addR : forall {G : magma} {Hsg : IsSemigroup G}, law (@quotU G).
Proof.
red.
intros ? ?. apply (quotU_rec2 G (fun x y => class_of equivU (addU x y))).
intros. apply related_classes_eq. apply addU_respects;assumption.
Defined.

Definition quotMag (G : magma) {Hsg : IsSemigroup G} : magma
 := BuildMagma (@quotU G) addR.

Definition quotU_rect (G : magma) := @quotient_rect _ (@equivU G).
Definition quotU_ind (G : magma) := @quotient_rect_prop _ (@equivU G).

Instance quotAssoc : forall G {Hsg : IsSemigroup G}, Associative (quotMag G).
Proof.
intros. red. simpl.
apply (quotU_ind _ (fun x => forall y z, addR x (addR y z) = addR (addR x y) z)).
intros. apply trunc_forall.

intro. apply (quotU_ind _ (fun y => forall z,
 addR (class_of _ x) (addR y z) = addR (addR (class_of _ x) y) z)).
intros. apply trunc_forall.

intro y.
apply quotU_ind.
intro. apply hprop_allpath;apply quotU_set.

intro z. simpl.
apply related_classes_eq.
destruct x as [xa xb];destruct y as [ya yb];destruct z as [za zb].
unfold addU;unfold equivU;simpl.
apply ap11;[apply ap|].
 apply sg_assoc.
 symmetry;apply sg_assoc.
Defined.

Instance quotComm : forall G {Hsg : IsSemigroup G}, Commutative (quotMag G).
Proof.
intros. red. simpl.

apply (quotU_ind _ (fun x => forall y, addR x y = addR y x)).
intros. apply trunc_forall.

intro x.
apply quotU_ind.
intro. apply hprop_allpath;apply quotU_set.

intro y. simpl.
apply related_classes_eq.
destruct x,y.
apply ap11;[apply ap|];apply sg_comm.
Defined.

Instance quotIsSg : forall G {Hsg : IsSemigroup G}, IsSemigroup (quotMag G)
 := fun G _ => BuildIsSemigroup _ _ _.

Definition quotE (G : monoid) : (quotMag G) := quotIn (gidV, gidV).

Instance quotE_left : forall (G : monoid), Left_id (quotE G).
Proof.
intros;red. apply quotU_ind.
intro;apply hprop_allpath;apply quotU_set.
intros [a b]. unfold gop;simpl.
apply ap. apply path_prod';apply gid.
Defined.

Instance quotE_right : forall (G : monoid), Right_id (quotE G).
Proof.
intros;red. apply quotU_ind.
intro;apply hprop_allpath;apply quotU_set.
intros [a b]. unfold gop;simpl.
apply ap. apply path_prod';apply gid.
Defined.

Instance quotE_id : forall (G : monoid), IsId (quotE G)
 := fun G => BuildIsId _ _ _ _.

Definition quotId : forall (G : monoid), Identity (quotMag G) 
:= fun _ => BuildIdentity _ _ _.

Instance quotU_ismonoid : forall (G : monoid), IsMonoid (quotMag G) 
 := fun G => BuildIsMonoid _ _ (quotId G).

Definition quotOppV : forall {G : magma} {Hsg : IsSemigroup G},
 quotMag G -> quotMag G.
Proof.
intros ? ?. simpl.
apply (quotU_rect G (fun _ => quotU G) (fun x => match x with
  | (a,b) => quotIn (b,a) end)).
intros [xa xb] [ya yb] H.
path_via (class_of equivU (xb, xa)).
apply transport_const.
apply related_classes_eq.
unfold equivU in *. simpl in *.
path_via (gop ya xb). apply sg_comm. eapply concat. symmetry;apply H.
apply sg_comm.
Defined.

Canonical Structure quotU_monoid (G : monoid) : monoid :=
 BuildMonoid (quotMag G) _.

Instance quotOppV_correct : forall G : monoid,
 forall x : quotMag G, IsInverse x (quotOppV x).
Proof.
intros ?. simpl. apply quotU_ind.
intro. apply _.
intros [xa xb];apply linverse_inverse. red.
simpl. apply transport with (quotE G). symmetry.
apply related_classes_eq. simpl.
eapply concat. apply sg_comm. apply ap. apply sg_comm.
apply _.
Defined.

Definition quotOpp : forall G : monoid, forall x : quotMag G, Inverse x.
Proof.
intros;exists (quotOppV x). apply _.
Defined.

Instance quotU_group : forall G : monoid, IsGroup (quotMag G)
 := fun G => @easyIsGroup (quotMag G) (quotU_ismonoid G) (quotOpp G).

Definition quotEmbed : forall {G : monoid},
G -> quotMag G := fun G x => quotIn (x, gidV).

Lemma quotEmbed_morphism : forall G : monoid, forall x y : G, 
quotEmbed (gop x y) = gop (quotEmbed x) (quotEmbed y).
Proof.
intros. unfold quotEmbed.
unfold gop;simpl. apply ap.
unfold addU;simpl. apply ap. apply inverse;apply gid.
Defined.

Lemma quotIn_lcancel : forall (G : magma) {Hsg : IsSemigroup G},
 forall x a b : G, quotIn (gop x a, gop x b) = quotIn (a, b).
Proof.
intros. apply related_classes_eq. red. simpl.
ssrapply (@ast_use G). reflexivity.
Defined.

(*
Note: this is the only place where we use the cancellation hypothesis
(more precisely, cancellation -> equivU transitive which is used to define the in_class predicate used in classes_eq_related)
(we can't skip this as classes_eq_related and related_classes_eq together imply that the quotienting relation is an equivalence)
The Hset hypothesis is also used to define in_class as we need that if R x y then R x z = R y z.
*)
Lemma quotMag_eq_related : forall (G : magma) {Hset : IsHSet G} 
{Hg : IsCMonoid G}, forall x y : G*G, quotIn x = quotIn y -> equivU x y.
Proof.
intros ? ? ?. apply classes_eq_related.
Defined.

Lemma quotEmbed_injective : forall G : magma,
forall {Hset : IsHSet G} {Hmon : IsCMonoid G}, forall x y : G, 
quotEmbed x = quotEmbed y -> x = y.
Proof.
unfold quotEmbed.
intros ? ? ? ?  ? H.
apply (quotMag_eq_related G) in H.
red in H. simpl in H.
path_via (gop x gid). apply inverse;apply gid.
path_via (gop y gid). apply gid.
Defined.

Lemma quotEmbed_mere_surjective : forall G : magma, forall {Hg : IsGroup G}, 
forall y : quotMag G, minus1Trunc (exists x : G, quotEmbed x = y).
Proof.
intros ? ?.
apply quotU_ind.
intros;apply minus1Trunc_is_prop.
intros. apply min1.
exists (gop (fst x) (gopp (snd x))).
destruct x as [x y]. simpl. unfold quotEmbed.
apply related_classes_eq.
red;simpl. path_via (gop x (gop (gopp y) y)). symmetry;apply sg_assoc.
apply ap. apply id_unique;apply _.
Defined.

Lemma quotEmbed_surjective : forall G : magma, forall {Hset : IsHSet G} 
{Hg : IsGroup G}, forall y : quotMag G, exists x : G, quotEmbed x = y.
Proof.
intros. apply iota.
intros. apply hprop_allpath. apply quotU_set.
red. split. apply quotEmbed_mere_surjective.
red. intros.
apply quotEmbed_injective with group_is_cmonoid. apply _.
path_via y.
Defined.

(*
With structure invariance property we can then prove that if G is a group and its carrier is a set
  then G = quotMag G
*)


Section Semir.

Variable G : semiring.

(* (a-b)*(a'-b') = (a*a' + b*b' - (a*b' + b*a')) *)
Definition multU : law (G*G) := fun x y => 
((fst x)°(fst y) + (snd x)°(snd y), (fst x)°(snd y) + (fst y)°(snd x)).

Lemma multU_comm : forall x y, multU x y = multU y x.
Proof.
intros;unfold multU.
apply ap11;[apply ap|].
apply ap11;[apply ap|];apply (@sg_comm (prering_mult G) _).
apply (@sg_comm (prering_plus G) _).
Defined.

Lemma multU_respects : @compatible 
  (G*G) (@equivU (prering_plus G)) 
  (G*G) (@equivU (prering_plus G)) 
  (G*G) (@equivU (prering_plus G)) multU.
Proof.
assert (H : lcompat (@equivU (prering_plus G)) (@equivU (prering_plus G)) multU).
Focus 2.
apply transitive_lr_compat.
apply (@equivU_trans (prering_plus G) _ _).
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
fold (@rplus G) in *.
path_via (((xa + yb) ° za) + ((xb + ya) ° zb)).
ssrapply (@ast2_full_semiring G _).
reflexivity.

pattern (xa + yb). eapply transport. symmetry. apply H.
pattern (xb + ya). apply transport with (xa + yb).
path_via (ya + xb). apply (@commutative (prering_plus G) _).
ssrapply (@ast2_full_semiring G _);reflexivity.
Defined.

Definition multR : law (quotU (prering_plus G)).
Proof.
red. apply (quotU_rec2 (prering_plus G)
   (fun x y => class_of _ (multU x y)));simpl.
intros;apply related_classes_eq;apply multU_respects;assumption.
Defined.

Definition quotPrering : prering :=
 makePrering (quotU (prering_plus G)) (@addR (prering_plus G) _) multR.

Notation quotMult := (prering_mult quotPrering).

Context {Hset : IsHSet G}.

Instance quotMult_comm : Commutative quotMult.
Proof.
red.
apply (quotU_ind _
 (fun x : quotMult => forall y : quotMult, gop x y = gop y x)).
intro;apply trunc_forall.

intro x. simpl in x.
apply quotU_ind.
intro;apply hprop_allpath;apply quotient_is_set.
intro y;simpl in y.

unfold gop;simpl. apply ap. apply multU_comm.
Defined.

Instance quotMult_assoc : Associative quotMult.
Proof.
red. simpl.
assert (hp : forall x y z, IsHProp (multR x (multR y z) = multR (multR x y) z)).
change (forall x y z : quotMult, IsHProp (gop x (gop y z) = gop (gop x y) z)).
intros. apply hprop_allpath;apply quotient_is_set.

apply (quotU_ind _
 (fun x : quotMult => forall y z, multR x (multR y z) = multR (multR x y) z)).
repeat (intro;apply hprop_forall);intro;apply _.

intro x.
apply (quotU_ind _ (fun y => forall z,
multR (class_of equivU x) (multR y z) = multR (multR (class_of equivU x) y) z)).
repeat (intro;apply hprop_forall);intro;apply _.

intro y.
apply quotU_ind.
intro;apply _.
clear  hp.
intro z;simpl in *.
apply ap.
destruct x as [xa xb];destruct y as [ya yb];destruct z as [za zb].
unfold multU;simpl.
apply ap11;[apply ap|];ssrapply (@ast2_full_semiring G _);reflexivity.
Defined.

Instance quotMult_sg : IsSemigroup quotMult := BuildIsSemigroup _ _ _.

Definition quotOneV : quotMult := @quotIn (prering_plus G) (@OneV G, @ZeroV G).

Instance quotOne_left : Left_id quotOneV.
Proof.
red. apply quotU_ind.
intros;apply hprop_allpath;apply quotient_is_set.
unfold gop;simpl. intros.
apply ap;destruct x.
unfold multU;simpl;apply ap11;[apply ap|].
eapply concat;[|apply (@id_right (prering_plus G) _ _)].
simpl. apply ap11;[apply ap|]. apply (@gid (semiring_mult_monoid G)).
apply rmult_0_l.
eapply concat;[|apply (@id_right (prering_plus G) _ _)].
simpl. apply ap11;[apply ap|]. apply (@gid (semiring_mult_monoid G)).
apply rmult_0_r.
Defined.

Instance quotOne_right : Right_id quotOneV.
Proof.
red. apply quotU_ind.
intros;apply hprop_allpath;apply quotient_is_set.
unfold gop;simpl. intros.
destruct x;simpl;apply ap.
unfold multU;simpl;apply ap11;[apply ap|].
eapply concat;[|apply (@id_right (prering_plus G) _ _)].
simpl. apply ap11;[apply ap|]. apply (@gid (semiring_mult_monoid G)).
apply rmult_0_r.
eapply concat;[|apply (@id_left (prering_plus G) _ _)].
simpl. apply ap11;[apply ap|]. apply rmult_0_r.
apply (@gid (semiring_mult_monoid G)).
Defined.

Instance quotOne_id : IsId quotOneV := BuildIsId _ _ _ _.

Definition quotOne : Identity quotMult := BuildIdentity _ _ _.

Instance quotMult_monoid : IsMonoid quotMult := BuildIsMonoid _ _ quotOne.

Lemma quotPrering_ind : forall P : quotPrering -> Type, 
forall {Hp : forall q, IsHProp (P q)},
(forall x : G*G, P (@quotIn (prering_plus G) x)) -> forall q, P q.
Proof.
apply quotU_ind.
Defined.

Ltac unfold_ops := repeat (first [unfold multU | unfold addU ]).

Instance quot_l_distrib : Ldistributes quotPrering.
Proof.
red.
assert (Hp : forall a b c : quotPrering, IsHProp (a ° (b + c) = a ° b + a ° c)).
intros. apply hprop_allpath. apply quotient_is_set.
apply (@quotPrering_ind (fun a => forall b c, a ° (b + c) = a ° b + a ° c)).
intro;apply trunc_forall.
intro a.
apply (@quotPrering_ind (fun b => forall c, _ ° (b + c) = _ ° b + _ ° c)).
intro;apply trunc_forall.
intro b.
apply quotPrering_ind.
intro;apply Hp.
clear Hp.

intro c.
destruct a,b,c.
apply (ap (@quotIn (prering_plus G))). unfold_ops;unfold addU. simpl.
fold (@rplus G). apply ap11;[apply ap|];
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

Instance quot_ring : IsRing quotPrering := BuildIsRing _ _ (quotOpp _).

(* result : any semiring can be embedded into a ring *)

Fail Check (@Zero' quotPrering).

End Semir.

Section WithRel.

Variable G : LR_sig.

Definition quotRelU : relation (G*G) := fun x y => 
rrel (gop (fst x) (snd y)) (gop (fst y) (snd x)).

Inductive quotRelT : (quotU G) -> (quotU G) -> Type :=
  | repr_quotRelT : forall x y, quotRelU x y -> quotRelT (quotIn x) (quotIn y)
.

Lemma quotRelT_repr : forall {Hset : IsHSet G} {Hmon : IsCMonoid G}
{Hcompat : IsLInvariant G} {Hreg : forall x, IsLRegular G x},
forall x y, quotRelT (quotIn x) (quotIn y) -> quotRelU x y.
Proof.
intros ? ? ? ?.
assert (H : forall x0 y0, quotRelT x0 y0 ->
 forall x y, x0 = quotIn x -> y0 = quotIn y -> quotRelU x y).
Focus 2. intros? ? H'. eapply H;[apply H'| |];reflexivity.

intros ? ? H;destruct H as [[xa0 xb0] [ya0 yb0] H].
intros [xa xb] [ya yb] Hx Hy.
apply quotMag_eq_related in Hx;auto.
apply quotMag_eq_related in Hy;auto.
red in Hx,Hy,H;simpl in Hx,Hy,H.
red. simpl.
apply Hreg with (gop xb0 yb0).
pattern (gop (gop xb0 yb0) (gop xa yb)). apply transport with
(gop (gop xb yb) (gop xa0 yb0)).
path_via (gop (gop xa0 xb) (gop yb0 yb)).
ssrapply (@ast_use G);reflexivity.
path_via (gop (gop xa xb0) (gop yb0 yb)).
apply (ap (fun g => gop g _)). auto.
ssrapply (@ast_use G);reflexivity.
pattern (gop (gop xb0 yb0) (gop ya xb)). apply transport with
(gop (gop xb yb) (gop ya0 xb0)).
path_via (gop (gop xb0 xb) (gop ya0 yb)).
ssrapply (@ast_use G);reflexivity.
path_via (gop (gop xb0 xb) (gop ya yb0)).
apply ap. auto.
ssrapply (@ast_use G);reflexivity.

apply Hcompat. assumption.
Defined.

Definition quotRel : relation (quotU G) :=
fun x y => minus1Trunc (quotRelT x y).

Instance quotRel_prop : forall x y, IsHProp (quotRel x y).
Proof.
intros. apply minus1Trunc_is_prop.
Defined.

Definition repr_quotRel : forall x y, quotRelU x y ->
 quotRel (quotIn x) (quotIn y) := 
fun x y H => min1 (repr_quotRelT x y H).

Lemma quotRel_repr : forall {Hset : IsHSet G}
{Hprop : forall x y : G, IsHProp (rrel x y)}
{Hmon : IsCMonoid G} {Hcompat : IsLInvariant G} {Hreg : forall x, IsLRegular G x},
forall x y, quotRel (quotIn x) (quotIn y) -> quotRelU x y.
Proof.
intros ? ? ? ? ? ? ?. apply minus1Trunc_rect_nondep.
apply quotRelT_repr.
apply Hprop.
Defined.

Context {Hset : IsHSet G} {Hprop : forall x y : G, IsHProp (rrel x y)}
{Hmon : IsCMonoid G}
{Hcompat : IsLInvariant G} {Hreg : forall x, IsLRegular G x}.

Definition quotOMag : LR_sig := BuildLR_sig (quotU G)
 (BuildLR_Class _ (@gop (quotMag G)) quotRel).

Instance quot_lcompat : IsLInvariant quotOMag.
Proof.
red.
apply quotU_ind.
intros;apply trunc_forall.
intros z. red. apply (quotU_ind G (fun x : quotOMag => forall y : quotOMag, 
rrel x y -> rrel (@gop quotOMag (class_of equivU z) x) 
                 (@gop quotOMag (class_of equivU z) y))).
intros;apply trunc_forall.
intros x. apply (quotU_ind G (fun y => 
@rrel quotOMag (class_of equivU x) y ->
rrel (@gop quotOMag (class_of equivU z) (class_of equivU x))
     (@gop quotOMag (class_of equivU z) y))).
intros;apply trunc_forall.
intros y H.

destruct x as [xa xb];destruct y as [ya yb];destruct z as [za zb].
unfold rrel in H; simpl in H. unfold rrel;simpl.
apply quotRel_repr in H. apply repr_quotRel.
unfold addU;simpl. red;red in H;simpl;simpl in H.
pattern (gop (gop za xa) (gop zb yb)). apply transport with
(gop (gop za zb) (gop xa yb)). ssrapply (@ast_use G);reflexivity.
pattern (gop (gop za ya) (gop zb xb)). apply transport with
(gop (gop za zb) (gop ya xb)). ssrapply (@ast_use G);reflexivity.
apply Hcompat. assumption.
Defined.

Instance quot_lregular : forall x, IsLRegular quotOMag x.
Proof.
intros. eapply rinverse_lregular. apply _.
Defined.

Lemma embed_rel : forall x y : G, rrel x y ->
 @rrel quotOMag (quotEmbed x) (quotEmbed y).
Proof.
intros. unfold quotEmbed. apply repr_quotRel. red;simpl.
apply transport with y. apply inverse. apply gid.
pattern (gop x gidV). apply transport with x. apply inverse. apply gid.
assumption.
Defined.

Lemma embed_rel_back : forall x y : G, @rrel quotOMag (quotEmbed x) (quotEmbed y)
 -> rrel x y.
Proof.
intros ? ? H. unfold quotEmbed in H.
apply quotRel_repr in H.
apply transport with (gop y gid). apply gid.
pattern x;apply transport with (gop x gid). apply gid.
apply H.
Defined.

End WithRel.

End GroupOfCMono.


