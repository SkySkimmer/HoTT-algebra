
Require Import HoTT.

Require Import FunextAxiom UnivalenceAxiom.

Require Import hit.minus1Trunc.

Open Scope path_scope.
Open Scope equiv_scope.

Module GroupLike.

Definition law (A : Type) := A -> A -> A.

Instance law_set : forall A, IsHSet A -> IsHSet (law A).
Proof.
intros.
apply @trunc_arrow. exact _.
apply trunc_arrow.
Defined.

Record magma := BuildMagma {
gcarr :> Type;
gop : law gcarr;
magma_is_set :> IsHSet gcarr
}.

Definition magma_sigma : sigT (fun carr =>
   sigT (fun _ : law carr => IsHSet carr)) <~> magma.
Proof.
issig BuildMagma gcarr gop magma_is_set.
Defined.

Arguments gop {m} x y.

Class Associative (G : magma) : Type := associative : 
forall x y z : G, gop x (gop y z) = gop (gop x y) z.

Instance assoc_prop : forall {G : magma}, IsHProp (Associative G).
Proof.
intros.
apply hprop_forall. intro;apply hprop_forall. intro;apply hprop_forall.
intro.
apply hprop_allpath. apply magma_is_set.
Defined.

Class Commutative (G : magma) : Type := commutative : 
forall x y : G, gop x y = gop y x.

Instance comm_prop : forall {G}, IsHProp (Commutative G).
Proof.
intros.
apply hprop_forall. intro;apply hprop_forall.
intro.
apply hprop_allpath. apply magma_is_set.
Defined.

Class IsSemigroup (G : magma) := BuildIsSemigroup {
sg_assoc :> Associative G;
sg_comm :> Commutative G
}.

Record semigroup := BuildSemigroup {
sg_mag :> magma;
sg_is_sg :> IsSemigroup sg_mag
}.

Definition is_sg_sg {G : magma} {Hsg : IsSemigroup G} : semigroup
 := BuildSemigroup G Hsg.

Canonical Structure is_sg_sg.
Existing Instance sg_is_sg.

Instance issg_prop : forall {G}, IsHProp (IsSemigroup G).
Proof.
intro.
apply (@trunc_equiv' (sigT (fun _ : Associative G => Commutative G))).
issig (BuildIsSemigroup G) (@sg_assoc G) (@sg_comm G).
apply @trunc_sigma. apply _. intro. apply _.
Defined.

Class Left_id {G : magma} (e : G) := is_left_id : 
forall x : G, gop e x = x.
Class Right_id {G : magma} (e : G) := is_right_id : 
forall x : G, gop x e = x.

Class IsId {G : magma} (e : G) := BuildIsId {
id_left :> Left_id e;
id_right :> Right_id e
}.

Lemma id_unique : forall G : magma, forall e : G, 
IsId e -> forall e': G, IsId e' -> e = e'.
Proof.
intros.
apply (@concat _ _ (gop e e')).
 apply inverse;apply id_right.
 apply id_left.
Defined.

Instance id_prop : forall G e, IsHProp (@IsId G e).
Proof.
intros.
apply (@trunc_equiv' (sigT (fun _ : Left_id e => Right_id e))).
issig (BuildIsId G e) (@id_left G e) (@id_right G e).

apply @trunc_sigma.
apply @hprop_forall. exact _. intros.
apply hprop_allpath.
apply (magma_is_set G).
intro H;clear H.
apply @hprop_forall. exact _. intros.
apply hprop_allpath.
apply (magma_is_set G).
Defined.

Lemma left_id_id : forall {G : semigroup} {e : G}, Left_id e -> IsId e.
Proof.
intros. split;auto.
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

Instance idT_prop : forall G, IsHProp (sigT (@IsId G)).
Proof.
intro G.
apply hprop_inhabited_contr. intro X.
apply BuildContr with X.
intro Y.
destruct X as [e He];destruct Y as [e' He'].
apply path_sigma with (id_unique _ _ He _ He').
apply id_prop.
Defined.

Class IsMonoid (G : magma) := BuildIsMonoid {
monoid_is_sg :> IsSemigroup G;
gid : G;
monoid_id :> IsId gid
}.

Record monoid := BuildMonoid {
monoid_mag :> magma;
monoid_is_monoid :> IsMonoid monoid_mag
}.

Arguments gid {_ _}.

Definition is_mono_mono {G : magma} {Hmono : IsMonoid G} : monoid
 := BuildMonoid G Hmono.

Canonical Structure is_mono_mono.
Existing Instance monoid_is_monoid.

Instance ismonoid_prop : forall {G}, IsHProp (IsMonoid G).
Proof.
intro.
apply (@trunc_equiv' (sigT (fun _ : IsSemigroup G => 
                    sigT (@IsId G)))).
issig (BuildIsMonoid G) (@monoid_is_sg G) (@gid G) (@monoid_id G).
apply @trunc_sigma. apply _.
intro. apply _.
Defined.

Canonical Structure monoid_sg : forall {G : monoid}, semigroup.
Proof.
intro.
apply BuildSemigroup with G.
apply _.
Defined.

Coercion monoid_sg : monoid >-> semigroup.

Class Lcancel {G : magma} (a : G) : Type := left_cancel : 
forall b c : G, gop a b = gop a c -> b = c.
Class Rcancel {G : magma} (a : G) : Type := right_cancel : 
forall b c : G, gop b a = gop c a -> b = c.
Class Cancel {G : magma} (a : G) : Type := BuildCancel {
Left_cancel :> Lcancel a;
Right_cancel :> Rcancel a
}.

Lemma left_cancel_cancel : forall {G}, Commutative G ->
forall a : G, Lcancel a -> Cancel a.
Proof.
intros ? Hcomm ? X. split;auto.
red;intros ? ? X0.
red in X. apply X.
eapply concat. apply Hcomm. eapply concat. apply X0. apply Hcomm.
Defined.

Instance cancelling_prop : forall G a, IsHProp (@Cancel G a).
Proof.
intros.
apply (@trunc_equiv' (sigT (fun _ : Lcancel a => Rcancel a))).
issig (BuildCancel _ a) (@Left_cancel _ a) (@Right_cancel _ a).
apply @trunc_sigma;[|intro C;clear C];
repeat (apply @hprop_forall;[ exact _ | intros]);
apply hprop_allpath;
apply magma_is_set.
Defined.

Class IsCMonoid (G : magma) := BuildIsCMonoid {
cmonoid_is_monoid :> IsMonoid G;
cmonoid_cancel :> forall a : G, Cancel a
}.

Record Cmonoid := BuildCMonoid {
cmono_mag :> magma;
cmono_is_cmono :> IsCMonoid cmono_mag
}.

Definition is_cmono_cmono {G : magma} {Hmono : IsCMonoid G} : Cmonoid
 := BuildCMonoid G Hmono.

Canonical Structure is_cmono_cmono.
Existing Instance cmono_is_cmono.

Instance iscmono_prop : forall {G}, IsHProp (IsCMonoid G).
Proof.
intro.
apply (@trunc_equiv' (sigT (fun _ : IsMonoid G => forall a : G, Cancel a))).
issig (BuildIsCMonoid G) (@cmonoid_is_monoid G) (@cmonoid_cancel G).
apply @trunc_sigma.
apply _.
intro; apply _.
Defined.

Canonical Structure cmono_monoid : forall {G : Cmonoid}, monoid.
Proof.
intro. apply BuildMonoid with G. apply _.
Defined.

Coercion cmono_monoid : Cmonoid >-> monoid.

Class Linverse {G : monoid} (x y : G) : Type := left_inverse : 
gop x y = gid.
Class Rinverse {G : monoid} (x y : G) : Type := right_inverse : 
gop y x = gid.

Class IsInverse {G : monoid} (x y : G) : Type := BuildIsInverse {
inverse_left :> Linverse x y;
inverse_right :> Rinverse x y
}.

Lemma linverse_inverse : forall {G : monoid} (x y : G), 
Linverse x y -> IsInverse x y.
Proof.
intros ? ? ? X;split;auto.
red. eapply concat. apply sg_comm.
apply X.
Defined.

Instance inverse_prop : forall G x y, IsHProp (@IsInverse G x y).
Proof.
intros. 
apply (@trunc_equiv' (sigT (fun _ : Linverse x y => Rinverse x y))).
issig (BuildIsInverse _ x y) (@inverse_left G x y) (@inverse_right G x y).
apply @trunc_sigma;[|intro C;clear C];
apply hprop_allpath; apply magma_is_set.
Defined.

Lemma inverse_symm : forall G, Symmetric (@IsInverse G).
Proof.
red. intros ? ? ? X. split;apply X.
Defined.

Lemma inverse_symm_rw : @IsInverse  = fun G x y => @IsInverse G y x.
Proof.
apply funext_axiom. intro G.
apply funext_axiom. intro x. apply funext_axiom;intro y.
apply univalence_axiom. apply equiv_iff_hprop;apply inverse_symm.
Defined.

Class IsGroup (G : magma) := BuildIsGroup {
group_is_monoid :> IsMonoid G;
gopp : G -> G;
gopp_correct : forall x : G, IsInverse x (gopp x)
}.

Existing Instance gopp_correct.

Record group := BuildGroup {
group_mag :> magma;
group_is_group :> IsGroup group_mag
}.

Definition is_group_group {G : magma} {Hg : IsGroup G} : group
 := BuildGroup G Hg.

Canonical Structure is_group_group.
Existing Instance group_is_group.

Arguments gopp {_ _} _.

Lemma inverse_cancelling : forall {G : monoid}, forall a : G,
 sigT (IsInverse a) -> Cancel a.
Proof.
intros. apply left_cancel_cancel. apply sg_comm.
destruct X as [a' H].
red; intros.
eapply concat;[ | eapply concat;[ apply (ap (gop a') X) | ]].

eapply concat;[ | symmetry;apply sg_assoc].
pattern (gop a' a). eapply transport. symmetry. apply H.
apply inverse. apply monoid_id.

eapply concat;[ apply sg_assoc |].
pattern (gop a' a). eapply transport. symmetry. apply H.
apply monoid_id.
Defined.

Lemma group_is_cancelling : forall {G : group}, forall a : G, Cancel a.
Proof.
intros.
pose (@group_is_monoid G _).
apply inverse_cancelling. exists (gopp a). apply gopp_correct.
Defined.

Instance group_is_cmono : forall {G} {Hg : IsGroup G}, IsCMonoid G.
Proof.
intros;apply BuildIsCMonoid.
apply _.
apply group_is_cancelling.
Defined.

Canonical Structure group_cmono : forall {G : group}, Cmonoid.
Proof.
intro G.
apply BuildCMonoid with G. apply BuildIsCMonoid.
- apply _.
- apply group_is_cancelling.
Defined.

Coercion group_cmono : group >-> Cmonoid.

Lemma inverse_unique : forall {G : monoid}, forall x y : G, IsInverse x y -> 
forall y', IsInverse x y' -> y = y'.
Proof.
intros. apply inverse_cancelling with x. exists y;exact X.
eapply concat. apply X. symmetry. apply X0.
Defined.

Lemma group_inverse_gopp : forall {G : group}, forall x y : G,
 @IsInverse G x y -> gopp x = y.
Proof.
intros. 
apply (@inverse_unique G) with x.
 apply gopp_correct.
 apply X.
Defined.

Lemma gopp_gopp : forall {G : group} (x : G), gopp (gopp x) = x.
Proof.
intros. apply group_inverse_gopp.
apply inverse_symm. apply gopp_correct.
Defined.

Instance gid_inverse : forall G : monoid, @IsInverse G gid gid.
Proof.
intros.
split; apply monoid_id.
Defined.

Lemma gopp_gid : forall G : group, @paths G (gopp gid) gid.
Proof.
intros. apply group_inverse_gopp. apply gid_inverse.
Defined.

Lemma inverse_gop : forall G : monoid, forall x x' : G, IsInverse x x' -> 
forall y y' : G, IsInverse y y' -> IsInverse (gop x y) (gop y' x').
Proof.
intros. apply linverse_inverse. red.
transitivity (gop x (gop (gop y y') x')).

eapply concat. symmetry. apply sg_assoc. apply ap.
apply sg_assoc.

pattern (gop y y'). eapply transport. symmetry. apply X0.
pattern (gop gid x'). eapply transport. symmetry. apply monoid_id.
apply X.
Defined.

Lemma gopp_gop : forall G : group, forall x y : G,
 gopp (gop x y) = gop (gopp y) (gopp x).
Proof.
intros. apply group_inverse_gopp.
apply inverse_gop;apply gopp_correct.
Defined.

Lemma gopp_unique : forall (G : monoid) (opp : G -> G), 
(forall x, IsInverse x (opp x)) -> forall opp' : G -> G, 
(forall x, IsInverse x (opp' x)) -> opp = opp'.
Proof.
intros. apply funext_axiom. intro.
eapply inverse_unique. apply X. apply X0.
Defined.

Instance is_gopp_prop : forall G : monoid, forall opp, 
IsHProp (forall x : G, IsInverse x (opp x)).
Proof.
intros. apply @trunc_forall. apply _. intro. apply _.
Defined.

Instance goppT_prop : forall G : monoid, IsHProp (sigT (fun opp : G -> G => 
forall x, IsInverse x (opp x))).
Proof.
intros.
apply hprop_inhabited_contr. intro X.
apply BuildContr with X.
intro Y.
destruct X as [e He];destruct Y as [e' He'].
apply path_sigma with (gopp_unique _ _ He _ He').
simpl. apply is_gopp_prop.
Defined.

Instance group_prop : forall {G}, IsHProp (IsGroup G).
Proof.
intro;apply (@trunc_equiv' (sigT (fun ismono : IsMonoid G => 
                   (sigT (fun opp : G -> G => forall x, IsInverse x (opp x)))))).
issig (BuildIsGroup G) (@group_is_monoid G) (@gopp G) (@gopp_correct G).

apply @trunc_sigma. apply _.
intro. apply _.
Defined.

End GroupLike.

Module Related.

Record relator := BuildRelator {
runder :> Type;
rrel : relation runder;
relator_set : IsHSet runder;
relator_prop : forall {x y}, IsHProp (rrel x y)
}.

Existing Instance relator_set.
Existing Instance relator_prop.

Arguments rrel {_} _ _.

Class IsTransitive (R : relator) := istrans : Transitive (@rrel R).
Class IsReflexive (R : relator) := isrefl : Reflexive (@rrel R).
Class IsSymmetric (R : relator) := issymm : Symmetric (@rrel R).

Class IsEquivalence (R : relator) := BuildIsEquivalence {
equivalence_refl :> IsReflexive R;
equivalence_symm :> IsSymmetric R;
equivalence_trans :> IsTransitive R
}.

Instance istrans_prop : forall {r}, IsHProp (IsTransitive r).
Proof.
intros.
repeat (apply hprop_forall;intro). apply _.
Defined.

Instance isrefl_prop : forall {r}, IsHProp (IsReflexive r).
Proof.
intros.
repeat (apply hprop_forall;intro). apply _.
Defined.

Instance issymm_prop : forall {r}, IsHProp (IsSymmetric r).
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

Instance isequivalence_prop : forall {r}, IsHProp (IsEquivalence r).
Proof.
intro r.
eapply trunc_equiv'.
apply IsEquivalence_sig.
apply @trunc_sigma. apply _.
intro. apply @trunc_sigma. apply _.
intro;apply _.
Defined.

Class IsAntisymmetric (R : relator) :=
 isantisymm : forall x y : R, rrel x y -> rrel y x -> x = y.

Class IsIrreflexive (R : relator) := 
 isirrefl : forall x : R, rrel x x -> Empty.

Lemma irrefl_neq : forall {R} {Hr : IsIrreflexive R}, 
  forall x y : R, rrel x y -> x = y -> Empty.
Proof.
intros ? ? ? ? ?. intros H. destruct H. apply Hr with x. assumption.
Defined.

Instance isantisymm_prop : forall {r}, IsHProp (IsAntisymmetric r).
Proof.
intros.
repeat (apply hprop_forall;intro). apply hprop_allpath;apply relator_set.
Defined.

Instance isirrefl_prop : forall {r}, IsHProp (IsIrreflexive r).
Proof.
intros.
repeat (apply hprop_forall;intro). apply _.
Defined.

Class IsPoset (R : relator) := BuildIsPoset {
order_trans :> IsTransitive R;
order_refl :> IsReflexive R;
order_antisymm :> IsAntisymmetric R
}.

Definition isposet_sig : forall r, sigT (fun _ : IsTransitive r => 
sigT (fun _ : IsReflexive r => IsAntisymmetric r)) <~> IsPoset r.
Proof.
intro r;
issig (BuildIsPoset r) (@order_trans r) (@order_refl r) (@order_antisymm r).
Defined.

Instance isposet_prop : forall {r}, IsHProp (IsPoset r).
Proof.
intro.
eapply trunc_equiv'.
apply isposet_sig.
apply @trunc_sigma. apply _.
intro. apply @trunc_sigma. apply _.
intro;apply _.
Defined.

Class IsCotransitive (R : relator) := 
 icotrans : forall x y : R, rrel x y -> forall z,
   minus1Trunc (rrel x z \/ rrel y z).

Instance iscotrans_prop : forall {r}, IsHProp (IsCotransitive r).
Proof.
intros.
repeat (apply hprop_forall;intro). apply minus1Trunc_is_prop.
Defined.

Class IsApartness (R : relator) := BuildIsApartness {
apart_irrefl :> IsIrreflexive R;
apart_symm :> IsSymmetric R;
apart_cotrans :> IsCotransitive R
}.

Definition isapart_sig : forall r, sigT (fun _ : IsIrreflexive r =>
sigT (fun _ : IsSymmetric r => IsCotransitive r)) <~> IsApartness r.
Proof.
intros.
issig (BuildIsApartness r) (@apart_irrefl r) (@apart_symm r) (@apart_cotrans r).
Defined.

Instance isapart_prop : forall {r}, IsHProp (IsApartness r).
Proof.
intro;eapply trunc_equiv'.
apply isapart_sig.
apply @trunc_sigma. apply _.
intro. apply @trunc_sigma. apply _.
intro;apply _.
Defined.

Class IsLinear (R : relator) := 
 islinear : forall x y : R, minus1Trunc (rrel x y \/ rrel y x).

Instance islinear_prop : forall {r}, IsHProp (IsLinear r).
Proof.
intro. repeat (apply hprop_forall;intro). apply minus1Trunc_is_prop.
Defined.

Class IsStrictLinear (R : relator) := 
 isstrictlinear : forall x y : R, rrel x y -> forall z, rrel x z \/ rrel z y.
(* not HProp *)

Definition relator_inverse : relator -> relator.
Proof.
intro R.
apply BuildRelator with R (fun x y => rrel y x).
apply _. apply _.
Defined.

Notation "R ^" := (relator_inverse R) (at level 3) : relator_scope.

Open Scope relator_scope.

Instance inverse_trans : forall {R} {Htrans : IsTransitive R}, 
  IsTransitive (R ^).
Proof.
intros. repeat intro.
eapply Htrans. apply X0. apply X.
Defined.

Instance inverse_refl : forall {R} {Hrefl : IsReflexive R}, 
  IsReflexive (R ^).
Proof.
repeat intro. apply Hrefl.
Defined.

Instance inverse_symm : forall {R} {Hsymm : IsSymmetric R}, 
  IsSymmetric (R ^).
Proof.
repeat intro. apply Hsymm;assumption.
Defined.

Instance inverse_irrefl : forall {R} {Hirrefl : IsIrreflexive R}, 
  IsIrreflexive (R ^).
Proof.
intros. eapply Hirrefl.
Defined.

Record ordered_mag := BuildOrderedMagma {

}.

End Related.

Module RingLike.
Export GroupLike.

Record magma2 := BuildMagma2 {
rcarr :> Type;
radd : law rcarr;
rmult : law rcarr;
magma2_is_set :> IsHSet rcarr
}.

Definition magma2_sigma : sigT (fun carr => sigT (fun _ : law carr => 
  sigT (fun _ : law carr => IsHSet carr))) <~> magma2.
Proof.
issig BuildMagma2 rcarr radd rmult magma2_is_set.
Defined.

Canonical Structure mag2_add (G : magma2) : magma.
Proof.
apply BuildMagma with (rcarr G).
exact (radd G).
apply magma2_is_set.
Defined.

Canonical Structure mag2_mult : magma2 -> magma.
Proof.
intro G. apply BuildMagma with (rcarr G).
exact (rmult G).
apply magma2_is_set.
Defined.

Arguments radd {_} _ _.
Arguments rmult {_} _ _.

Infix "+" := radd.
Infix "°" := rmult (at level 40). (*level 40 is same as "*" *)

Class Ldistributes (G : magma2) := left_distributes : 
forall a b c : G, a ° (b+c) = (a°b) + (a°c).
Class Rdistributes (G : magma2) := right_distributes : 
forall a b c : G, (b+c) ° a = (b°a) + (c°a).
Class Distributes (G : magma2) : Type := BuildDistributes {
distrib_left :> Ldistributes G;
distrib_right :> Rdistributes G
}.

Instance distrib_prop : forall {G}, IsHProp (Distributes G).
Proof.
intro G. apply (@trunc_equiv' (sigT (fun _ : Ldistributes G => Rdistributes G))).
issig (BuildDistributes G) (@distrib_left G) (@distrib_right G).
apply @trunc_sigma;[|intro C;clear C];
repeat (apply hprop_forall;intro);
apply hprop_allpath; apply magma2_is_set.
Defined.

Class IsSemiring (G : magma2) := BuildIsSemiring {
semiring_add :> IsMonoid (mag2_add G);
semiring_mult :> IsMonoid (mag2_mult G);
semiring_cancel :> forall a : (mag2_add G), Cancel a;
semiring_distributes :> Distributes G
}.

Record semiring := BuildSemiring {
semir_mag2 :> magma2;
semir_is_semir :> IsSemiring semir_mag2
}.

Definition is_semir_semir {G : magma2} {Hsr : IsSemiring G} : semiring
 := BuildSemiring G Hsr.

Canonical Structure is_semir_semir.
Existing Instance semir_is_semir.

Canonical Structure semiring_add_monoid : forall {G : semiring}, monoid.
Proof.
intro. apply BuildMonoid with (mag2_add G).
apply _.
Defined.

Canonical Structure semiring_mult_monoid : forall {G : semiring}, monoid.
Proof.
intro. apply BuildMonoid with (mag2_mult G).
apply _.
Defined.


Instance issemir_prop : forall {G}, IsHProp (IsSemiring G).
Proof.
intro.
apply (@trunc_equiv' (sigT (fun _ : IsMonoid (mag2_add G) => 
  sigT (fun _ : IsMonoid (mag2_mult G) => 
    sigT (fun _ : forall a : mag2_add G, Cancel a => 
      Distributes G))))).
issig (BuildIsSemiring G) (@semiring_add G) (@semiring_mult G)
  (@semiring_cancel G) (@semiring_distributes G).

repeat (apply @trunc_sigma;[|intro C;clear C]);apply _.
Defined.

Definition Zero {G : semiring} : G := @gid (mag2_add G) _.

Definition One {G : semiring} : G := @gid (mag2_mult G) _.

Lemma rmult_0_l : forall {G : semiring}, 
forall x : G, Zero ° x = Zero.
Proof.
intros.
apply semiring_cancel with (Zero ° x).
eapply concat. Focus 2. apply (@inverse _ _ (Zero ° x)).
apply (@monoid_id (mag2_add G)).
apply (@concat _ _ ((Zero + Zero) ° x) _).
symmetry. apply semiring_distributes.
apply ap10. apply ap.
apply (@monoid_id (mag2_add _)).
Defined.

Lemma rmult_0_r : forall {G : semiring}, 
forall x : G, x ° Zero = Zero.
Proof.
intros.
apply semiring_cancel with (x ° Zero).
eapply concat. Focus 2. apply (@inverse _ _ (x ° Zero)).
apply (@monoid_id (mag2_add G)).
apply (@concat _ _ (x ° (Zero + Zero)) _).
symmetry. apply semiring_distributes.
apply ap.
apply (@monoid_id (mag2_add _)).
Defined.


Class IsRing (G : magma2) := BuildIsRing {
ring_is_semir :> IsSemiring G;
ropp : G -> G;
ropp_correct :> forall x : G,
      @IsInverse (BuildMonoid _ semiring_add) x (ropp x)
}.

Record ring := BuildRing {
ring_mag2 :> magma2;
ring_is_ring :> IsRing ring_mag2
}.

Definition is_ring_ring {G : magma2} {Hr : IsRing G}
 : ring := BuildRing G Hr.

Canonical Structure is_ring_ring.
Existing Instance ring_is_ring.


Instance ring_is_group : forall {G : magma2} {Hr : IsRing G},
 IsGroup (mag2_add G).
Proof.
intros. apply BuildIsGroup with semiring_add ropp.
apply ropp_correct.
Defined.

Canonical Structure ring_group : ring -> group
 := fun G => BuildGroup _ (@ring_is_group G _).

Instance isring_prop : forall {G}, IsHProp (IsRing G).
Proof.
intro.
apply (@trunc_equiv' (sigT (fun semir : IsSemiring G => 
  sigT (fun opp : G -> G => 
    forall x, @IsInverse (BuildMonoid _ semiring_add) x (opp x))))).
issig (BuildIsRing G) (@ring_is_semir G) (@ropp G) (@ropp_correct G).

apply @trunc_sigma. apply _.
intro. apply (goppT_prop (BuildMonoid _ semiring_add)).
Defined.

Canonical Structure ring_semiring : ring -> semiring.
Proof.
intro G.
apply BuildSemiring with G.
apply _.
Defined.

Coercion ring_semiring : ring >-> semiring.

Class IsIntegralDomain (G : magma2) := BuildIsIntegralDomain {
integral_ring :> IsRing G;
integral_pr :> forall a b : G, a ° b = Zero -> ((a = Zero) + (b = Zero))
}.

Record integralDomain := BuildIntegralDomain {
intdom_mag2 :> magma2;
intdom_is_intdom :> IsIntegralDomain intdom_mag2
}.

Definition is_intdom_intdom {G : magma2} {Hsr : IsIntegralDomain G}
 : integralDomain := BuildIntegralDomain G Hsr.

Canonical Structure is_intdom_intdom.
Existing Instance intdom_is_intdom.

Lemma intdom_partial_cancels_left : forall {G : integralDomain}, 
forall a : G, (a = Zero -> Empty) ->
 forall b c, a°b = a°c -> b = c.
Proof.
intros.
assert (a ° (b + (ropp c)) = Zero).
eapply concat.
apply (@semiring_distributes G _). 
pose (@semiring_cancel G _). 
apply (@Right_cancel _ _ (c0 (a ° c))).
apply (@concat _ _ (a°b + (a° (ropp c) + a°c))).
simpl. symmetry. apply (@sg_assoc (mag2_add G) _).
eapply concat;[|symmetry;apply monoid_id].
eapply concat;[|apply X].
eapply concat;[ apply ap | apply (@monoid_id (mag2_add G) _)].
eapply concat. symmetry.
apply semiring_distributes.
eapply concat;[apply ap | apply rmult_0_r].
apply ropp_correct.
apply integral_pr in X0.
destruct X0. destruct H;auto.
apply (@Right_cancel _ _ (@semiring_cancel G _ (ropp c))).
eapply concat. apply p.
symmetry. apply ropp_correct.
Defined.

Lemma intdom_partial_cancels_right :forall {G : integralDomain}, 
forall a : G, (a = Zero -> Empty) ->
 forall b c, b°a = c°a -> b = c.
Proof.
intros. apply intdom_partial_cancels_left with a;auto.
eapply concat;[|eapply concat;[apply X|]];apply (@sg_comm (mag2_mult G) _).
Defined.

(** Field needs appartness **)
(*
Class IsField (G : mag2 + appartness) := BuildIsField {
field_is_appart :> appart_ok (BuildAppart ..);
field_is_ring :> IsRing (BuildMagma2 ..);
finv : forall x : G, appart x Zero -> G;
finv_correct :> forall x H, is_inverse {mult} x (finv x H)
}.
*)

End RingLike.








