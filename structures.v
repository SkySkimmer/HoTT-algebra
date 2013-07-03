
Require Import HoTT.
Require Import hit.minus1Trunc.

Open Scope path_scope.
Open Scope equiv_scope.

Module Magma.

Definition law (A : Type) := A -> A -> A.

Record class (G : Type) := BuildClass {
classV :> law G
}.

Arguments BuildClass {_} _.
Arguments classV {_} _ _ _.

Record magma := BuildMagma {
gcarr :> Type;
gclass : class gcarr
}.

Definition gop : forall {G : magma}, law G := fun G => match G with
 | BuildMagma _ (BuildClass l) => l end.

Arguments gop {G} _ _ : simpl never.

Class IsMereMagma (G : magma) := BuildIsMereMagma {
meremagma_is_set :> IsHSet G
}.

Definition easyMagma (G : Type) (l : law G) : magma := 
BuildMagma G (BuildClass l).

Class Associative (G : magma) : Type := associative : 
forall x y z : G, gop x (gop y z) = gop (gop x y) z.

Class Commutative (G : magma) : Type := commutative : 
forall x y : G, gop x y = gop y x.

Class IsSemigroup (G : magma) := BuildIsSemigroup {
sg_assoc :> Associative G;
sg_comm :> Commutative G
}.

Record semigroup := BuildSemigroup {
sg_mag :> magma;
sg_is_sg :> IsSemigroup sg_mag
}.

Canonical Structure is_sg_sg {G : magma} {Hsg : IsSemigroup G} : semigroup
 := BuildSemigroup G Hsg.

Existing Instance sg_is_sg.

Class Left_id {G : magma} (e : G) := is_left_id : 
forall x : G, gop e x = x.
Class Right_id {G : magma} (e : G) := is_right_id : 
forall x : G, gop x e = x.

Class IsId {G : magma} (e : G) := BuildIsId {
id_left :> Left_id e;
id_right :> Right_id e
}.

Record Identity (G : magma) := BuildIdentity {
identity_val :> G;
identity_pr : IsId identity_val
}.
Existing Instance identity_pr.

Class IsMonoid (G : magma) := BuildIsMonoid {
monoid_is_sg :> IsSemigroup G;
monoid_id : Identity G
}.

Record monoid := BuildMonoid {
monoid_mag :> magma;
monoid_is_monoid :> IsMonoid monoid_mag
}.

Definition gid {G : monoid} : Identity G := @monoid_id G G.
Definition gidV {G : monoid} : G := gid.

Instance gid_id : forall G, IsId (@gid G) := fun G => _.

Canonical Structure is_mono_mono {G : magma} {Hmono : IsMonoid G} : monoid
 := BuildMonoid G Hmono.

Existing Instance monoid_is_monoid.

Canonical Structure monoid_sg (G : monoid) : semigroup := 
BuildSemigroup G _.

Coercion monoid_sg : monoid >-> semigroup.

Class Lcancel {G : magma} (a : G) : Type := left_cancel : 
forall b c : G, gop a b = gop a c -> b = c.
Class Rcancel {G : magma} (a : G) : Type := right_cancel : 
forall b c : G, gop b a = gop c a -> b = c.
Class Cancel {G : magma} (a : G) : Type := BuildCancel {
Left_cancel :> Lcancel a;
Right_cancel :> Rcancel a
}.

Class IsCMonoid (G : magma) := BuildIsCMonoid {
cmonoid_is_monoid :> IsMonoid G;
cmonoid_cancel :> forall a : G, Cancel a
}.

Record Cmonoid := BuildCMonoid {
cmono_mag :> magma;
cmono_is_cmono :> IsCMonoid cmono_mag
}.

Canonical Structure is_cmono_cmono {G : magma} {Hmono : IsCMonoid G} : Cmonoid
 := BuildCMonoid G Hmono.

Existing Instance cmono_is_cmono.

Canonical Structure cmono_monoid (G : Cmonoid) : monoid :=
BuildMonoid G _.

Coercion cmono_monoid : Cmonoid >-> monoid.

(*
Usually we would require G to be a monoid, with the left_inverse property being gop x y = gid
By doing things this way, we gain
- less complicated coercion paths if G comes from say a field or something
- more ease of use:
  if we need gop x y = gid we use unicity of identity elements, then since IsId is a class instance resolution suffices
  if we need gop (gop x y) z = z we directly apply the IsInverse hypothesis
*)
Class Linverse {G : magma} (x y : G) : Type := left_inverse : IsId (gop x y).
Class Rinverse {G : magma} (x y : G) : Type := right_inverse : IsId (gop y x).

Existing Instances left_inverse right_inverse.

Class IsInverse {G : magma} (x y : G) : Type := BuildIsInverse {
inverse_left :> Linverse x y;
inverse_right :> Rinverse x y
}.

Record Inverse {G : magma} (x : G) := BuildInverse {
inverse_val :> G;
inverse_is_inverse :> IsInverse x inverse_val
}.
Existing Instance inverse_is_inverse.

Class IsGroup (G : magma) := BuildIsGroup {
group_is_cmonoid :> IsCMonoid G;
g_opp : forall x : G, Inverse x
}.

Record group := BuildGroup {
group_mag :> magma;
group_is_group :> IsGroup group_mag
}.

Definition gopp {G : group} : forall x : G, Inverse x := @g_opp G G.

Canonical Structure is_group_group {G : magma} {Hg : IsGroup G} : group
 := BuildGroup G Hg.

Existing Instance group_is_group.

Definition gopp' {G : magma} {Hg : IsGroup G} : forall x : G, Inverse x := gopp.

Definition goppV {G : group} : G -> G := fun x => gopp x.
Definition goppV' {G : magma} {Hg : IsGroup G} : G -> G := goppV.

Canonical Structure group_cmono (G : group) : Cmonoid :=
BuildCMonoid G _.

Coercion group_cmono : group >-> Cmonoid.

Instance gopp_correct : forall (G : group) x, @IsInverse G x (gopp x)
 := fun _ _ => _.

Class IsMorphism {G H : magma} (f : G -> H)
 := ismorphism : forall x y : G, f (gop x y) = gop (f x) (f y).

End Magma.

Module Related.

Record class (T : Type) := BuildClass {
classV : relation T
}.

Record relator := BuildRelator {
runder :> Type;
rrelC : class runder
}.

Definition rrel {r : relator} : relation r := 
match r with | BuildRelator _ (BuildClass cmp) => cmp end.

Arguments rrel {_} _ _ : simpl never.
Arguments BuildClass {_} _.
Arguments classV {_} _ _ _.

Definition easyRelator : forall T : Type, relation T -> relator := 
fun T r => BuildRelator T (BuildClass r).

Class relatorProp (r : relator) :=
 relatorprop : forall x y : r, IsHProp (rrel x y).
Existing Instance relatorprop.

Class IsMereRelator (r : relator) := BuildIsMereRelator {
mererelator_is_set :> IsHSet r;
mererelator_is_prop :> relatorProp r
}.

Class IsTransitive (R : relator) := istrans : Transitive (@rrel R).
Class IsReflexive (R : relator) := isrefl : Reflexive (@rrel R).
Class IsSymmetric (R : relator) := issymm : Symmetric (@rrel R).

Class IsEquivalence (R : relator) := BuildIsEquivalence {
equivalence_refl :> IsReflexive R;
equivalence_symm :> IsSymmetric R;
equivalence_trans :> IsTransitive R
}.

Class IsAntisymmetric (R : relator) :=
 isantisymm : forall x y : R, rrel x y -> rrel y x -> x = y.

Class IsIrreflexive (R : relator) := 
 isirrefl : forall x : R, rrel x x -> Empty.

Class IsPoset (R : relator) := BuildIsPoset {
order_trans :> IsTransitive R;
order_refl :> IsReflexive R;
order_antisymm :> IsAntisymmetric R
}.

Class IsStrictLinear (R : relator) := 
 isstrictlinear : forall x y : R, rrel x y -> forall z,
   minus1Trunc (rrel x z \/ rrel z y).

Class IsCotransitive (R : relator) := 
 iscotrans :> IsStrictLinear R.

Class IsApartness (R : relator) := BuildIsApartness {
apart_irrefl :> IsIrreflexive R;
apart_symm :> IsSymmetric R;
apart_cotrans :> IsCotransitive R;
apart_tight : forall x y : R, ~ rrel x y -> x=y
}.

Class IsLinear (R : relator) := 
 islinear : forall x y : R, minus1Trunc (rrel x y \/ rrel y x).

Class IsConstrLinear (R : relator) := 
 isconstrlinear : forall x y : R, rrel x y \/ rrel y x.

Class IsConstrStrictLinear (R : relator) := isconstrstrictlinear
 : forall x y : R, rrel x y -> forall z,rrel x z \/ rrel z y.

Class IsDecidable (R : relator) := 
 isdecidable : forall x y : R, (rrel x y)+(~rrel x y).

Class IsStrictPoset (R : relator) := BuildIsStrictPoset {
strictposet_irrefl :> IsIrreflexive R;
strictposet_trans :> IsTransitive R
}.

Record relator2 := BuildRelator2 {
runder2 :> Type;
rrelC2_1 : class runder2;
rrelC2_2 : class runder2
}.

Definition relator2_1 (r : relator2) : relator
 := BuildRelator r (rrelC2_1 r).
Definition rrel2_1 {r : relator2} : relation r := @rrel (relator2_1 r).

Definition relator2_2 (r : relator2) : relator
 := BuildRelator r (rrelC2_2 r).
Definition rrel2_2 {r : relator2} : relation r := @rrel (relator2_2 r).

Class IsTight (r : relator2) :=
 istight : forall x y : r, rrel2_1 x y <-> ~ rrel2_2 y x.

Class IsPoset2 (r : relator2) := BuildIsPoset2 {
poset2_1 :> IsPoset (relator2_1 r);
poset2_2 :> IsStrictPoset (relator2_2 r);
poset2_tight :> IsTight r
}.

Class IsUpper (r : relator) (P : r -> Type) (m : r) := 
isupper : forall x, P x -> rrel x m.
Class IsLower (r : relator) (P : r -> Type) (m : r) := 
islower : forall x, P x -> rrel m x.

Class IsMaximum (r : relator) P (m : r) := BuildIsMaximum {
maximum_upper :> IsUpper r P m;
maximum_verifies : P m
}.

Class IsMinimum (r : relator) P (m : r) := BuildIsMinimum {
minimum_lower :> IsLower r P m;
minimum_verifies : P m
}.

Class IsSupremum (r : relator) P (m : r) :=
 issupremum : IsMinimum r (IsUpper r P) m.

Instance supremum_upper : forall r P m {H : IsSupremum r P m}, IsUpper r P m := 
fun _ _ _ H => @minimum_verifies _ _ _ H.

Class IsInfimum (r : relator) P (m : r) :=
 isinfimum : IsMaximum r (IsLower r P) m.

Instance infimum_lower : forall r P m {H : IsInfimum r P m}, IsLower r P m := 
fun _ _ _ H => @maximum_verifies _ _ _ H.

Record Upper (r : relator) P := BuildUpper {
upper_val :> r;
upper_is_upper :> IsUpper r P upper_val
}.
Existing Instance upper_is_upper.
Arguments upper_val {_ _} _.

Record Lower (r : relator) P := BuildLower {
lower_val :> r;
lower_is_lower :> IsLower r P lower_val
}.
Existing Instance lower_is_lower.
Arguments lower_val {_ _} _.

Record Maximum (r : relator) P := BuildMaximum {
maximum_val :> r;
maximum_is_maximum :> IsMaximum r P maximum_val
}.
Existing Instance maximum_is_maximum.
Arguments maximum_val {_ _} _.

Record Minimum (r : relator) P := BuildMinimum {
minimum_val :> r;
minimum_is_minimum :> IsMinimum r P minimum_val
}.
Existing Instance minimum_is_minimum.
Arguments minimum_val {_ _} _.

Definition Supremum (r : relator) P : Type := Minimum r (IsUpper r P).
Instance supremum_is_supremum : forall r P (m : Supremum r P),
 IsSupremum r P m.
Proof. intros. red. apply _. Defined.

Definition Infimum (r : relator) P := Maximum r (IsLower r P).
Instance infimum_is_infimum : forall r P (m : Infimum r P),
 IsInfimum r P m.
Proof. intros;red;apply _. Defined.

Definition doubleton {T : Type} (a b : T) (x : T) : Type :=
minus1Trunc (a=x \/ b=x).

Definition Supremum2 (r : relator) (a b : r) := Supremum r (doubleton a b).
Definition Infimum2  (r : relator) (a b : r) := Infimum  r (doubleton a b).
Definition Maximum2  (r : relator) (a b : r) := Maximum  r (doubleton a b).
Definition Minimum2  (r : relator) (a b : r) := Minimum  r (doubleton a b).

Class IsLattice (r : relator) := BuildIsLattice {
lattice_is_poset :> IsPoset r;
lattice_has_sup2 : forall a b, Supremum2 r a b;
lattice_has_inf2 : forall a b, Infimum2  r a b
}.

Class IsTotalOrder (r : relator) := BuildIsTotalOrder {
totalorder_is_poset :> IsPoset r;
totalorder_linear :> IsLinear r
}.

Class IsConstrTotalOrder (r : relator) := BuildIsConstrTotalOrder {
constrtotalorder_is_poset :> IsPoset r;
constrtotalorder_linear :> IsConstrLinear r
}.

Class IsMorphism {r r' : relator} (f : r -> r')
 := ismorphism : forall x y : r, rrel x y -> rrel (f x) (f y).
Class IsReflecting {r r' : relator} (f : r -> r')
 := isreflecting : forall x y : r, rrel (f x) (f y) -> rrel x y.
Class IsEmbedding {r r' : relator} (f : r -> r') := BuildIsEmbedding {
embedding_is_morphism :> IsMorphism f;
embedding_is_reflecting :> IsReflecting f
}.

Class IsBinMorphism {r1 r2 r' : relator} (f : r1 -> r2 -> r') := isbinmorphism
 : forall x x' : r1, rrel x x' -> forall y y' : r2, rrel y y'
   -> rrel (f x y) (f x' y').
Class IsBinReflecting {r1 r2 r' : relator} (f : r1 -> r2 -> r')
 := isbinreflecting : forall x x' y y', rrel (f x y) (f x' y')
   -> minus1Trunc (rrel x x' \/ rrel y y').

Definition pathRel (T : Type) : relator := easyRelator T paths.

End Related.

Module OrderedMagma.
Export Magma.
Export Related.

Record oMag := BuildOMag {
ocarr :> Type;
olawC : Magma.class ocarr;
orelC : Related.class ocarr
}.

(*
Declaring as canonical structure allows us to do something like
forall G : oMag, forall x y : G, gop x y = ...
Declaring as coercion allows us to use our predicates on magmas: IsMonoid, etc
*)
Canonical Structure omag_mag (G : oMag) : magma := 
BuildMagma G (olawC G).
Coercion omag_mag : oMag >-> magma.

Canonical Structure omag_rel (G : oMag) : relator := 
BuildRelator G (orelC G).
Coercion omag_rel : oMag >-> relator.

Class IsLInvariant (G : oMag)
 := islcompat :> forall z : G, IsMorphism (gop z).
Class IsRInvariant (G : oMag)
 := isrcompat :> forall z : G, IsMorphism (fun a : G => gop a z).
Class IsInvariant (G : oMag) := BuildIsInvariant {
invariant_left :> IsLInvariant G;
invariant_right :> IsRInvariant G
}.

Class IsCompat (G : oMag) := iscompat :> IsBinMorphism (@gop G).

Class IsLRegular (G : oMag) (a : G) :=
 islregular :> IsReflecting (gop a).
Class IsRRegular (G : oMag) (a : G) :=
 isrregular :> IsReflecting (fun b : G => gop b a).
Class IsRegular (G : oMag) (a : G) := BuildIsRegular {
isreg_left :> IsLRegular G a;
isreg_right :> IsRRegular G a
}.

Class IsBinRegular (G : oMag) := isbinregular :> IsBinReflecting (@gop G).
(*
NB: in semirings, we expect that (a ° _) is morphism for <= forall a >= 0
and embedding for < for a > 0
*)

End OrderedMagma.

Module Ring.
Export Magma.

(* consider using 
radd :> magma;
rmult : Magma.class radd
instead? *)
Record prering := BuildPrering {
rcarr :> Type;
raddC : Magma.class rcarr;
rmultC : Magma.class rcarr
}.

Definition easyPrering : forall G : Type, law G -> law G -> prering := 
fun G a m => BuildPrering G (BuildClass a) (BuildClass m).

Canonical Structure prering_add (G : prering) : magma :=
BuildMagma (rcarr G) (raddC G).

Canonical Structure prering_mult (G : prering) : magma :=
BuildMagma (rcarr G) (rmultC G).

Definition rplus {G : prering} : law G := @gop (prering_add G).
Definition rmult {G : prering} : law G := @gop (prering_mult G).

Arguments rplus {_} _ _ : simpl never.
Arguments rmult {_} _ _ : simpl never.

Infix "+" := (@rplus _).
Infix "°" := (@rmult _) (at level 40).

Class Ldistributes (G : prering) := left_distributes : 
forall a b c : G, a ° (b+c) = (a°b) + (a°c).
Class Rdistributes (G : prering) := right_distributes : 
forall a b c : G, (b+c) ° a = (b°a) + (c°a).
Class Distributes (G : prering) : Type := BuildDistributes {
distrib_left :> Ldistributes G;
distrib_right :> Rdistributes G
}.

Class IsSemiring (G : prering) := BuildIsSemiring {
semiring_add :> IsCMonoid (prering_add G);
semiring_mult :> IsMonoid (prering_mult G);
semiring_distributes :> Distributes G
}.

Record semiring := BuildSemiring {
semir_mag2 :> prering;
semir_is_semir :> IsSemiring semir_mag2
}.

Canonical Structure is_semir_semir {G : prering} {Hsr : IsSemiring G} : semiring
 := BuildSemiring G Hsr.

Existing Instance semir_is_semir.

Canonical Structure semiring_add_cmonoid (G : semiring) : Cmonoid :=
BuildCMonoid (prering_add G) _.

Canonical Structure semiring_mult_monoid (G : semiring) : monoid :=
BuildMonoid (prering_mult G) _.

Definition Zero {G : semiring} : Identity (prering_add G) :=
 @gid (semiring_add_cmonoid G).
Definition ZeroV {G : semiring} : prering_add G := Zero.

Definition Zero' {G : prering} {Hg : IsSemiring G} : Identity (prering_add G)
 := Zero.
Definition ZeroV' {G : prering} {Hg : IsSemiring G} : prering_add G := Zero.

Definition One {G : semiring} : Identity (prering_mult G) :=
 @gid (semiring_mult_monoid G).
Definition OneV {G : semiring} : prering_mult G := One.

Definition One' {G : prering} {Hg : IsSemiring G} : Identity (prering_mult G)
 := One.
Definition OneV' {G : prering} {Hg : IsSemiring G} : prering_mult G := One.

Class IsRing (G : prering) := BuildIsRing {
ring_is_semir :> IsSemiring G;
r_opp : forall x : G, @Inverse (prering_add G) x
}.

Record ring := BuildRing {
ring_mag2 :> prering;
ring_is_ring :> IsRing ring_mag2
}.

Canonical Structure is_ring_ring {G : prering} {Hr : IsRing G}
 : ring := BuildRing G Hr.

Existing Instance ring_is_ring.

Instance ring_is_group : forall (G : prering) {Hr : IsRing G},
 IsGroup (prering_add G) := fun G Hr => BuildIsGroup _ _ r_opp.

Canonical Structure ring_group : ring -> group
 := fun G => BuildGroup _ (@ring_is_group G _).

Canonical Structure ring_semiring : ring -> semiring := 
fun G => BuildSemiring G _.

Coercion ring_semiring : ring >-> semiring.

Definition ropp {G : ring} : forall x : G, @Inverse (prering_add G) x
 := @gopp (ring_group G).

Definition ropp' {G : prering} {Hg : IsRing G} := @ropp (@is_ring_ring G _).

Instance ropp_correct : forall (G : ring) x,
 @IsInverse (ring_group G) x (@ropp G x) := @ropp.

Definition roppV {G : ring} : G -> G := fun x => @inverse_val _ _ (ropp x).
Definition roppV' {G : prering} {Hg : IsRing G} : G -> G := roppV.

Notation "x - y" := (rplus x (roppV y)).
Notation "- x" := (roppV x).

Class IsIntegralDomain (G : prering) := BuildIsIntegralDomain {
integral_ring :> IsRing G;
integral_pr :> forall a : G, ~ a = ZeroV -> forall b : G, ~ b = ZeroV ->
   ~ a°b = ZeroV;
intdom_neq :> ~ (@paths G OneV ZeroV)
}.

Record integralDomain := BuildIntegralDomain {
intdom_mag2 :> prering;
intdom_is_intdom :> IsIntegralDomain intdom_mag2
}.

Class IsStrictIntegral (G : semiring) := isstrictintegral
 : forall a b : G, a°b = ZeroV -> minus1Trunc (a=ZeroV \/ b=ZeroV).

Canonical Structure is_intdom_intdom {G : prering} {Hsr : IsIntegralDomain G}
 : integralDomain := BuildIntegralDomain G Hsr.

Existing Instance intdom_is_intdom.

Canonical Structure intdom_ring : integralDomain -> ring := 
fun G => BuildRing G _.

Coercion intdom_ring : integralDomain >-> ring.

End Ring.

Module Lattice.
Export Ring Related OrderedMagma.

Class IsIdempotent (G : magma) := isidempotent :> forall x : G, gop x x = x.

Class IsLatticeMag (G : magma) := BuildIsLatticeMag {
lattice_mag_sg :> IsSemigroup G;
lattice_mag_idem :> IsIdempotent G
}.

Class IsLatticeMeetR (G : oMag) :=
 islatticemeet : forall x y : G, rrel x y <-> gop x y = x.
Class IsLatticeJoinR (G : oMag) :=
 islatticejoin : forall x y : G, rrel x y <-> gop y x = y.

Class IsMeetSemiLattice (G : oMag) := BuildIsMeetSemiLattice {
semilattice_meet_mag :> IsLatticeMag G;
semilattice_meet_rel :> IsLatticeMeetR G
}.

Class IsJoinSemiLattice (G : oMag) := BuildIsJoinSemiLattice {
semilattice_join_mag :> IsLatticeMag G;
semilattice_join_rel :> IsLatticeJoinR G
}.

Record prelattice := BuildPreLattice {
prelattice_t :> Type;
prelattice_relC : Related.class prelattice_t;
prelattice_meetC : Magma.class prelattice_t;
prelattice_joinC : Magma.class prelattice_t
}.

Canonical Structure prelattice_rel (l : prelattice) : relator
 := BuildRelator l (prelattice_relC l).
Coercion prelattice_rel : prelattice >-> relator.

Definition prelattice_meet (l : prelattice) : oMag
 := BuildOMag l (prelattice_meetC l) (prelattice_relC l).
Definition prelattice_join (l : prelattice) : oMag
 := BuildOMag l (prelattice_joinC l) (prelattice_relC l).

Class IsFullLattice (l : prelattice) := BuildIsLattice {
islattice_meet :> IsMeetSemiLattice (prelattice_meet l);
islattice_join :> IsJoinSemiLattice (prelattice_join l)
}.

End Lattice.

Module Field.
Export Ring.
Export Related.
Export OrderedMagma.

Record prefield := BuildPrefield {
prefield_prering :> prering;
prefield_relC : Related.class prefield_prering
}.

Canonical Structure prefield_relator (F : prefield) : relator :=
 BuildRelator F (prefield_relC F).
Coercion prefield_relator : prefield >-> relator.

Definition prefield_add (F : prefield) : oMag :=
 BuildOMag F (raddC (prefield_prering F)) (prefield_relC F).
Definition prefield_mult (F : prefield) : oMag :=
 BuildOMag F (rmultC (prefield_prering F)) (prefield_relC F).

Class IsField (F : prefield) := BuildIsField {
field_is_apart :> IsApartness (prefield_relator F);
field_is_ring :> IsRing F;
field_add :> IsBinRegular (prefield_add F);
field_mult :> IsBinRegular (prefield_mult F);
field_neq : rrel OneV ZeroV;
f_inv : forall x : F, rrel x ZeroV -> @Inverse (prering_mult F) x;
field_inv_back : forall x : F, @Inverse (prering_mult F) x -> rrel x ZeroV
}.

Record field := BuildField {
field_prefield :> prefield;
field_is_field :> IsField field_prefield
}.

Existing Instance field_is_field.
Canonical Structure is_field_field (F : prefield) {Hf : IsField F}
 := BuildField F Hf.

Definition finv {F : field} : forall x : F, rrel x ZeroV ->
 @Inverse (prering_mult F) x := f_inv.
Definition finvV {F : field} : forall x : F, rrel x ZeroV -> prering_mult F
 := finv.

Definition finv' {F} {Hf : IsField F} : forall x : F, rrel x ZeroV ->
 @Inverse (prering_mult F) x := finv.
Definition finvV' {F} {Hf : IsField F} : forall x : F, rrel x ZeroV ->
 (prering_mult F) := finv.


End Field.


Module AlgebraNotation.
Export Magma Related OrderedMagma Ring Field.
(*                            WIP                               *)

Class Le A := le : relation A.
Infix "<=" := le.
Class LeRel := lerel : relator.
Instance getLe : forall {r : LeRel}, Le r := @rrel.

Class Lt A := lt : relation A.
Infix "<" := lt.
Class LtRel := ltrel : relator.
Instance getLt : forall {r : LtRel}, Lt r := @rrel.

Class Apart A := apart : relation A.
Infix "#" := apart.
Class ApartRel := apartrel : relator.
Instance getApart : forall {r : ApartRel}, Apart r := @rrel.

Class OrderRel2 := orderrel2 : relator2.
Instance getLe2 : forall {r : OrderRel2}, Le r := @rrel2_1.
Instance getLt2 : forall {r : OrderRel2}, Lt r := @rrel2_2.

Class Adder A := adder : law A.
Infix "+" := adder.
Class AdderMag := addermag : magma.
Instance getAdderMag : forall {G : AdderMag}, Adder G := @gop.

Class Multer A := multer : law A.
Infix "°" := multer (at level 40). (*level 40 is same as "*" *)
Class MulterMag := multermag : magma.
Instance getMulterMag : forall {G : MulterMag}, Multer G := @gop.

Instance getAdderRPlus : forall {G : prering}, Adder G := @rplus.
Instance getMulterRMult : forall {G : prering}, Multer G := @rmult.

Ltac unfoldNota := unfold le,lt,apart,adder,multer;
  unfold getLe,getLt,getApart,getLe2,getLt2,getAdderMag,getMulterMag,
  getAdderRPlus,getMulterRMult.

(***********  Testing  ******************)
Lemma blob : forall r : prering, forall x y : r, rmult x y = multer x y.
reflexivity. Defined.
Lemma bb0 : (forall r : ApartRel, forall x y : r, rrel x y). Abort.
Lemma bb : forall r : relator, forall x y : r, rrel x y. Abort.
Fail Lemma bb : (forall r : relator, forall x y : r, x # y).
Fail Lemma bb : (forall r : ApartR, forall x y, x < y).
Lemma bb : forall r : OrderRel2, forall x y, x < y -> x <= y. Abort.
Lemma test : forall r : relator2, forall x y : r, rrel2_1 x y.
intros. change OrderRel2 in r. change (x <= y). Abort.

End AlgebraNotation.
