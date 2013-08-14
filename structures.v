
Require Import Overture.
Require Import hit.minus1Trunc.

Open Scope path_scope.
Open Scope equiv_scope.

Definition law T := T -> T -> T.
Definition neq {T} : relation T := fun x y => ~ x=y.

Module Symbols.
(* Symbols for notations *)

Class Gop   (T : Type) := gop   : law T.
Class Plus  (T : Type) := plus  :> Gop T.
Class Mult  (T : Type) := mult  :> Gop T.

Class Rel   (T : Type) := rrel  : relation T.
Class Leq   (T : Type) := leq   :> Rel T.
Class Lt    (T : Type) := lt    :> Rel T.
Class Apart (T : Type) := apart :> Rel T.

Infix "&"  := gop (at level 50, left associativity).
Notation "(&)" := gop (only parsing).
Infix "+"  := plus.
Notation "(+)" := plus (only parsing).
Infix "°"  := mult (at level 40, left associativity). (* same as * *)
Notation "(°)" := mult (only parsing).

(* scalar/vector multiplication
Infix "*" := times.
Notation "(*)" := times (only parsing)
*)

Infix "~>" := rrel (at level 60, no associativity).
Notation "(~>)" := rrel (only parsing).
Infix "<=" := leq.
Notation "(<=)" := leq (only parsing).
Infix "<"  := lt.
Notation "(<)" := lt (only parsing).
Infix "<>" := apart.
Notation "(<>)" := apart (only parsing).
Infix "!=" := neq (at level 70, no associativity). (*same as <> *)
Notation "(!=)" := neq (only parsing).

End Symbols.


Module Signatures.
Export Symbols.

(*********** PRERING ******************)

Record LL_Class (T : Type) := BuildLL_Class {
LL_L1 : law T;
LL_L2 : law T
}.

Class Prering (T : Type) := prering : LL_Class T.
Instance prering_plus : forall {T}, Prering T -> Plus T := LL_L1.
Instance prering_mult : forall {T}, Prering T -> Mult T := LL_L2.

Notation "(+ °)" := prering (only parsing).


(******************* 2 Relations ***************)

(*
Used for apart + lt
In general we put apart before leq before lt in signatures
*)

Record RR_Class (T : Type) := BuildRR_Class {
RR_R1 : relation T;
RR_R2 : relation T
}.

Class ApartLt T := apartlt : RR_Class T.

Instance apartlt_apart : forall {T}, ApartLt T -> Apart T := RR_R1.
Instance apartlt_lt : forall {T}, ApartLt T -> Lt T := RR_R2.

Notation "(<> <)" := apartlt (only parsing).

Class LeqLt T := leqlt : RR_Class T.

Instance leqlt_leq : forall {T}, LeqLt T -> Leq T := RR_R1.
Instance leqlt_lt  : forall {T}, LeqLt T -> Lt T := RR_R2.

(* define others as needed *)

(******************* 3 Relations ****************)

(*
apart, leq, lt
*)

Record RRR_Class (T : Type) := BuildRRR_Class {
RRR_R1 : relation T;
RRR_R2 : relation T;
RRR_R3 : relation T
}.

Class FullRelation T := fullrelation : RRR_Class T.

Instance fullrel_apartlt {T} (R : FullRelation T) : ApartLt T
 := BuildRR_Class T (RRR_R1 T R) (RRR_R3 T R).
(*canonical structure? coercion?*)

Instance fullrel_apart {T} (R : FullRelation T) : Apart T := _.
Instance fullrel_lt {T} (R : FullRelation T) : Lt T := _.
Instance fullrel_leq {T} (R : FullRelation T) : Leq T := RRR_R2 T R.

(***************** LR ***********************)

Record LR_Class (T : Type) := BuildLR_Class {
LR_L : law T;
LR_R : relation T
}.

Class OpRel T := oprel : LR_Class T.

Instance oprel_op : forall {T}, OpRel T -> Gop T := LR_L.
Instance oprel_rel : forall {T}, OpRel T -> Rel T := LR_R.


Class PlusApart T := plusapart : OpRel T.

Notation "(+ <>)" := plusapart.

Instance plusapart_plus : forall {T}, PlusApart T -> Plus T := @oprel_op.
Instance plusapart_apart : forall {T}, PlusApart T -> Apart T := @oprel_rel.

Class MultApart T := multapart : OpRel T.

Notation "(° <>)" := multapart.

Instance multapart_mult : forall {T}, MultApart T -> Mult T := @oprel_op.
Instance multapart_apart : forall {T}, MultApart T -> Apart T := @oprel_rel.


(*others as needed*)

(******************* LLR ***********************)

Record LLR_Class (T : Type) := BuildLLR_Class {
LLR_L1 : law T;
LLR_L2 : law T;
LLR_R : relation T
}.

Class PreringRel T := preringrel : LLR_Class T.
Class Prefield T := prefield :> PreringRel T.

Instance preringrel_prering {T} (G : PreringRel T) : Prering T :=
BuildLL_Class _ (LLR_L1 _ G) (LLR_L2 _ G).

Instance preringrel_rel : forall {T}, PreringRel T -> Rel T := LLR_R.

Instance prefieldApart : forall {T}, Prefield T -> Apart T := @preringrel_rel.

Instance prefield_plusapart : forall {T}, Prefield T -> PlusApart T
 := fun T L => BuildLR_Class T (+) (<>).
Instance prefield_multapart : forall {T}, Prefield T -> MultApart T
 := fun T L => BuildLR_Class T (°) (<>).


(****************** LLRR *******************)

(*
relations are apartness + lt
*)

Record LLRR_Class (T : Type) := BuildLLRR_Class {
LLRR_L1 : law T;
LLRR_L2 : law T;
LLRR_R1 : relation T;
LLRR_R2 : relation T
}.

Class PreringStrict T := preringstrict : LLRR_Class T.

Instance preringstrict_prefield : forall {T}, PreringStrict T -> Prefield T
 := fun T G => BuildLLR_Class T (LLRR_L1 T G) (LLRR_L2 T G) (LLRR_R1 T G).

Instance preringstrict_strict :  forall {T}, PreringStrict T -> ApartLt T
 := fun T G => BuildRR_Class T (LLRR_R1 T G) (LLRR_R2 T G).

(* etc *)

(****************** LLRRR *******************)

(*
NB: used for ordered fields: 2 laws + apartness + partial order + strict order
*)

Record LLRRR_Class (T : Type) := BuildLLRRR_Class {
LLRRR_L1 : law T;
LLRRR_L2 : law T;
LLRRR_R1 : relation T;
LLRRR_R2 : relation T;
LLRRR_R3 : relation T
}.

Class PreringFull T := preringfull : LLRRR_Class T.

Instance preringfull_strict : forall {T}, PreringFull T -> PreringStrict T
 := fun T G => BuildLLRR_Class T (LLRRR_L1 T G) (LLRRR_L2 T G)
                                 (LLRRR_R1 T G) (LLRRR_R3 T G).

Instance preringfull_fullrel : forall {T}, PreringFull T -> FullRelation T
 := fun T G => BuildRRR_Class T (LLRRR_R1 T G) (LLRRR_R2 T G) (LLRRR_R3 T G).

(* etc *)

End Signatures.


Module Magma.
Export Signatures.

Class Associative {T} (G : Gop T) := associative : 
forall x y z : T, gop x (gop y z) = gop (gop x y) z.

Class Commutative {T} (G : Gop T) := commutative : 
forall x y : T, gop x y = gop y x.

Class IsSemigroup {T} (G : Gop T) := BuildIsSemigroup {
sg_assoc :> Associative G;
sg_comm :> Commutative G
}.

Class Left_id {T} (G : Gop T) (e : T) := left_id : 
forall x : T, gop e x = x.
Class Right_id {T} (G : Gop T) (e : T) := right_id : 
forall x : T, gop x e = x.

Class IsId {T} (G : Gop T) (e : T) := BuildIsId {
id_is_left :> Left_id G e;
id_is_right :> Right_id G e
}.

Class Identity {T:Type} (G : Gop T) := BuildIdentity {
g_id : T;
g_idP :> IsId G g_id
}.
Existing Instance g_idP.

Arguments g_id {_ _ _}.
Arguments g_idP {_ _ _}.

Class IsMonoid {T} (G : Gop T) := BuildIsMonoid {
monoid_is_sg :> IsSemigroup G;
monoid_id :> Identity G
}.

Definition gid {T} {G : Gop T} {Hg : IsMonoid G} : Identity G := _.
Definition gidV {T} {G : Gop T} {Hg : IsMonoid G} : T := @g_id _ _ gid.
Instance gidP {T} {G : Gop T} {Hg : IsMonoid G} : IsId G gidV := _.

Class Lcancel {T} (G : Gop T) (a : T) : Type := left_cancel : 
forall b c : T, gop a b = gop a c -> b = c.
Class Rcancel {T} (G : Gop T) (a : T) : Type := right_cancel : 
forall b c : T, gop b a = gop c a -> b = c.
Class Cancel {T} (G : Gop T) (a : T) : Type := BuildCancel {
Left_cancel :> Lcancel G a;
Right_cancel :> Rcancel G a
}.

Class IsCMonoid {T} (G : Gop T) := BuildIsCMonoid {
cmonoid_is_monoid :> IsMonoid G;
cmonoid_cancel :> forall a : T, Cancel G a
}.

(*
Usually we would require G to be a monoid, with the left_inverse property being gop x y = gid
By doing things this way, we gain
- less complicated coercion paths if G comes from say a field or something
- more ease of use:
  if we need gop x y = gid we use unicity of identity elements, then since IsId is a class instance resolution suffices
  if we need gop (gop x y) z = z we directly apply the IsInverse hypothesis
*)
Class Linverse {T} (G : Gop T) (x y : T) : Type
 := left_inverse :> IsId G (gop x y).
Class Rinverse {T} (G : Gop T) (x y : T) : Type
 := right_inverse :> IsId G (gop y x).

Class IsInverse {T} (G : Gop T) (x y : T) : Type := BuildIsInverse {
inverse_left :> Linverse G x y;
inverse_right :> Rinverse G x y
}.

Record Inverse {T} (G : Gop T) (x : T) := BuildInverse {
inverse_val : T;
inverse_pr : IsInverse G x inverse_val
}.
Existing Instance inverse_pr.

Arguments inverse_val {_ _ _} _.

Class IsGroup {T} (G : Gop T) := BuildIsGroup {
group_is_cmonoid :> IsCMonoid G;
gopp : forall x, Inverse G x
}.

Definition goppV : forall {T} {G : Gop T} {Hg : IsGroup G}, T -> T
 := fun T G Hg x => inverse_val (gopp x).
Instance goppP : forall {T} {G : Gop T} {Hg : IsGroup G}, forall x:T,
 IsInverse G x (goppV x) := _.

Class IsMorphism {T} (G : Gop T) {T'} (G' : Gop T') (f : T -> T')
 := ismorphism : forall x y, f (gop x y) = gop (f x) (f y).

End Magma.

Module Relation.
Export Signatures.

Class RelationProp {T} (R : Rel T) :=
 relationprop :> forall x y : T, IsHProp (rrel x y).

Class Equivalence {T} (R : Rel T) := BuildEquivalence {
equivalence_refl :> Reflexive R;
equivalence_symm :> Symmetric R;
equivalence_trans :> Transitive R
}.

Class Antisymmetric {T} (R : Leq T) :=
 antisymmetric : forall x y : T, x <= y -> y <= x -> x=y.

Class StrongAntisymmetric {T : Type} (R : Lt T) :=
 strongantisymm : forall x y : T, x < y -> y < x -> Empty.

Class Irreflexive {T} (R : Rel T) := 
 irrefl : forall x : T, rrel x x -> Empty.

Class Poset {T} (R : Leq T) := BuildPoset {
order_trans :> Transitive R;
order_refl :> Reflexive R;
order_antisymm :> Antisymmetric R
}.

(*NB: do not use < here, it becomes ambiguous when used with an apartness relation*)
Class Cotransitive {T} (R : Rel T) := 
 iscotransitive : forall x y : T, rrel x y -> forall z,
   minus1Trunc (rrel x z \/ rrel z y).

Class Apartness {T} (R : Apart T) := BuildApartness {
apart_irrefl :> Irreflexive R;
apart_symm :> Symmetric R;
apart_cotrans :> Cotransitive R;
apart_tight : forall x y : T, ~ x <> y -> x=y
}.

Class Linear {T} (R : Leq T) := 
 islinear : forall x y : T, minus1Trunc (x <= y \/ y <= x).

Class ConstrLinear {T} (R : Leq T) := 
 isconstrlinear : forall x y : T, x <= y \/ y <= x.

Class ConstrCotransitive {T} (R : Lt T) := constrcotransitive
 : forall x y : T, x < y -> forall z, x < z \/ z < y.

Class Trichotomic {T} (R : Lt T) := trichotomic
 : forall x y : T, x<y \/ x=y \/ y<x.

Class Decidable {T} (R : Rel T) := 
 decidable : forall x y : T, (rrel x y)+(~rrel x y).

Class StrictOrder {T} (R : Lt T) := BuildStrictOrder {
strictorder_irrefl :> Irreflexive R;
strictorder_trans :> Transitive R
}.


Class IsUpper {T} (R : Leq T) (P : T -> Type) (m : T) := 
isupper : forall x, P x -> x <= m.
Class IsLower {T} (R : Leq T) (P : T -> Type) (m : T) := 
islower : forall x, P x -> m <= x.

Class IsMaximum {T} (R : Leq T) P (m : T) := BuildIsMaximum {
maximum_upper :> IsUpper R P m;
maximum_verifies : P m
}.

Class IsMinimum {T} (R : Leq T) P (m : T) := BuildIsMinimum {
minimum_lower :> IsLower R P m;
minimum_verifies : P m
}.

Class IsSupremum {T} (R : Leq T) P (m : T) :=
 issupremum :> IsMinimum R (IsUpper R P) m.

Instance supremum_upper : forall T (r : Leq T) P m {H : IsSupremum r P m},
 IsUpper r P m := fun _ _ _ => @minimum_verifies _ _ _.

Class IsInfimum {T} (R : Rel T) P (m : T) :=
 isinfimum :> IsMaximum R (IsLower R P) m.

Instance infimum_lower : forall T (r : Leq T) P m {H : IsInfimum r P m},
 IsLower r P m := fun _ _ _ => @maximum_verifies _ _ _.

(**TODO**)
(*
Record Upper (r : LeqRelation) P := BuildUpper {
upper_val :> r;
upper_is_upper :> IsUpper r P upper_val
}.
Existing Instance upper_is_upper.
Arguments upper_val {_ _} _.

Record Lower (r : LeqRelation) P := BuildLower {
lower_val :> r;
lower_is_lower :> IsLower r P lower_val
}.
Existing Instance lower_is_lower.
Arguments lower_val {_ _} _.

Record Maximum (r : LeqRelation) P := BuildMaximum {
maximum_val :> r;
maximum_is_maximum :> IsMaximum r P maximum_val
}.
Existing Instance maximum_is_maximum.
Arguments maximum_val {_ _} _.

Record Minimum (r : LeqRelation) P := BuildMinimum {
minimum_val :> r;
minimum_is_minimum :> IsMinimum r P minimum_val
}.
Existing Instance minimum_is_minimum.
Arguments minimum_val {_ _} _.

Definition Supremum (r : LeqRelation) P : Type := Minimum r (IsUpper r P).
Instance supremum_is_supremum : forall r P (m : Supremum r P),
 IsSupremum r P m.
Proof. intros; red; apply _. Defined.

Definition Infimum (r : LeqRelation) P := Maximum r (IsLower r P).
Instance infimum_is_infimum : forall r P (m : Infimum r P),
 IsInfimum r P m.
Proof. intros; red; apply _. Defined.

Definition doubleton {T : Type} (a b : T) (x : T) : Type :=
minus1Trunc (a=x \/ b=x).

Definition Supremum2 (r : Relation) (a b : r) := Supremum r (doubleton a b).
Definition Infimum2  (r : Relation) (a b : r) := Infimum  r (doubleton a b).
Definition Maximum2  (r : Relation) (a b : r) := Maximum  r (doubleton a b).
Definition Minimum2  (r : Relation) (a b : r) := Minimum  r (doubleton a b).

Class IsLattice (r : LeqRelation) := BuildIsLattice {
lattice_is_poset :> IsPoset r;
lattice_has_sup2 : forall a b, Supremum2 r a b;
lattice_has_inf2 : forall a b, Infimum2  r a b
}.
*)

Class TotalOrder {T} (R : Leq T) := BuildTotalOrder {
totalorder_poset :> Poset R;
totalorder_linear :> Linear R
}.

Class ConstrTotalOrder {T} (R : Leq T) := BuildConstrTotalOrder {
constrtotalorder_poset :> Poset R;
constrtotalorder_linear :> ConstrLinear R
}.


(*
In classical logic we can construct a strict order from a poset (resp poset from strict order) by taking x<y iff x<=y and x<>y (resp x<=y if x<y or x=y)
In constructive logic the inequality becomes apartness and the two iffs are not equivalent (2nd is stronger from its \/)
We end up using the first one.
cf math classes for working example (src/interfaces/orders.v > FullPartialOrder)
*)

Class PseudoOrder {T} (R : ApartLt T) := BuildPseudoOrder {
pseudoorder_apart :> Apartness (<>);
pseudoorder_antisym : forall x y : T, x<y -> y<x -> Empty;
pseudoorder_cotrans :> Cotransitive (<);
apart_iff_total_lt : forall x y : T, x <> y <-> (x<y \/ y<x)
}.

Class FullPoset {T} (R : FullRelation T) := BuildFullPartialOrder {
fullpartial_apart :> Apartness (<>);
fullpartial_poset :> Poset (<=);
fullpartial_trans :> Transitive (<);
lt_iff_le_apart : forall x y : T, x < y <-> (x <= y /\ x <> y)
}.

Class FullPseudoOrder {T} (R : FullRelation T) := BuildFullPseudoOrder {
fullpseudoorder_pseudo :> PseudoOrder (<> <);
le_iff_not_lt_flip : forall x y : T, x <= y <-> ~ y < x
}.


Class IsMorphism {T} (R : Rel T) {T'} (R' : Rel T') (f : T -> T')
 := ismorphism : forall x y, rrel x y -> rrel (f x) (f y).
Class IsReflecting {T} (R : Rel T) {T'} (R' : Rel T') (f : T -> T')
 := isreflecting : forall x y, rrel (f x) (f y) -> rrel x y.
Class IsEmbedding {T} (R : Rel T) {T'} (R' : Rel T') (f : T -> T')
 := BuildIsEmbedding {
embedding_is_morphism :> IsMorphism R R' f;
embedding_is_reflecting :> IsReflecting R R' f
}.

Class IsBinMorphism {T1} (R1 : Rel T1) {T2} (R2 : Rel T2) {T'} (R' : Rel T')
  (f : T1 -> T2 -> T') := isbinmorphism
 : forall x x', rrel x x' -> forall y y', rrel y y'
   -> rrel (f x y) (f x' y').
Class IsBinReflecting {T1} (R1 : Rel T1) {T2} (R2 : Rel T2) {T'} (R' : Rel T')
  (f : T1 -> T2 -> T') := isbinreflecting
 : forall x x' y y', rrel (f x y) (f x' y')
   -> minus1Trunc (rrel x x' \/ rrel y y').

End Relation.

Module OrderedMagma.
Export Magma.
Export Relation.

(* LInvariant: forall z x y, x <= y -> z x <= z y *)
Class IsLInvariant {G} (R : OpRel G)
 := islinvariant :> forall z : G, IsMorphism (~>) (~>) (gop z).
Class IsRInvariant {G} (R : OpRel G)
 := isrinvariant :> forall z : G, IsMorphism (~>) (~>) (fun a : G => gop a z).
Class IsInvariant {G} (R : OpRel G) := BuildIsInvariant {
isinvariant_left :> IsLInvariant R;
isinvariant_right :> IsRInvariant R
}.

(* Compat: forall x x' y y', x <= x', y <= y' -> x + y <= x' + y' *)
Class IsCompat {G} (R : OpRel G)
 := iscompat :> IsBinMorphism (~>) (~>) (~>) (&).

(* LRegular a: forall x y, a x <= a y -> x <= y *)
Class IsLRegular {G} (R : OpRel G) (a : G) :=
 islregular :> IsReflecting (~>) (~>) (gop a).
Class IsRRegular {G} (R : OpRel G) (a : G) :=
 isrregular :> IsReflecting (~>) (~>) (fun b : G => gop b a).
Class IsRegular {G} (R : OpRel G) (a : G) := BuildIsRegular {
isreg_left :> IsLRegular R a;
isreg_right :> IsRRegular R a
}.

(* BinRegular : forall x x' y y', x+y <= x'+y' -> x<=x' or y<=y' *)
Class IsBinRegular {G} (R : OpRel G) :=
 isbinregular :> IsBinReflecting (~>) (~>) (~>) (&).
(*
NB: in semirings, we expect that (a ° _) is morphism for <= forall a >= 0
and embedding for < for a > 0
*)

End OrderedMagma.

Module Ring.
Export Magma.


Class Ldistributes {G} (L : Prering G) := ldistributes : 
forall a b c : G, a ° (b+c) = (a°b) + (a°c).
Class Rdistributes {G} (L : Prering G) := rdistributes : 
forall a b c : G, (b+c) ° a = (b°a) + (c°a).
Class Distributes {G} (L : Prering G) := BuildDistributes {
distributes_left :> Ldistributes L;
distributes_right :> Rdistributes L
}.

Class IsSemiring {G} (L : Prering G) := BuildIsSemiring {
semiring_plus :> IsCMonoid (+);
semiring_mult :> IsMonoid (°);
semiring_distributes :> Distributes L
}.

Definition Zero {G} {L : Prering G} {H : IsSemiring L} : Identity (+)
 := @gid _ (+) _.
Definition ZeroV {G} {L : Prering G} {H : IsSemiring L} : G := @gidV _ (+) _.
Instance ZeroP {G} {L : Prering G} {H : IsSemiring L} : IsId (+) ZeroV
 := gidP.

Definition One {G} {L : Prering G} {H : IsSemiring L} : Identity (°)
 := @gid _ (°) _.
Definition OneV {G} {L : Prering G} {H : IsSemiring L} : G := @gidV _ (°) _.
Instance OneP {G} {L : Prering G} {H : IsSemiring L} : IsId (°) OneV
 := gidP.

Class IsRing {G} (L : Prering G) := BuildIsRing {
ring_is_semir :> IsSemiring L;
r_opp : forall x, Inverse (+) x
}.

Instance ring_is_group : forall {T} (G : Prering T) {Hr : IsRing G},
 IsGroup (+).
Proof.
intros;apply BuildIsGroup. apply _.
apply r_opp.
Defined.

Definition ropp {T} {L : Prering T} {G : IsRing L}
 : forall x, Inverse (+) x := gopp.

Definition roppV : forall {T} {L : Prering T} {G : IsRing L}, T -> T
 := fun T L G => goppV.
Instance roppP {T} {L : Prering T} {G : IsRing L} : forall x:T,
 IsInverse (+) x (roppV x) := goppP.

Class IsIntegralDomain {T} (L : Prering T)
 := BuildIsIntegralDomain {
integral_ring :> IsRing L;
integral_pr :> forall a : T, neq ZeroV a -> forall b : T, neq ZeroV b ->
   neq ZeroV (a°b);
intdom_neq : @neq T ZeroV OneV
}.

Class IsStrictIntegral {T} (L : Prering T) {G : IsSemiring L}
 := isstrictintegral : forall a b : T, ZeroV = a°b
   -> minus1Trunc (ZeroV=a \/ ZeroV=b).

End Ring.

Module Lattice.
Export Ring Relation OrderedMagma.

Class IsIdempotent {G} (L : Gop G) := isidempotent :> forall x : G, gop x x = x.

Class IsLatticeMag {G} (L : Gop G) := BuildIsLatticeMag {
lattice_mag_sg :> IsSemigroup L;
lattice_mag_idem :> IsIdempotent L
}.

Class IsLatticeMeetR {G} (L : OpRel G) :=
 islatticemeet : forall x y : G, rrel x y <-> gop x y = x.
Class IsLatticeJoinR {G} (L : OpRel G) :=
 islatticejoin : forall x y : G, rrel x y <-> gop y x = y.

Class IsMeetSemiLattice {G} (L : OpRel G) := BuildIsMeetSemiLattice {
semilattice_meet_mag :> IsLatticeMag (&);
semilattice_meet_rel :> IsLatticeMeetR L
}.

Class IsJoinSemiLattice {G} (L : OpRel G) := BuildIsJoinSemiLattice {
semilattice_join_mag :> IsLatticeMag (&);
semilattice_join_rel :> IsLatticeJoinR L
}.

(*
Record prelattice := BuildPreLattice {
prelattice_t :> Type;
prelattice_relC : relation prelattice_t;
prelattice_meetC : law prelattice_t;
prelattice_joinC : law prelattice_t
}.

Canonical Structure prelattice_rel (l : prelattice) : Relation
 := BuildRelation l (prelattice_relC l).
Coercion prelattice_rel : prelattice >-> Relation.

Definition prelattice_meet (l : prelattice) : LR_sig
 := BuildLR_sig l (BuildLR_Class _ (prelattice_meetC l) (prelattice_relC l)).
Definition prelattice_join (l : prelattice) : LR_sig
 := BuildLR_sig l (BuildLR_Class _ (prelattice_joinC l) (prelattice_relC l)).

Class IsFullLattice (l : prelattice) := BuildIsLattice {
islattice_meet :> IsMeetSemiLattice (prelattice_meet l);
islattice_join :> IsJoinSemiLattice (prelattice_join l)
}.
*)

End Lattice.

Module Field.
Export Ring.
Export Relation.
Export OrderedMagma.

Class IsDecField {F} (L : Prering F) := BuildIsDecField {
decfield_is_ring :> IsRing L;
decfield_neq : @neq F ZeroV OneV;
dec_inv : F -> F;
dec_inv0 : dec_inv ZeroV = ZeroV;
dec_inv_ok : forall x : F, neq ZeroV x ->
             IsInverse (°) x (dec_inv x)
}.

Class IsField {F} (L : Prefield F) := BuildIsField {
field_is_apart :> Apartness (<>);
field_is_ring :> IsRing (+ °);
field_add :> IsBinRegular (+ <>);
field_mult :> IsBinRegular (° <>);
field_neq : @apart F _ ZeroV OneV;
finv : forall x : F, ZeroV <> x -> Inverse (°) x;
field_inv_neq : forall x, Inverse (°) x -> ZeroV <> x
}.

Definition finvV {F} {L : Prefield F} {Hf : IsField L}
 : forall x : F, ZeroV <> x -> F := fun x H => inverse_val (finv x H).
Instance finvP {F} {L : Prefield F} {Hf : IsField L}
 : forall (x : F) (H :ZeroV <> x), IsInverse (°) x (finvV x H) := _.

End Field.

Module OrderedRing.
Export Ring Relation OrderedMagma.


(**TODO**)
(*
Class IsPosPreserving {G} (L : PreringRel G)
 := ispospreserving : forall zero : Identity (+),
      forall x y : G, @rrel G (gid zero) x
                   -> @rrel G (gid zero) y 
                   -> @rrel G (gid zero) (x°y).

Class IsSemiringOrder (G : PreringRel) := BuildIsSemiringOrder {
srorder_po :> IsPoset G;
srorder_partial_minus : forall x y : G, rrel x y -> exists z, y = x + z;
srorder_plus :> forall z : G, IsEmbedding (plus z);
nonneg_mult_compat :> IsPosPreserving G
}.

Class IsStrictSemiringOrder (G : PreringRel) := BuildIsStrictSemiringOrder {
strict_srorder_so :> IsStrictOrder G;
strict_srorder_partial_minus : forall x y : G, rrel x y -> exists z, y = x + z;
strict_srorder_plus :> forall z : G, IsEmbedding (plus z);
pos_mult_compat :> IsPosPreserving G
}.

Class IsPseudoSemiringOrder (G : PreringStrict) := BuildIsPseudoSemiringOrder {
pseudo_srorder_strict :> IsPseudoOrder G;
pseudo_srorder_partial_minus : forall x y : G, ~y < x -> exists z, y = x + z;
pseudo_srorder_plus :> forall z : G,
        @IsEmbedding (RR_to_R2 G) (RR_to_R2 G) (plus z);
pseudo_srorder_mult_ext :> IsBinRegular (LLRR_to_L2R1 G);
pseudo_srorder_pos_mult_compat :> IsPosPreserving (LLRR_to_LLR2 G)
}.

Class FullPseudoSemiringOrder (G : PreringFull) :=
  BuildIsFullPseudoSemiringOrder {
full_pseudo_srorder_pso :> IsPseudoSemiringOrder G;
full_pseudo_srorder_le_iff_not_lt_flip : forall x y : G, x <= y <-> ~y < x
}.
*)


End OrderedRing.




