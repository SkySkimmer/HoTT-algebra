
Require Import Overture.
Require Import hit.minus1Trunc.

Open Scope path_scope.
Open Scope equiv_scope.

(*
General note:
some structures (monoids, groups, fields, etc) contain actual values (identity, inverses, etc)
this results in record projections like 
  is_val : forall G:base, IsFoo G -> ValueType G
these will also  be used with packed structures, generating a function
  pack_val : forall G:foo, ValueType (base_of_foo G)
    := fun G => is_val (base_of_foo G) (foo_is_foo G)
One pack_val is defined, all other definitions, properties, etc should use it instead of is_val

This is because foo_is_foo (BuildFoo G Hg) simplifies to Hg, but BuildFoo (base_of_foo G) (foo_is_foo G) does not simplify to G

Note that we usually define pack_val' : forall G:base, IsFoo G -> ValueType G
  := fun G Hg => pack_val (BuildFoo G Hg)
which simplifies to is_val yet works for theorems using pack_val
*)

Definition law T := T -> T -> T.
Definition neq {T} : relation T := fun x y => ~ x=y.

Module Symbols.
(* Symbols for notations *)

Class Plus  (T : Type) := plus  : law T.
Class Mult  (T : Type) := mult  : law T.
Class Leq   (T : Type) := leq   : relation T.
Class Lt    (T : Type) := lt    : relation T.
Class Apart (T : Type) := apart : relation T.

Infix "+"  := plus.
Infix "°"  := mult (at level 40). (* same as * *)
(*Infix "*" := times.*) (*scalar/vector multiplication*)
Infix "<=" := leq.
Infix "<"  := lt.
Infix "<>" := apart.
Infix "!=" := neq (at level 70). (*same as <> *)

End Symbols.


Module Signatures.
Export Symbols.

(****************************************
************* MAGMA *********************
****************************************)

Definition law (T : Type) := T -> T -> T.

Record magma := BuildMagma {
gcarr :> Type;
glaw : law gcarr
}.

Definition gop {G : magma} : law G := 
match G with | BuildMagma _ l => l end.

Arguments gop {G} _ _ : simpl never.

(*
NB: the following notations can still be used in some cases even if the magma isn't given as PlusMagma/MultMagma
ex:
Lemma bb : forall G : magma, forall x y : G, x+y = x.
*)

Definition PlusMagma := magma.
Instance PlusMag_Op : forall G : PlusMagma, Plus G := @gop.

Definition MultMagma := magma.
Instance MultMag_Op : forall G : MultMagma, Mult G := @gop.



(*********** PRERING ******************)

Record LL_Class (T : Type) := BuildLL_Class {
LL_c_L1 : law T;
LL_c_L2 : law T
}.

Record LL_sig := BuildLL_sig {
LL_carr :> Type;
LL_class : LL_Class LL_carr
}.

Notation prering := LL_sig.

Definition makePrering : forall T : Type, law T -> law T -> prering
 := fun T pl ml => BuildLL_sig T (BuildLL_Class _ pl ml).

(* canonical structures? *)
Definition prering_plus (G : prering) : PlusMagma :=
BuildMagma G (LL_c_L1 _ (LL_class G)).
Definition prering_mult (G : prering) : MultMagma :=
BuildMagma G (LL_c_L2 _ (LL_class G)).

Instance rplus {G : prering} : Plus G := @gop (prering_plus G).
Instance rmult {G : prering} : Mult G := @gop (prering_mult G).

(*
we take care to go through gop so that properties on magmas still work
this is expecially useful once we have properties on the specific magmas prering_plus and prering_mult
*)

(****************************************
************* RELATION ******************
****************************************)


Record Relation := BuildRelation {
relcarr :> Type;
rel_r : relation relcarr
}.

Definition rrel {R : Relation} : relation R :=
match R with | BuildRelation _ r => r end.

Arguments rrel {_} _ _ : simpl never.

Definition ApartRelation := Relation.
Definition LeqRelation := Relation.
Definition LtRelation := Relation.

Instance ApartRel_Op : forall R : ApartRelation, Apart R := @rrel.
Instance LeqRel_Op : forall R : LeqRelation, Leq R := @rrel.
Instance LtRel_Op : forall R : LtRelation, Lt R := @rrel.


(******************* 2 Relations ***************)

(*
Used for apart + lt
In general we put apart before leq before lt in signatures
*)

Record RR_Class (T : Type) := BuildRR_Class {
RR_c_R1 : relation T;
RR_c_R2 : relation T
}.

Record RR_sig := BuildRR_sig {
RR_carr :> Type;
RR_class : RR_Class RR_carr
}.

Definition makeRR_sig : forall T : Type, relation T -> relation T -> RR_sig
 := fun T r1 r2 => BuildRR_sig T (BuildRR_Class _ r1 r2).

Definition RR_to_R1 (R : RR_sig) : ApartRelation :=
BuildRelation R (RR_c_R1 _ (RR_class R)).
Definition RR_to_R2 (R : RR_sig) : LtRelation :=
BuildRelation R (RR_c_R2 _ (RR_class R)).

Instance RR_R1 {R : RR_sig} : Apart R := @rrel (RR_to_R1 R).
Instance RR_R2 {R : RR_sig} : Lt R := @rrel (RR_to_R2 R).

(******************* 3 Relations ****************)

(*
apart, leq, lt
*)

Record RRR_Class (T : Type) := BuildRRR_Class {
RRR_c_R1 : relation T;
RRR_c_R2 : relation T;
RRR_c_R3 : relation T
}.

Record RRR_sig := BuildRRR_sig {
RRR_carr :> Type;
RRR_class : RRR_Class RRR_carr
}.

Definition RRR_to_R1 (R : RRR_sig) : ApartRelation :=
BuildRelation R (RRR_c_R1 _ (RRR_class R)).
Definition RRR_to_R2 (R : RRR_sig) : LeqRelation :=
BuildRelation R (RRR_c_R2 _ (RRR_class R)).
Definition RRR_to_R3 (R : RRR_sig) : LtRelation :=
BuildRelation R (RRR_c_R3 _ (RRR_class R)).

Definition RRR_to_R1R3 (R : RRR_sig) : RR_sig :=
BuildRR_sig R (BuildRR_Class R (RRR_c_R1 R (RRR_class R))
                               (RRR_c_R3 R (RRR_class R))).

Instance RRR_R1 {R : RRR_sig} : Apart R := @rrel (RRR_to_R1 R).
Instance RRR_R2 {R : RRR_sig} : Leq R := @rrel (RRR_to_R2 R).
Instance RRR_R3 {R : RRR_sig} : Lt R := @rrel (RRR_to_R3 R).

(***************** LR ***********************)

(*
Both law and relation have no single default meaning
*)

Record LR_Class (T : Type) := BuildLR_Class {
LR_c_L : law T;
LR_c_R : relation T
}.

Record LR_sig := BuildLR_sig {
LR_carr :> Type;
LR_class : LR_Class LR_carr
}.

Definition makeLR_sig : forall T : Type, law T -> relation T -> LR_sig
 := fun T op rel => BuildLR_sig T (BuildLR_Class _ op rel).

Canonical Structure LR_to_L (G : LR_sig) : magma :=
BuildMagma G (LR_c_L _ (LR_class G)).
Coercion LR_to_L : LR_sig >-> magma.

Canonical Structure LR_to_R (G : LR_sig) : Relation :=
BuildRelation G (LR_c_R _ (LR_class G)).
Coercion LR_to_R : LR_sig >-> Relation.

(******************* LLR ***********************)

Record LLR_Class (T : Type) := BuildLLR_Class {
LLR_c_L1 : law T;
LLR_c_L2 : law T;
LLR_c_R : relation T
}.

Record LLR_sig := BuildLLR_sig {
LLR_carr :> Type;
LLR_class : LLR_Class LLR_carr
}.

Definition makeLLR_sig : forall T : Type, law T -> law T -> relation T -> LLR_sig
 := fun T pl ml rel => BuildLLR_sig T (BuildLLR_Class _ pl ml rel).

Canonical Structure LLR_to_LL (G : LLR_sig) : prering :=
BuildLL_sig G (BuildLL_Class _ (LLR_c_L1 _ (LLR_class G))
                               (LLR_c_L2 _ (LLR_class G))).
Coercion LLR_to_LL : LLR_sig >-> prering.

Canonical Structure LLR_to_R (G : LLR_sig) : Relation :=
BuildRelation G (LLR_c_R _ (LLR_class G)).
Coercion LLR_to_R : LLR_sig >-> Relation.

(*not coercions: would be ambiguous*)
Definition LLR_to_L1R (G : LLR_sig) : LR_sig :=
BuildLR_sig G (BuildLR_Class _ (LLR_c_L1 _ (LLR_class G))
                               (LLR_c_R _ (LLR_class G))).
Definition LLR_to_L2R (G : LLR_sig) : LR_sig :=
BuildLR_sig G (BuildLR_Class _ (LLR_c_L2 _ (LLR_class G))
                               (LLR_c_R _ (LLR_class G))).

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

Record LLRR_sig := BuildLLRR_sig {
LLRR_carr :> Type;
LLRR_class : LLRR_Class LLRR_carr
}.

Definition makeLLRR_sig T pl ml r1 r2
 := BuildLLRR_sig T (BuildLLRR_Class T pl ml r1 r2).

Canonical Structure LLRR_to_LL (G : LLRR_sig) : prering :=
BuildLL_sig G (BuildLL_Class _ (LLRR_L1 _ (LLRR_class G))
                               (LLRR_L2 _ (LLRR_class G))).
Coercion LLRR_to_LL : LLRR_sig >-> prering.


Canonical Structure LLRR_to_RR (G : LLRR_sig) : RR_sig :=
BuildRR_sig G (BuildRR_Class _ (LLRR_R1 _ (LLRR_class G))
                               (LLRR_R2 _ (LLRR_class G))).
Coercion LLRR_to_RR : LLRR_sig >-> RR_sig.

Definition LLRR_to_L1R1 (G : LLRR_sig) : LR_sig :=
BuildLR_sig G (BuildLR_Class _ (LLRR_L1 _ (LLRR_class G))
                               (LLRR_R1 _ (LLRR_class G))).

Definition LLRR_to_L1R2 (G : LLRR_sig) : LR_sig :=
BuildLR_sig G (BuildLR_Class _ (LLRR_L1 _ (LLRR_class G))
                               (LLRR_R2 _ (LLRR_class G))).

Definition LLRR_to_L2R1 (G : LLRR_sig) : LR_sig :=
BuildLR_sig G (BuildLR_Class _ (LLRR_L2 _ (LLRR_class G))
                               (LLRR_R1 _ (LLRR_class G))).

Definition LLRR_to_L2R2 (G : LLRR_sig) : LR_sig :=
BuildLR_sig G (BuildLR_Class _ (LLRR_L2 _ (LLRR_class G))
                               (LLRR_R2 _ (LLRR_class G))).

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

Record LLRRR_sig := BuildLLRRR_sig {
LLRRR_carr :> Type;
LLRRR_class : LLRRR_Class LLRRR_carr
}.

Definition makeLLRRR_sig T pl ml r1 r2 r3
 := BuildLLRRR_sig T (BuildLLRRR_Class T pl ml r1 r2 r3).

Canonical Structure LLRRR_to_LL (G : LLRRR_sig) : prering :=
BuildLL_sig G (BuildLL_Class _ (LLRRR_L1 _ (LLRRR_class G))
                                 (LLRRR_L2 _ (LLRRR_class G))).
Coercion LLRRR_to_LL : LLRRR_sig >-> prering.


Canonical Structure LLRRR_to_RRR (G : LLRRR_sig) : RRR_sig :=
BuildRRR_sig G (BuildRRR_Class _ (LLRRR_R1 _ (LLRRR_class G))
                                 (LLRRR_R2 _ (LLRRR_class G))
                                 (LLRRR_R2 _ (LLRRR_class G))).
Coercion LLRRR_to_RRR : LLRRR_sig >-> RRR_sig.

Definition LLRRR_to_LLR1R3 (G : LLRRR_sig) : LLRR_sig :=
BuildLLRR_sig G (BuildLLRR_Class G (LLRRR_L1 _ (LLRRR_class G))
                                   (LLRRR_L2 _ (LLRRR_class G))
                                   (LLRRR_R1 _ (LLRRR_class G))
                                   (LLRRR_R3 _ (LLRRR_class G))).

End Signatures.


Module Magma.
Export Signatures.

Class IsMereMagma (G : magma) := BuildIsMereMagma {
meremagma_is_set :> IsHSet G
}.

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

Arguments identity_val {_} _.
Arguments identity_pr {_} _.

Class IsMonoid (G : magma) := BuildIsMonoid {
monoid_is_sg :> IsSemigroup G;
monoid_id : Identity G
}.

Record monoid := BuildMonoid {
monoid_mag :> magma;
monoid_is_monoid :> IsMonoid monoid_mag
}.

Canonical Structure is_mono_mono {G : magma} {Hmono : IsMonoid G} : monoid
 := BuildMonoid G Hmono.

Existing Instance monoid_is_monoid.

Definition gid {G : monoid} : Identity G := @monoid_id G G.
Definition gidV {G : monoid} : G := gid.

Definition gid' {G : magma} {Hg : IsMonoid G} : Identity G := gid.
Definition gidV' {G : magma} {Hg : IsMonoid G} : G := gid.

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

Module Relation.
Export Signatures.


Class RelationProp (r : Relation) :=
 Relationprop : forall x y : r, IsHProp (rrel x y).
Existing Instance Relationprop.

Class IsMereRelator (r : Relation) := BuildIsMereRelator {
mereRelation_is_set :> IsHSet r;
mereRelation_is_prop :> RelationProp r
}.

Class IsTransitive (R : Relation) := istrans :> Transitive (@rrel R).
Class IsReflexive (R : Relation) := isrefl :> Reflexive (@rrel R).
Class IsSymmetric (R : Relation) := issymm :> Symmetric (@rrel R).

Class IsEquivalence (R : Relation) := BuildIsEquivalence {
equivalence_refl :> IsReflexive R;
equivalence_symm :> IsSymmetric R;
equivalence_trans :> IsTransitive R
}.

Class IsAntisymmetric (R : LeqRelation) :=
 isantisymm : forall x y : R, x <= y -> y <= x -> x = y.

Class IsIrreflexive (R : Relation) := 
 isirrefl : forall x : R, rrel x x -> Empty.

Class IsPoset (R : LeqRelation) := BuildIsPoset {
order_trans :> IsTransitive R;
order_refl :> IsReflexive R;
order_antisymm :> IsAntisymmetric R
}.

Class IsCotransitive (R : LtRelation) := 
 iscotransitive : forall x y : R, x < y -> forall z,
   minus1Trunc (x < z \/ z < y).

Class IsApartness (R : ApartRelation) := BuildIsApartness {
apart_irrefl :> IsIrreflexive R;
apart_symm :> IsSymmetric R;
apart_cotrans :> IsCotransitive R;
apart_tight : forall x y : R, ~ x <> y -> x=y
}.

Class IsLinear (R : LeqRelation) := 
 islinear : forall x y : R, minus1Trunc (x <= y \/ y <= x).

Class IsConstrLinear (R : LeqRelation) := 
 isconstrlinear : forall x y : R, x <= y \/ y <= x.

Class IsConstrCotransitive (R : LtRelation) := isconstrcotransitive
 : forall x y : R, x < y -> forall z, x < z \/ z < y.

Class IsDecidable (R : Relation) := 
 isdecidable : forall x y : R, (rrel x y)+(~rrel x y).

Class IsStrictOrder (R : LtRelation) := BuildIsStrictPoset {
strictposet_irrefl :> IsIrreflexive R;
strictposet_trans :> IsTransitive R
}.


Class IsUpper (r : LeqRelation) (P : r -> Type) (m : r) := 
isupper : forall x, P x -> x <= m.
Class IsLower (r : LeqRelation) (P : r -> Type) (m : r) := 
islower : forall x, P x -> m <= x.

Class IsMaximum (r : LeqRelation) P (m : r) := BuildIsMaximum {
maximum_upper :> IsUpper r P m;
maximum_verifies : P m
}.

Class IsMinimum (r : LeqRelation) P (m : r) := BuildIsMinimum {
minimum_lower :> IsLower r P m;
minimum_verifies : P m
}.

Class IsSupremum (r : LeqRelation) P (m : r) :=
 issupremum :> IsMinimum r (IsUpper r P) m.

Instance supremum_upper : forall r P m {H : IsSupremum r P m}, IsUpper r P m :=
fun _ _ _ H => @minimum_verifies _ _ _ H.

Class IsInfimum (r : LeqRelation) P (m : r) :=
 isinfimum :> IsMaximum r (IsLower r P) m.

Instance infimum_lower : forall r P m {H : IsInfimum r P m}, IsLower r P m := 
fun _ _ _ H => @maximum_verifies _ _ _ H.

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
Proof. intros. red. apply _. Defined.

Definition Infimum (r : LeqRelation) P := Maximum r (IsLower r P).
Instance infimum_is_infimum : forall r P (m : Infimum r P),
 IsInfimum r P m.
Proof. intros;red;apply _. Defined.

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

Class IsTotalOrder (r : LeqRelation) := BuildIsTotalOrder {
totalorder_is_poset :> IsPoset r;
totalorder_linear :> IsLinear r
}.

Class IsConstrTotalOrder (r : LeqRelation) := BuildIsConstrTotalOrder {
constrtotalorder_is_poset :> IsPoset r;
constrtotalorder_linear :> IsConstrLinear r
}.


(*
In classical logic we can construct a strict order from a poset (resp poset from strict order) by taking x<y iff x<=y and x<>y (resp x<=y if x<y or x=y)
In constructive logic the inequality becomes apartness and the two iffs are not equivalent (2nd is stronger from its \/)
We end up using the first one.
cf math classes for working example (src/interfaces/orders.v > FullPartialOrder)
*)

Class IsPseudoOrder (R : RR_sig) := BuildIsPseudoOrder {
pseudoorder_is_apart :> IsApartness (RR_to_R1 R);
pseudoorder_is_antisym : forall x y : R, x<y -> y<x -> Empty;
pseudoorder_is_cotrans :> IsCotransitive (RR_to_R2 R);
pseudoorder_iff : forall x y : R, x <> y <-> (x<y \/ y<x)
}.

Class IsFullPartialOrder (R : RRR_sig) := BuildIsFullPartialOrder {
fullpartial_is_apart :> IsApartness (RRR_to_R1 R);
fullpartial_is_poset :> IsPoset (RRR_to_R2 R);
fullpartial_is_trans :> IsTransitive (RRR_to_R3 R);
lt_iff_le_apart : forall x y : R, x < y <-> (x <= y /\ x <> y)
}.

Class FullPseudoOrder (R : RRR_sig) := BuildIsFullPseudoOrder {
fullpseudoorder_is_pseudo :> IsPseudoOrder (RRR_to_R1R3 R);
le_iff_not_lt_flip : forall x y : R, x <= y <-> ~ y < x
}.


Class IsMorphism {r r' : Relation} (f : r -> r')
 := ismorphism : forall x y : r, rrel x y -> rrel (f x) (f y).
Class IsReflecting {r r' : Relation} (f : r -> r')
 := isreflecting : forall x y : r, rrel (f x) (f y) -> rrel x y.
Class IsEmbedding {r r' : Relation} (f : r -> r') := BuildIsEmbedding {
embedding_is_morphism :> IsMorphism f;
embedding_is_reflecting :> IsReflecting f
}.

Class IsBinMorphism {r1 r2 r' : Relation} (f : r1 -> r2 -> r') := isbinmorphism
 : forall x x' : r1, rrel x x' -> forall y y' : r2, rrel y y'
   -> rrel (f x y) (f x' y').
Class IsBinReflecting {r1 r2 r' : Relation} (f : r1 -> r2 -> r')
 := isbinreflecting : forall x x' y y', rrel (f x y) (f x' y')
   -> minus1Trunc (rrel x x' \/ rrel y y').

End Relation.

Module OrderedMagma.
Export Magma.
Export Relation.

(* LInvariant: forall z x y, x <= y -> z x <= z y *)
Class IsLInvariant (G : LR_sig)
 := islcompat :> forall z : G, IsMorphism ((gop z):G->G).
Class IsRInvariant (G : LR_sig)
 := isrcompat :> forall z : G, IsMorphism ((fun a : G => gop a z):G->G).
Class IsInvariant (G : LR_sig) := BuildIsInvariant {
invariant_left :> IsLInvariant G;
invariant_right :> IsRInvariant G
}.

(* Compat: forall x x' y y', x <= x', y <= y' -> x + y <= x' + y' *)
Class IsCompat (G : LR_sig) := iscompat :> IsBinMorphism ((@gop G):law G).

(* LRegular a: forall x y, a x <= a y -> x <= y *)
Class IsLRegular (G : LR_sig) (a : G) :=
 islregular :> IsReflecting ((gop a):G->G).
Class IsRRegular (G : LR_sig) (a : G) :=
 isrregular :> IsReflecting ((fun b : G => gop b a):G->G).
Class IsRegular (G : LR_sig) (a : G) := BuildIsRegular {
isreg_left :> IsLRegular G a;
isreg_right :> IsRRegular G a
}.

(* BinRegular : forall x x' y y', x+y <= x'+y' -> x<=x' or y<=y' *)
Class IsBinRegular (G : LR_sig) :=
 isbinregular :> IsBinReflecting ((@gop G):law G).
(*
NB: in semirings, we expect that (a ° _) is morphism for <= forall a >= 0
and embedding for < for a > 0
*)

End OrderedMagma.

Module Ring.
Export Magma.

(*
Infix "+" := (@rplus _).
Infix "°" := (@rmult _) (at level 40).
*)

Class Ldistributes (G : prering) := left_distributes : 
forall a b c : G, a ° (b+c) = (a°b) + (a°c).
Class Rdistributes (G : prering) := right_distributes : 
forall a b c : G, (b+c) ° a = (b°a) + (c°a).
Class Distributes (G : prering) : Type := BuildDistributes {
distrib_left :> Ldistributes G;
distrib_right :> Rdistributes G
}.

Class IsSemiring (G : prering) := BuildIsSemiring {
semiring_add :> IsCMonoid (prering_plus G);
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
BuildCMonoid (prering_plus G) _.

Canonical Structure semiring_mult_monoid (G : semiring) : monoid :=
BuildMonoid (prering_mult G) _.

Definition Zero {G : semiring} : Identity (prering_plus G) :=
 @gid (semiring_add_cmonoid G).
Definition ZeroV {G : semiring} : prering_plus G := Zero.

Definition Zero' {G : prering} {Hg : IsSemiring G} : Identity (prering_plus G)
 := Zero.
Definition ZeroV' {G : prering} {Hg : IsSemiring G} : prering_plus G := Zero.

Definition One {G : semiring} : Identity (prering_mult G) :=
 @gid (semiring_mult_monoid G).
Definition OneV {G : semiring} : prering_mult G := One.

Definition One' {G : prering} {Hg : IsSemiring G} : Identity (prering_mult G)
 := One.
Definition OneV' {G : prering} {Hg : IsSemiring G} : prering_mult G := One.

Class IsRing (G : prering) := BuildIsRing {
ring_is_semir :> IsSemiring G;
r_opp : forall x : G, @Inverse (prering_plus G) x
}.

Record ring := BuildRing {
ring_prering :> prering;
ring_is_ring :> IsRing ring_prering
}.

Canonical Structure is_ring_ring {G : prering} {Hr : IsRing G}
 : ring := BuildRing G Hr.

Existing Instance ring_is_ring.

Instance ring_is_group : forall (G : prering) {Hr : IsRing G},
 IsGroup (prering_plus G) := fun G Hr => BuildIsGroup (prering_plus G) _ r_opp.

Canonical Structure ring_group : ring -> group
 := fun G => BuildGroup _ (@ring_is_group G _).

Canonical Structure ring_semiring : ring -> semiring := 
fun G => BuildSemiring G _.

Coercion ring_semiring : ring >-> semiring.

Definition ropp {G : ring} : forall x : G, @Inverse (prering_plus G) x
 := @gopp (ring_group G).

Definition ropp' {G : prering} {Hg : IsRing G} := @ropp (@is_ring_ring G _).

Instance ropp_correct : forall (G : ring) x,
 @IsInverse (ring_group G) x (@ropp G x) := @ropp.

Definition roppV {G : ring} : G -> G := fun x => @inverse_val _ _ (ropp x).
Definition roppV' {G : prering} {Hg : IsRing G} : G -> G := roppV.

Class IsIntegralDomain (G : prering) := BuildIsIntegralDomain {
integral_ring :> IsRing G;
integral_pr :> forall a : G, ~ a = ZeroV' -> forall b : G, ~ b = ZeroV' ->
   ~ a°b = ZeroV';
intdom_neq :> ~ (@paths G OneV' ZeroV')
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
Export Ring Relation OrderedMagma.

Class IsIdempotent (G : magma) := isidempotent :> forall x : G, gop x x = x.

Class IsLatticeMag (G : magma) := BuildIsLatticeMag {
lattice_mag_sg :> IsSemigroup G;
lattice_mag_idem :> IsIdempotent G
}.

Class IsLatticeMeetR (G : LR_sig) :=
 islatticemeet : forall x y : G, rrel x y <-> gop x y = x.
Class IsLatticeJoinR (G : LR_sig) :=
 islatticejoin : forall x y : G, rrel x y <-> gop y x = y.

Class IsMeetSemiLattice (G : LR_sig) := BuildIsMeetSemiLattice {
semilattice_meet_mag :> IsLatticeMag G;
semilattice_meet_rel :> IsLatticeMeetR G
}.

Class IsJoinSemiLattice (G : LR_sig) := BuildIsJoinSemiLattice {
semilattice_join_mag :> IsLatticeMag G;
semilattice_join_rel :> IsLatticeJoinR G
}.

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

End Lattice.

Module Field.
Export Ring.
Export Relation.
Export OrderedMagma.

Notation "'prefield'" := LLR_sig : field_scope.
Notation "'prefield_prering'" := LLR_to_LL : field_scope.

Notation "'prefield_add'" := LLR_to_L1R : field_scope.
Notation "'prefield_mult'" := LLR_to_L2R : field_scope.

Notation "'prefield_Relation'" := LLR_to_R : field_scope.

Open Scope field_scope.

Class IsDecField (F : prering) := BuildIsDecField {
decfield_is_ring :> IsRing F;
decfield_neq : ~ ((@OneV' F _):F) = ZeroV';
dec_inv : F -> F;
dec_inv0 : dec_inv ZeroV' = ZeroV';
dec_inv_ok : forall x : F, ~ x = ZeroV' ->
             @IsInverse (prering_mult F) x (dec_inv x)
}.

Record decfield := BuildDecField {
decfield_prering :> prering;
decfield_is_decfield :> IsDecField decfield_prering
}.

Existing Instance decfield_is_decfield.
Canonical Structure is_decfield_decfield (F : prering) {Hf : IsDecField F}
 := BuildDecField F Hf.

Canonical Structure decfield_ring : decfield -> ring
 := fun F => BuildRing F _.
Coercion decfield_ring : decfield >-> ring.

Definition decInv {F : decfield} : F -> F := dec_inv.
Definition decInv' {F : prering} {Hf : IsDecField F} : F -> F := decInv.

Lemma decInv_0 : forall F : decfield, decInv (@ZeroV F) = ZeroV.
Proof.
intros. apply dec_inv0.
Defined.

Instance decInv_inverse : forall F : decfield, forall x : F, ~ x = ZeroV -> 
  @IsInverse (prering_mult F) x (decInv x).
Proof.
intros F. apply dec_inv_ok.
Defined.


Class IsField (F : prefield) := BuildIsField {
field_is_apart :> IsApartness (prefield_Relation F);
field_is_ring :> IsRing F;
field_add :> IsBinRegular (prefield_add F);
field_mult :> IsBinRegular (prefield_mult F);
field_neq : ((@OneV' F _):F) <> ZeroV';
f_inv : forall x : F, x <> ZeroV' -> @Inverse (prering_mult F) x;
field_inv_back : forall x : F, @Inverse (prering_mult F) x -> x <> ZeroV'
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

Module OrderedRing.
Export Ring Relation OrderedMagma.

Class IsPosPreserving (G : LR_sig)
 := ispospreserving : forall zero : Identity G, 
      forall x y : G, identity_val zero <= x -> identity_val zero <= y 
           -> identity_val zero <= x°y.

Class IsSemiringOrder (G : LLR_sig) := BuildIsSemiringOrder {
srorder_po :> IsPoset G;
srorder_partial_minus : forall x y : G, x <= y -> exists z, y = x + z;
srorder_plus :> forall z : G, IsEmbedding (plus z);
nonneg_mult_compat :> IsPosPreserving (LLR_to_L2R G)
}.

Class IsStrictSemiringOrder (G : LLRR_sig) := BuildIsStrictSemiringOrder {
strict_srorder_so :> IsStrictOrder (RR_to_R2 G);
strict_srorder_partial_minus : forall x y : G, x < y -> exists z, y = x + z;
strict_srorder_plus :> forall z : G,
       @IsEmbedding (RR_to_R2 G) (RR_to_R2 G) (plus z);
pos_mult_compat :> IsPosPreserving (LLRR_to_L2R2 G)
}.

Class IsPseudoSemiringOrder (G : LLRR_sig) := BuildIsPseudoSemiringOrder {
pseudo_srorder_strict :> IsPseudoOrder G;
pseudo_srorder_partial_minus : forall x y : G, ~y < x -> exists z, y = x + z;
pseudo_srorder_plus :> forall z : G,
        @IsEmbedding (RR_to_R2 G) (RR_to_R2 G) (plus z);
pseudo_srorder_mult_ext :> IsBinRegular (LLRR_to_L2R1 G);
pseudo_srorder_pos_mult_compat :> IsPosPreserving (LLRR_to_L2R2 G)
}.

Class FullPseudoSemiringOrder (G : LLRRR_sig) :=
  BuildIsFullPseudoSemiringOrder {
full_pseudo_srorder_pso :> IsPseudoSemiringOrder (LLRRR_to_LLR1R3 G);
full_pseudo_srorder_le_iff_not_lt_flip : forall x y : G, x <= y <-> ~y < x
}.



End OrderedRing.




