
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

Module Signatures.

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

(*********** PRERING ******************)

Record preringClass (T : Type) := BuildPreringC {
prering_plusV : law T;
prering_multV : law T
}.

Record prering := BuildPrering {
rigcarr :> Type;
rigC : preringClass rigcarr
}.

Definition makePrering : forall T : Type, law T -> law T -> prering
 := fun T pl ml => BuildPrering T (BuildPreringC _ pl ml).

(* canonical structures? *)
Canonical Structure prering_plus (G : prering) : magma :=
BuildMagma G (prering_plusV _ (rigC G)).
Canonical Structure prering_mult (G : prering) : magma :=
BuildMagma G (prering_multV _ (rigC G)).

Definition rplus {G : prering} : law G := @gop (prering_plus G).
Definition rmult {G : prering} : law G := @gop (prering_mult G).

(*
NB: never access the laws in a prering directly if you can at all avoid it.
Instead use prering_plus or rplus (depending on which you need)
That way results on magmas are immediately usable

Same thing for other compound structures eg ordered magmas, etc
*)


(****************************************
************* RELATION ******************
****************************************)

(*
Definition relation T := T -> T -> Type.
*)

Record Relation := BuildRelation {
relcarr :> Type;
rel_r : relation relcarr
}.

Definition rrel {R : Relation} : relation R :=
match R with | BuildRelation _ r => r end.

Arguments rrel {_} _ _ : simpl never.

(*
Axiom blob : forall R : Relation, forall x y : R, rrel x y.

Lemma blob_use : forall T : Type, forall x y : T, x=y.
intros. apply (blob _ x y).
Abort.
*)

(*
Generic naming scheme when there isn't a default meaning:
X is a word made of R and L, R standing for relation and L for law
relations come after laws
  eg for prering, X = LL, for ordered ring, X = LLR
then we have X_Class (T : Type) a record with projections
  projection names are X_c_xn where x is L or R and n is the index of the law/rel starting from 1
  n is omitted if only one law/rel in signature
  eg for ordered ring we have LLR_Vlaw1, LLR_Vlaw2 and LLR_Vrel
  (should be used as little as possible)
then X_sig := BuildX_sig { X_carr :> Type; X_class : X_Class X_carr }

finally we define (?name? like prering_plus and prering_mult)
X_to_Y where Y selects letters from X. eg LLR_to_L1R, LLR_to_L2R, LLR_to_R, etc
(only when deemed useful)
and functions X_xn (only useful when multiple laws (relations), otherwise canonical structures pick it up using gop/rrel)
*)

(******************* 2 Relations ***************)

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

Canonical Structure RR_to_R1 (R : RR_sig) : Relation :=
BuildRelation R (RR_c_R1 _ (RR_class R)).
Canonical Structure RR_to_R2 (R : RR_sig) : Relation :=
BuildRelation R (RR_c_R2 _ (RR_class R)).

Definition RR_R1 {R : RR_sig} : relation R := @rrel (RR_to_R1 R).
Definition RR_R2 {R : RR_sig} : relation R := @rrel (RR_to_R2 R).

(***************** LR ***********************)

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

(* example of why we don't need LR_L or LR_R *)
(*
Check (forall G : LR_sig, forall x y z : G, rrel (gop y z) x).
*)

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
BuildPrering G (BuildPreringC _ (LLR_c_L1 _ (LLR_class G))
                                (LLR_c_L2 _ (LLR_class G))).
Coercion LLR_to_LL : LLR_sig >-> prering.

Canonical Structure LLR_to_R (G : LLR_sig) : Relation :=
BuildRelation G (LLR_c_R _ (LLR_class G)).
Coercion LLR_to_R : LLR_sig >-> Relation.

(*not coercions: would be ambiguous*)
Canonical Structure LLR_to_L1R (G : LLR_sig) : LR_sig :=
BuildLR_sig G (BuildLR_Class _ (LLR_c_L1 _ (LLR_class G))
                               (LLR_c_R _ (LLR_class G))).
Canonical Structure LLR_to_L2R (G : LLR_sig) : LR_sig :=
BuildLR_sig G (BuildLR_Class _ (LLR_c_L2 _ (LLR_class G))
                               (LLR_c_R _ (LLR_class G))).

(*
Lemma blob : forall G : LLR_sig, forall a b c d : G,
 rrel ((rplus a b):G) (rmult c d).
Proof.
simpl. (*gets rid of the :G*)
Abort.
*)

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
BuildPrering G (BuildPreringC _ (LLRRR_L1 _ (LLRRR_class G))
                                 (LLRRR_L2 _ (LLRRR_class G))).
Coercion LLRRR_to_LL : LLRRR_sig >-> prering.

Canonical Structure LLRRR_to_LLR1 (G : LLRRR_sig) : LLR_sig :=
BuildLLR_sig G (BuildLLR_Class _ (LLRRR_L1 _ (LLRRR_class G))
                                 (LLRRR_L2 _ (LLRRR_class G))
                                 (LLRRR_R1 _ (LLRRR_class G))).
Canonical Structure LLRRR_to_LLR2 (G : LLRRR_sig) : LLR_sig :=
BuildLLR_sig G (BuildLLR_Class _ (LLRRR_L1 _ (LLRRR_class G))
                                 (LLRRR_L2 _ (LLRRR_class G))
                                 (LLRRR_R2 _ (LLRRR_class G))).
Canonical Structure LLRRR_to_LLR3 (G : LLRRR_sig) : LLR_sig :=
BuildLLR_sig G (BuildLLR_Class _ (LLRRR_L1 _ (LLRRR_class G))
                                 (LLRRR_L2 _ (LLRRR_class G))
                                 (LLRRR_R3 _ (LLRRR_class G))).

Canonical Structure LLRRR_to_R1R2 (G : LLRRR_sig) : RR_sig :=
BuildRR_sig G (BuildRR_Class _   (LLRRR_R1 _ (LLRRR_class G))
                                 (LLRRR_R2 _ (LLRRR_class G))).

(*
Lemma test : forall G : LLRRR_sig, forall a b : G, rplus a b = rmult a b.
Abort.
*)

End Signatures.



Module AlgebraNotation.
Export Signatures.

Class PlusOp (A : Type) := plus : law A.

Infix "+" := plus.

Ltac foldPlusOp op := change op with (@plus _ op).

Definition AdditiveMagma := magma.

Instance AddMag_PlusOp : forall G : AdditiveMagma, PlusOp G := @gop.

Ltac foldAddMag G := change (@gop G) with (@plus _ (AddMag_PlusOp G)).


Class MultOp (A : Type) := mult : law A.

Infix "°" := mult (at level 40).

Ltac foldMultOp op := change op with (@mult _ op).

Definition MultiplicativeMagma := magma.

Instance MultMag_MultOp : forall G : MultiplicativeMagma, MultOp G
 := @gop.

Ltac foldMultMag G := change (@gop G) with (@mult _ (MultMag_MultOp G)).

Instance Prering_PlusOp : forall G : prering, PlusOp G := @rplus.
Instance Prering_MultOp : forall G : prering, MultOp G := @rmult.

Ltac foldAddPrering G := change (@rplus G) with (@plus _ (Prering_PlusOp G)).
Ltac foldMultPrering G := change (@rmult G) with (@mult _ (Prering_MultOp G)).
Ltac foldPreringOps G := foldAddPrering G; foldMultPrering G.

(*
Lemma blob : forall G : prering, forall x y z: G, x ° (y+z) = (x°y) + x°z.
Lemma blob' : forall G : LLR_sig, forall x y : G, x ° y = rmult x y.
intros. foldPreringOps G.
Lemma blob'' : forall G : prering, forall x y : G, rplus x y = rmult y x.
intros. foldPreringOps G.
*)


Class LeqOp (A : Type) := leq : relation A.

Infix "<=" := leq.

Ltac foldLeqOp op := change op with (@leq _ op).

Definition LeqRelation := Relation.

Instance LeqRel_LeqOp : forall R : LeqRelation, LeqOp R := @rrel.

Ltac foldLeqRel R := change (@rrel R) with (@leq _ (LeqRel_LeqOp R)).


Class LtOp (A : Type) := lt : relation A.

Infix "<" := lt.

Ltac foldLtOp op := change op with (@lt _ op).

Definition LtRelation := Relation.

Instance LtRel_LtOp : forall R : LtRelation, LtOp R := @rrel.

Ltac foldLtRel R := change (@rrel R) with (@lt _ (LtRel_LtOp R)).


Definition OrderPair_sig := RR_sig.

Instance Order2_LeqOp : forall R : OrderPair_sig, LeqOp R := @RR_R1.
Instance Order2_LtOp : forall R : OrderPair_sig, LtOp R := @RR_R2.

Ltac foldOrderLeq R := change (@RR_R1 R) with (@leq _ (Order2_LeqOp R)).
Ltac foldOrderLt R := change (@RR_R2 R) with (@lt _ (Order2_LtOp R)).
Ltac foldOrder2 R := foldOrderLeq R; foldOrderLt R.


Class ApartOp (A : Type) := apart : relation A.

Infix "<>" := apart.

Ltac foldApartOp op := change op with (@apart _ op).

Definition ApartRelation := Relation.

Instance ApartRel_ApartOp : forall R : ApartRelation, ApartOp R := @rrel.

Ltac foldApartRel R := change (@rrel R) with (@apart _ (ApartRel_ApartOp R)).


Definition prefield := LLR_sig.

Instance Prefield_ApartOp : forall F : prefield, ApartOp F := @rrel.

Ltac foldPrefieldApart F := change (@rrel F) with
   (@apart _ (Prefield_ApartOp F)).

(*
Lemma blob : forall F : prefield, forall x y : F, x+y <> x°y.
*)

End AlgebraNotation.





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

Module Related.
Export Signatures.
Import AlgebraNotation.

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

Class IsStrictLinear (R : Relation) := 
 isstrictlinear : forall x y : R, rrel x y -> forall z,
   minus1Trunc (rrel x z \/ rrel z y).

Class IsCotransitive (R : Relation) := 
 iscotrans :> IsStrictLinear R.

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

Class IsConstrStrictLinear (R : Relation) := isconstrstrictlinear
 : forall x y : R, rrel x y -> forall z, rrel x z \/ rrel z y.

Class IsDecidable (R : Relation) := 
 isdecidable : forall x y : R, (rrel x y)+(~rrel x y).

Class IsStrictPoset (R : LtRelation) := BuildIsStrictPoset {
strictposet_irrefl :> IsIrreflexive R;
strictposet_trans :> IsTransitive R
}.

Class IsTight (r : RR_sig) :=
 istight : forall x y : r, RR_R1 x y <-> ~ RR_R2 y x.

Class IsPoset2 (r : OrderPair_sig) := BuildIsPoset2 {
poset2_1 :> IsPoset (RR_to_R1 r);
poset2_2 :> IsStrictPoset (RR_to_R2 r);
poset2_tight :> IsTight r
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

End Related.

Module OrderedMagma.
Export Magma.
Export Related.

Class IsLInvariant (G : LR_sig)
 := islcompat :> forall z : G, IsMorphism ((gop z):G->G).
Class IsRInvariant (G : LR_sig)
 := isrcompat :> forall z : G, IsMorphism ((fun a : G => gop a z):G->G).
Class IsInvariant (G : LR_sig) := BuildIsInvariant {
invariant_left :> IsLInvariant G;
invariant_right :> IsRInvariant G
}.

Class IsCompat (G : LR_sig) := iscompat :> IsBinMorphism ((@gop G):law G).

Class IsLRegular (G : LR_sig) (a : G) :=
 islregular :> IsReflecting ((gop a):G->G).
Class IsRRegular (G : LR_sig) (a : G) :=
 isrregular :> IsReflecting ((fun b : G => gop b a):G->G).
Class IsRegular (G : LR_sig) (a : G) := BuildIsRegular {
isreg_left :> IsLRegular G a;
isreg_right :> IsRRegular G a
}.

Class IsBinRegular (G : LR_sig) :=
 isbinregular :> IsBinReflecting ((@gop G):law G).
(*
NB: in semirings, we expect that (a ° _) is morphism for <= forall a >= 0
and embedding for < for a > 0
*)

End OrderedMagma.

Module Ring.
Export Magma AlgebraNotation.

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
ring_mag2 :> prering;
ring_is_ring :> IsRing ring_mag2
}.

Canonical Structure is_ring_ring {G : prering} {Hr : IsRing G}
 : ring := BuildRing G Hr.

Existing Instance ring_is_ring.

Instance ring_is_group : forall (G : prering) {Hr : IsRing G},
 IsGroup (prering_plus G) := fun G Hr => BuildIsGroup _ _ r_opp.

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

Notation "x - y" := (rplus x (roppV y)).
Notation "- x" := (roppV x).

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
Export Ring Related OrderedMagma.

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
Export Related.
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

