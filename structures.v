
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

Record LL_Class T := BuildLL_Class {
LL_L1 : law T;
LL_L2 : law T
}.

Class Prering (T : Type) := prering : LL_Class T.
Instance prering_plus : forall {T}, Prering T -> Plus T := LL_L1.
Instance prering_mult : forall {T}, Prering T -> Mult T := LL_L2.
Coercion prering_plus : Prering >-> Plus.
Coercion prering_mult : Prering >-> Mult.

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
Coercion apartlt_apart : ApartLt >-> Apart.
Coercion apartlt_lt : ApartLt >-> Lt.

Notation "(<> <)" := apartlt (only parsing).

Class LeqLt T := leqlt : RR_Class T.

Notation "(<= <)" := leqlt (only parsing).

Instance leqlt_leq : forall {T}, LeqLt T -> Leq T := RR_R1.
Instance leqlt_lt  : forall {T}, LeqLt T -> Lt T := RR_R2.
Coercion leqlt_leq : LeqLt >-> Leq.
Coercion leqlt_lt : LeqLt >-> Lt.

Class ApartLeq T := apartleq : RR_Class T.

Notation "(<> <=)" := apartleq.

Instance apartleq_apart : forall {T}, ApartLeq T -> Apart T := RR_R1.
Instance apartleq_leq : forall {T}, ApartLeq T -> Leq T := RR_R2.
Coercion apartleq_apart : ApartLeq >-> Apart.
Coercion apartleq_leq : ApartLeq >-> Leq.

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

Notation "(<> <= <)" := fullrelation (only parsing).

Instance fullrel_apartlt {T} (R : FullRelation T) : ApartLt T
 := BuildRR_Class T (RRR_R1 T R) (RRR_R3 T R).
Coercion fullrel_apartlt : FullRelation >-> ApartLt.

Instance fullrel_apart {T} (R : FullRelation T) : Apart T := _.
Instance fullrel_lt {T} (R : FullRelation T) : Lt T := _.
Instance fullrel_leq {T} (R : FullRelation T) : Leq T := RRR_R2 T R.
Coercion fullrel_leq : FullRelation >-> Leq.

(***************** LR ***********************)

Record LR_Class (T : Type) := BuildLR_Class {
LR_L : law T;
LR_R : relation T
}.

Class OpRel T := oprel : LR_Class T.

Notation "(& ~>)" := oprel (only parsing).

Instance oprel_op : forall {T}, OpRel T -> Gop T := LR_L.
Instance oprel_rel : forall {T}, OpRel T -> Rel T := LR_R.
Coercion oprel_op : OpRel >-> Gop.
Coercion oprel_rel : OpRel >-> Rel.


Class PlusRel T := plusrel :> OpRel T.

Notation "(+ ~>)" := plusrel (only parsing).

Instance plusrel_plus : forall {T}, PlusRel T -> Plus T := @oprel_op.
Coercion plusrel_plus : PlusRel >-> Plus.
Coercion plusrel : PlusRel >-> OpRel.

Class MultRel T := multrel :> OpRel T.

Notation "(° ~>)" := multrel (only parsing).

Instance multrel_mult : forall {T}, MultRel T -> Mult T := @oprel_op.
Coercion multrel_mult : MultRel >-> Mult.
Coercion multrel : MultRel >-> OpRel.

Class OpApart T := opapart :> OpRel T.

Notation "(& <>)" := opapart (only parsing).

Instance opapart_apart : forall {T}, OpApart T -> Apart T := @oprel_rel.
Coercion opapart_apart : OpApart >-> Apart.
Coercion opapart : OpApart >-> OpRel.

Class OpLeq T := opleq :> OpRel T.

Notation "(& <=)" := opleq (only parsing).

Instance opleq_leq : forall {T}, OpLeq T -> Leq T := @oprel_rel.
Coercion opleq_leq : OpLeq >-> Leq.
Coercion opleq : OpLeq >-> OpRel.

Class OpLt T := oplt :> OpRel T.

Notation "(& <)" := oplt (only parsing).

Instance oplt_lt : forall {T}, OpLt T -> Lt T := @oprel_rel.
Coercion oplt_lt : OpLt >-> Lt.
Coercion oplt : OpLt >-> OpRel.


Class PlusApart T := plusapart :> PlusRel T.

Notation "(+ <>)" := plusapart (only parsing).

Instance plusapart_opapart {T} : PlusApart T -> OpApart T := idmap.
Coercion plusapart_opapart : PlusApart >-> OpApart.
Coercion plusapart : PlusApart >-> PlusRel.

Class MultApart T := multapart : MultRel T.

Notation "(° <>)" := multapart (only parsing).

Instance multapart_opapart {T} : MultApart T -> OpApart T := idmap.
Coercion multapart_opapart : MultApart >-> OpApart.
Coercion multapart : MultApart >-> MultRel.


Class PlusLeq T := plusleq :> PlusRel T.

Notation "(+ <=)" := plusleq (only parsing).

Instance plusleq_opleq {T} : PlusLeq T -> OpLeq T := idmap.
Coercion plusleq_opleq : PlusLeq >-> OpLeq.
Coercion plusleq : PlusLeq >-> PlusRel.

Class MultLeq T := multleq : MultRel T.

Notation "(° <=)" := multleq (only parsing).

Instance multleq_opleq {T} : MultLeq T -> OpLeq T := idmap.
Coercion multleq_opleq : MultLeq >-> OpLeq.
Coercion multleq : MultLeq >-> MultRel.


Class PlusLt T := pluslt :> PlusRel T.

Notation "(+ <)" := pluslt (only parsing).

Instance pluslt_oplt {T} : PlusLt T -> OpLt T := idmap.
Coercion pluslt_oplt : PlusLt >-> OpLt.
Coercion pluslt : PlusLt >-> PlusRel.

Class MultLt T := multlt : MultRel T.

Notation "(° <)" := multlt (only parsing).

Instance multlt_oplt {T} : MultLt T -> OpLt T := idmap.
Coercion multlt_oplt : MultLt >-> OpLt.
Coercion multlt : MultLt >-> MultRel.

(******************* LLR ***********************)

Record LLR_Class (T : Type) := BuildLLR_Class {
LLR_L1 : law T;
LLR_L2 : law T;
LLR_R : relation T
}.

Class PreringRel T := preringrel : LLR_Class T.
Notation "(+ ° ~>)" := preringrel (only parsing).

Class Prefield T := prefield :> PreringRel T.
Coercion prefield : Prefield >-> PreringRel.
Notation "(+ ° <>)" := prefield (only parsing).

Instance preringrel_prering {T} (G : PreringRel T) : Prering T :=
BuildLL_Class _ (LLR_L1 _ G) (LLR_L2 _ G).
Coercion preringrel_prering : PreringRel >-> Prering.

Instance preringrel_rel : forall {T}, PreringRel T -> Rel T := LLR_R.
Coercion preringrel_rel : PreringRel >-> Rel.

Instance prefieldApart : forall {T}, Prefield T -> Apart T := @preringrel_rel.
Coercion prefieldApart : Prefield >-> Apart.

Instance prefield_plusapart : forall {T}, Prefield T -> PlusApart T
 := fun T L => BuildLR_Class T (+) (<>).
Instance prefield_multapart : forall {T}, Prefield T -> MultApart T
 := fun T L => BuildLR_Class T (°) (<>).
Coercion prefield_plusapart : Prefield >-> PlusApart.
Coercion prefield_multapart : Prefield >-> MultApart.


Class PreringLeq T := preringleq :> PreringRel T.
Coercion preringleq : PreringLeq >-> PreringRel.
Notation "(+ ° <=)" := preringleq (only parsing).

Instance preringleq_leq : forall {T}, PreringLeq T -> Leq T := @preringrel_rel.
Coercion preringleq_leq : PreringLeq >-> Leq.

Instance preringleq_plusleq : forall {T}, PreringLeq T -> PlusLeq T
 := fun T L => BuildLR_Class T (+) (<=).
Instance preringleq_multleq : forall {T}, PreringLeq T -> MultLeq T
 := fun T L => BuildLR_Class T (°) (<=).
Coercion preringleq_plusleq : PreringLeq >-> PlusLeq.
Coercion preringleq_multleq : PreringLeq >-> MultLeq.


Class PreringLt T := preringlt :> PreringRel T.
Coercion preringlt : PreringLt >-> PreringRel.
Notation "(+ ° <)" := preringlt (only parsing).

Instance preringlt_lt : forall {T}, PreringLt T -> Lt T := @preringrel_rel.
Coercion preringlt_lt : PreringLt >-> Lt.

Instance preringlt_pluslt : forall {T}, PreringLt T -> PlusLt T
 := fun T L => BuildLR_Class T (+) (<).
Instance preringlt_multlt : forall {T}, PreringLt T -> MultLt T
 := fun T L => BuildLR_Class T (°) (<).
Coercion preringlt_pluslt : PreringLt >-> PlusLt.
Coercion preringlt_multlt : PreringLt >-> MultLt.

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
Notation "(+ ° <> <)" := preringstrict (only parsing).

Instance preringstrict_prefield : forall {T}, PreringStrict T -> Prefield T
 := fun T G => BuildLLR_Class T (LLRR_L1 T G) (LLRR_L2 T G) (LLRR_R1 T G).
Coercion preringstrict_prefield : PreringStrict >-> Prefield.

Instance preringstrict_preringlt : forall {T}, PreringStrict T -> PreringLt T
 := fun T G => BuildLLR_Class T (LLRR_L1 T G) (LLRR_L2 T G) (LLRR_R2 T G).
Coercion preringstrict_preringlt : PreringStrict >-> PreringLt.

Instance preringstrict_strict :  forall {T}, PreringStrict T -> ApartLt T
 := fun T G => BuildRR_Class T (LLRR_R1 T G) (LLRR_R2 T G).
Coercion preringstrict_strict : PreringStrict >-> ApartLt.

(* no LRR_Class ? *)

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
Notation "(+ ° <> <= <)" := preringfull (only parsing).

Instance preringfull_fullrel : forall {T}, PreringFull T -> FullRelation T
 := fun T G => BuildRRR_Class T (LLRRR_R1 T G) (LLRRR_R2 T G) (LLRRR_R3 T G).
Coercion preringfull_fullrel : PreringFull >-> FullRelation.

Instance preringfull_strict : forall {T}, PreringFull T -> PreringStrict T
 := fun T G => BuildLLRR_Class T (LLRRR_L1 T G) (LLRRR_L2 T G)
                                 (LLRRR_R1 T G) (LLRRR_R3 T G).
Coercion preringfull_strict : PreringFull >-> PreringStrict.

Instance preringfull_preringleq : forall {T}, PreringFull T -> PreringLeq T
 := fun T G => BuildLLR_Class T (LLRRR_L1 T G) (LLRRR_L2 T G) (LLRRR_R2 T G).
Coercion preringfull_preringleq : PreringFull >-> PreringLeq.

(* no LRRR_Class ? *)

End Signatures.


Module Magma.
Export Signatures.

Section Magma.

Context {T : Type}. Variable G : Gop T.

Class Associative := associative : 
forall x y z : T, gop x (gop y z) = gop (gop x y) z.

Class Commutative := commutative : 
forall x y : T, gop x y = gop y x.

Class IsSemigroup := BuildIsSemigroup {
sg_assoc :> Associative;
sg_comm :> Commutative
}.

Coercion sg_assoc : IsSemigroup >-> Associative.
Coercion sg_comm : IsSemigroup >-> Commutative.

Section Identity.

Variable e : T.

Class Left_id := left_id : 
forall x : T, gop e x = x.
Class Right_id := right_id : 
forall x : T, gop x e = x.

Class IsId := BuildIsId {
id_is_left :> Left_id;
id_is_right :> Right_id
}.

Coercion id_is_left : IsId >-> Left_id.
Coercion id_is_right : IsId >-> Right_id.

End Identity.

Class Identity := BuildIdentity {
g_id : T;
g_idP :> IsId g_id
}.
Existing Instance g_idP.
Coercion g_id : Identity >-> T. (*NB: only for this section *)

Class IsMonoid := BuildIsMonoid {
monoid_is_sg :> IsSemigroup ;
monoid_id :> Identity
}.

Coercion monoid_is_sg : IsMonoid >-> IsSemigroup.

Definition gid {Hg : IsMonoid} : Identity := _.
Definition gidV {Hg : IsMonoid} : T := @g_id gid.
Global Instance gidP {Hg : IsMonoid} : IsId gidV := _.

Section Cancel.

Variable a : T.

Class Lcancel : Type := left_cancel : 
forall b c : T, gop a b = gop a c -> b = c.
Class Rcancel : Type := right_cancel : 
forall b c : T, gop b a = gop c a -> b = c.
Class Cancel : Type := BuildCancel {
Left_cancel :> Lcancel;
Right_cancel :> Rcancel
}.

Coercion Left_cancel : Cancel >-> Lcancel.
Coercion Right_cancel : Cancel >-> Rcancel.

End Cancel.

Class IsCMonoid := BuildIsCMonoid {
cmonoid_is_monoid :> IsMonoid;
cmonoid_cancel :> forall a : T, Cancel a
}.

Coercion cmonoid_is_monoid : IsCMonoid >-> IsMonoid.
Coercion cmonoid_cancel : IsCMonoid >-> Funclass.

(*
Usually we would require G to be a monoid, with the left_inverse property being gop x y = gid
By doing things this way, we gain
- less complicated coercion paths if G comes from say a field or something
- more ease of use:
  if we need gop x y = gid we use unicity of identity elements, then since IsId is a class instance resolution suffices
  if we need gop (gop x y) z = z we directly apply the IsInverse hypothesis
*)
Section Inverse.

Variables (x y : T).

Class Linverse := left_inverse :> IsId (gop x y).
Class Rinverse := right_inverse :> IsId (gop y x).

Class IsInverse := BuildIsInverse {
inverse_left :> Linverse;
inverse_right :> Rinverse
}.

Coercion inverse_left : IsInverse >-> Linverse.
Coercion inverse_right : IsInverse >-> Rinverse.

End Inverse.

Record Inverse x := BuildInverse {
inverse_val : T;
inverse_pr : IsInverse x inverse_val
}.
Global Existing Instance inverse_pr.

Coercion inverse_val : Inverse >-> T.

Class IsGroup := BuildIsGroup {
group_is_cmonoid :> IsCMonoid;
gopp : forall x, Inverse x
}.

Coercion group_is_cmonoid : IsGroup >-> IsCMonoid.

Definition goppV : forall {Hg : IsGroup}, T -> T
 := fun Hg x => inverse_val _ (gopp x).
Global Instance goppP : forall {Hg : IsGroup}, forall x:T,
 IsInverse x (goppV x) := _.

Class IsMorphism {T} (G : Gop T) {T'} (G' : Gop T') (f : T -> T')
 := ismorphism : forall x y, f (gop x y) = gop (f x) (f y).

End Magma.

Arguments inverse_val {_ _ _} _.

Arguments gopp {_ _ _} _.
Arguments goppV {_ _ _} _.
Arguments goppP {_ _ _} _.

Arguments gid {_ _ _}.
Arguments gidV {_ _ _}.
Arguments gidP {_ _ _}.

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

Coercion equivalence_refl  : Equivalence >-> Reflexive.
Coercion equivalence_symm  : Equivalence >-> Symmetric.
Coercion equivalence_trans : Equivalence >-> Transitive.

Class Antisymmetric {T} (R : Leq T) :=
 antisymmetric : forall x y : T, x <= y -> y <= x -> x=y.

Class StrongAntisymmetric {T : Type} (R : Lt T) :=
 strongantisymm : forall x y : T, x < y -> y < x -> Empty.

Class Irreflexive {T} (R : Rel T) := 
 irrefl : forall x : T, rrel x x -> Empty.

(*
Putting leq here means that when we unfold rrel in Transitive's definition, it unfolds to leq (as opposed to R)
This allows us to recover notations easily
*)
Class Poset {T} (R : Leq T) := BuildPoset {
order_trans :> Transitive leq;
order_refl :> Reflexive leq;
order_antisymm :> Antisymmetric R
}.

Coercion order_trans : Poset >-> Transitive.
Coercion order_refl  : Poset >-> Reflexive.
Coercion order_antisymm : Poset >-> Antisymmetric.

(*NB: do not use < here, it becomes ambiguous when used with an apartness relation*)
Class Cotransitive {T} (R : Rel T) := 
 iscotransitive : forall x y : T, rrel x y -> forall z,
   minus1Trunc (rrel x z \/ rrel z y).

Class Apartness {T} (R : Apart T) := BuildApartness {
apart_irrefl :> Irreflexive apart;
apart_symm :> Symmetric apart;
apart_cotrans :> Cotransitive apart;
apart_tight : forall x y : T, ~ x <> y -> x=y
}.

Coercion apart_irrefl : Apartness >-> Irreflexive.
Coercion apart_symm : Apartness >-> Symmetric.
Coercion apart_cotrans : Apartness >-> Cotransitive.

Class TrivialApart {T} (R : Apart T) := trivialapart
 : forall x y : T, x<>y <-> x!=y.

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
strictorder_irrefl :> Irreflexive lt;
strictorder_trans :> Transitive lt
}.

Coercion strictorder_irrefl : StrictOrder >-> Irreflexive.
Coercion strictorder_trans : StrictOrder >-> Transitive.

Class IsUpper {T} (R : Leq T) (P : T -> Type) (m : T) := 
isupper : forall x, P x -> x <= m.
Class IsLower {T} (R : Leq T) (P : T -> Type) (m : T) := 
islower : forall x, P x -> m <= x.

Class IsMaximum {T} (R : Leq T) P (m : T) := BuildIsMaximum {
maximum_upper :> IsUpper R P m;
maximum_verifies : P m
}.
Coercion maximum_upper : IsMaximum >-> IsUpper.

Class IsMinimum {T} (R : Leq T) P (m : T) := BuildIsMinimum {
minimum_lower :> IsLower R P m;
minimum_verifies : P m
}.
Coercion minimum_lower : IsMinimum >-> IsLower.

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
Coercion totalorder_poset : TotalOrder >-> Poset.
Coercion totalorder_linear : TotalOrder >-> Linear.

Class ConstrTotalOrder {T} (R : Leq T) := BuildConstrTotalOrder {
constrtotalorder_poset :> Poset R;
constrtotalorder_linear :> ConstrLinear R
}.
Coercion constrtotalorder_poset : ConstrTotalOrder >-> Poset.
Coercion constrtotalorder_linear : ConstrTotalOrder >-> ConstrLinear.


(*
In classical logic we can construct a strict order from a poset (resp poset from strict order) by taking x<y iff x<=y and x<>y (resp x<=y if x<y or x=y)
In constructive logic the inequality becomes apartness and the two iffs are not equivalent (2nd is stronger from its \/)
We end up using the first one.
cf math classes for working example (src/interfaces/orders.v > FullPartialOrder)
*)

Class PseudoOrder {T} (R : ApartLt T) := BuildPseudoOrder {
pseudoorder_apart :> Apartness R;
pseudoorder_antisym : forall x y : T, x<y -> y<x -> Empty;
pseudoorder_cotrans :> Cotransitive lt;
apart_iff_total_lt : forall x y : T, x <> y <-> (x<y \/ y<x)
}.
Coercion pseudoorder_apart : PseudoOrder >-> Apartness.
Coercion pseudoorder_cotrans : PseudoOrder >-> Cotransitive.

Class FullPoset {T} (R : FullRelation T) := BuildFullPartialOrder {
fullpartial_apart :> Apartness R;
fullpartial_poset :> Poset R;
fullpartial_trans :> Transitive lt;
lt_iff_le_apart : forall x y : T, x < y <-> (x <= y /\ x <> y)
}.
Coercion fullpartial_apart : FullPoset >-> Apartness.
Coercion fullpartial_poset : FullPoset >-> Poset.
Coercion fullpartial_trans : FullPoset >-> Transitive.

Class FullPseudoOrder {T} (R : FullRelation T) := BuildFullPseudoOrder {
fullpseudoorder_pseudo :> PseudoOrder R;
le_iff_not_lt_flip : forall x y : T, x <= y <-> ~ y < x
}.
Coercion fullpseudoorder_pseudo : FullPseudoOrder >-> PseudoOrder.

Class IsMorphism {T} (R : Rel T) {T'} (R' : Rel T') (f : T -> T')
 := ismorphism : forall x y, rrel x y -> rrel (f x) (f y).
Class IsReflecting {T} (R : Rel T) {T'} (R' : Rel T') (f : T -> T')
 := isreflecting : forall x y, rrel (f x) (f y) -> rrel x y.
Class IsEmbedding {T} (R : Rel T) {T'} (R' : Rel T') (f : T -> T')
 := BuildIsEmbedding {
embedding_is_morphism :> IsMorphism R R' f;
embedding_is_reflecting :> IsReflecting R R' f
}.
Coercion embedding_is_morphism : IsEmbedding >-> IsMorphism.
Coercion embedding_is_reflecting : IsEmbedding >-> IsReflecting.

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
 := islinvariant :> forall z : G, IsMorphism R R (gop z).
Class IsRInvariant {G} (R : OpRel G)
 := isrinvariant :> forall z : G, IsMorphism R R (fun a : G => gop a z).
Class IsInvariant {G} (R : OpRel G) := BuildIsInvariant {
isinvariant_left :> IsLInvariant R;
isinvariant_right :> IsRInvariant R
}.
Coercion isinvariant_left : IsInvariant >-> IsLInvariant.
Coercion isinvariant_right : IsInvariant >-> IsRInvariant.

(* Compat: forall x x' y y', x <= x', y <= y' -> x + y <= x' + y' *)
Class IsCompat {G} (R : OpRel G)
 := iscompat :> IsBinMorphism R R R gop.

(* LRegular a: forall x y, a x <= a y -> x <= y *)
Class IsLRegular {G} (R : OpRel G) (a : G) :=
 islregular :> IsReflecting R R (gop a).
Class IsRRegular {G} (R : OpRel G) (a : G) :=
 isrregular :> IsReflecting R R (fun b : G => gop b a).
Class IsRegular {G} (R : OpRel G) (a : G) := BuildIsRegular {
isreg_left :> IsLRegular R a;
isreg_right :> IsRRegular R a
}.
Coercion isreg_left : IsRegular >-> IsLRegular.
Coercion isreg_right : IsRegular >-> IsRRegular.

(* BinRegular : forall x x' y y', x+y <= x'+y' -> x<=x' or y<=y' *)
Class IsBinRegular {G} (R : OpRel G) :=
 isbinregular :> IsBinReflecting R R R gop.
(*
NB: in semirings, we expect that (a ° _) is morphism for <= forall a >= 0
and embedding for < for a > 0
*)

End OrderedMagma.

Module Ring.
Export Magma.

Section Prering.

Context {G : Type}.
Variable L : Prering G.

Class Ldistributes := ldistributes : 
forall a b c : G, a ° (b+c) = (a°b) + (a°c).
Class Rdistributes := rdistributes : 
forall a b c : G, (b+c) ° a = (b°a) + (c°a).
Class Distributes := BuildDistributes {
distributes_left :> Ldistributes;
distributes_right :> Rdistributes
}.

Coercion distributes_left : Distributes >-> Ldistributes.
Coercion distributes_right : Distributes >-> Rdistributes.

Class IsSemiring := BuildIsSemiring {
semiring_plus :> IsCMonoid (+);
semiring_mult :> IsMonoid (°);
semiring_distributes :> Distributes
}.

Coercion semiring_plus : IsSemiring >-> IsCMonoid.
Coercion semiring_mult : IsSemiring >-> IsMonoid.
Coercion semiring_distributes : IsSemiring >-> Distributes.

Definition Zero {H : IsSemiring} : Identity (+) := @gid _ (+) _.
Definition ZeroV {H : IsSemiring} : G := @gidV _ (+) _.
Instance ZeroP {H : IsSemiring} : IsId (+) ZeroV := @gidP _ (+) _.

Definition One {H : IsSemiring} : Identity (°) := @gid _ (°) _.
Definition OneV {H : IsSemiring} : G := @gidV _ (°) _.
Instance OneP {H : IsSemiring} : IsId (°) OneV := @gidP _ (°) _.

Class IsRing := BuildIsRing {
ring_is_semir :> IsSemiring;
r_opp : forall x, Inverse (+) x
}.
Coercion ring_is_semir : IsRing >-> IsSemiring.

Global Instance ring_is_group : forall {Hr : IsRing},
 IsGroup (+).
Proof.
intros;apply BuildIsGroup. apply _.
apply r_opp.
Defined.

Definition ropp {Hg : IsRing}
 : forall x, Inverse (+) x := @gopp _ (+) _.
Definition roppV {Hg : IsRing} : G -> G := @goppV _ (+) _.
Instance roppP {Hg : IsRing} : forall x:G, IsInverse (+) x (roppV x)
 := @goppP _ (+) _.

Class IsIntegralDomain := BuildIsIntegralDomain {
integral_ring :> IsRing;
integral_pr :> forall a : G, neq ZeroV a -> forall b : G, neq ZeroV b ->
   neq ZeroV (a°b);
intdom_neq : @neq G ZeroV OneV
}.
Coercion integral_ring : IsIntegralDomain >-> IsRing.

Class IsStrictIntegral {Hg : IsSemiring}
 := isstrictintegral : forall a b : G, ZeroV = a°b
   -> minus1Trunc (ZeroV=a \/ ZeroV=b).

End Prering.

Arguments Zero {_ _ _}.
Arguments ZeroV {_ _ _}.
Arguments ZeroP {_ _ _}.

Arguments One {_ _ _}.
Arguments OneV {_ _ _}.
Arguments OneP {_ _ _}.

Arguments ropp {_ _ _} _.
Arguments roppV {_ _ _} _.
Arguments roppP {_ _ _} _.

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
Coercion decfield_is_ring : IsDecField >-> IsRing.

Class IsField {F} (L : Prefield F) := BuildIsField {
field_is_apart :> Apartness L;
field_is_ring :> IsRing L;
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
Export Ring Field Relation OrderedMagma.

Class IsPosPreserving' {G} (L : PreringRel G)
 := ispospreserving' : forall zero : Identity (+),
                      forall x y : G, rrel (g_id (+)) x
                                   -> rrel (g_id (+)) y 
                                   -> rrel (g_id (+)) (x°y).

Class IsSemiringOrder {G} (L : PreringLeq G) := BuildIsSemiringOrder {
srorder_po :> Poset L;
srorder_partial_minus : forall x y : G, x <= y -> exists z, y = x + z;
srorder_plus :> forall z : G, IsEmbedding L L (plus z);
nonneg_mult_compat :> IsPosPreserving' L
}.
Coercion srorder_po : IsSemiringOrder >-> Poset.
Coercion srorder_plus : IsSemiringOrder >-> Funclass.

Class IsStrictSemiringOrder {G} (L : PreringLt G) :=
 BuildIsStrictSemiringOrder {
strict_srorder_so :> StrictOrder L;
strict_srorder_partial_minus : forall x y : G, x < y -> exists z, y = x + z;
strict_srorder_plus :> forall z : G, IsEmbedding L L (plus z);
pos_mult_compat :> IsPosPreserving' L
}.
Coercion strict_srorder_so : IsStrictSemiringOrder >-> StrictOrder.
Coercion strict_srorder_plus : IsStrictSemiringOrder >-> Funclass.

Class IsPseudoSemiringOrder {G} (L : PreringStrict G) :=
 BuildIsPseudoSemiringOrder {
pseudo_srorder_strict :> PseudoOrder L;
pseudo_srorder_partial_minus : forall x y : G, ~y < x -> exists z, y = x + z;
pseudo_srorder_plus :> forall z : G,
        IsEmbedding (<) (<) (plus z);
pseudo_srorder_mult_ext :> IsBinRegular (° <>);
pseudo_srorder_pos_mult_compat :> IsPosPreserving' (+ ° <)
}.
Coercion pseudo_srorder_strict : IsPseudoSemiringOrder >-> PseudoOrder.
Coercion pseudo_srorder_plus : IsPseudoSemiringOrder >-> Funclass.
Coercion pseudo_srorder_mult_ext : IsPseudoSemiringOrder >-> IsBinRegular.

Class FullPseudoSemiringOrder {G} (L : PreringFull G) :=
  BuildIsFullPseudoSemiringOrder {
full_pseudo_srorder_pso :> IsPseudoSemiringOrder L;
full_pseudo_srorder_le_iff_not_lt_flip : forall x y : G, x <= y <-> ~y < x
}.
Coercion full_pseudo_srorder_pso : FullPseudoSemiringOrder >-> IsPseudoSemiringOrder.


Class FullField {G} (L : PreringFull G) := BuildFullField {
fullfield_field :> IsField L;
fullfield_srorder :> FullPseudoSemiringOrder L
}.
Coercion fullfield_field : FullField >-> IsField.
Coercion fullfield_srorder : FullField >-> FullPseudoSemiringOrder.

Class IsPosPreserving {G} (L : PreringRel G) {Hg : IsSemiring L}
 := ispospreserving : forall x y : G, rrel ZeroV x
                                   -> rrel ZeroV y 
                                   -> rrel ZeroV (x°y).

Instance pospreserving_get {G} (L : PreringRel G) {Hg : IsSemiring L}
 {Hp : IsPosPreserving' L} : IsPosPreserving L := Hp _.


End OrderedRing.




