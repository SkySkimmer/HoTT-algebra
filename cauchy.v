Require Import HoTT.
Require Import FunextAxiom.
Require Import basics quotient hit.Truncations.

Module Cauchy.
Export Field_pr OrderedRing OrderedMagma_pr Relation_pr.

Section VarSec.

Context {T : Type}.
Variable L : PreringFull T.
Context {Hdec : DecidablePaths T} {HpropLt : RelationProp (<)}
 {Hfield : IsDecField L}
 {Hfo : FullPseudoSemiringOrder L} {Htri : Trichotomic (<)}.

Let Hset : IsHSet T := _.

Record Tpos := mkTpos { posV :> T; posP : ZeroV < posV }.

Lemma Tpos_plus_pr : forall a b : Tpos, ZeroV < (a:T) + b.
Proof.
intros.
Admitted.

Instance Tpos_plus : Plus Tpos := fun a b => mkTpos _ (Tpos_plus_pr a b).

Notation "- e" := (inverse_val (ropp e)).

Local Inductive real : Type :=
  | rat : T -> real
  | lim : forall (f : Tpos -> real), (forall d e : Tpos, equiv (d+e) (f d) (f e)) -> real

with equiv : Tpos -> real -> real -> Type :=
  | equiv_rat_rat : forall (q r : T) (e : Tpos),
      - (e : T) < q + (- r) ->
      (q : T) + (- r) < e ->
      equiv e (rat q) (rat r)
  | equiv_rat_lim : forall q y Hy (e d d' : Tpos),
      (e:T) = (d:T) + d' ->
      equiv d' (rat q) (y d) ->
      equiv e (rat q) (lim y Hy)
  | equiv_lim_rat : forall x Hx r (e d d' : Tpos),
      (e:T) = (d:T) + d' ->
      equiv d' (x d) (rat r) ->
      equiv e (lim x Hx) (rat r)
  | equiv_lim_lim : forall x Hx y Hy (e d n e' : Tpos),
      (e:T) = (d:T) + n + e' ->
      equiv e' (x d) (y n) ->
      equiv e (lim x Hx) (lim y Hy)
.






End VarSec.

End Cauchy.
