Require Import HoTT FunextAxiom UnivalenceAxiom.
Require Export basics.

(*
Results about types where some relations (equality/order) are decidable
*)

Module DecOrder.
Export Relation_pr.

Section VarSec.

Context {T : Type}.
Variable L : FullRelation T.

Lemma leqdec_eqdec {Hpo : Poset (<=)} : Decidable (<=) -> decidable_paths T.
Proof.
intros H x y.
destruct (H x y);[destruct (H y x);[left;apply antisymmetric;assumption|]|];
right;intros p;destruct p;apply n;apply @reflexivity;apply Hpo.
Defined.

Global Instance leqdec_ltdec {Htr : TrivialApart (<>)} {Hpo : FullPoset L}
 : Decidable (<=) -> Decidable (<).
Proof.
intros Hdec x y.
unfold rrel.
destruct (Hdec x y) as [H|H];unfold rrel in H.
destruct (leqdec_eqdec Hdec x y).
right;intro H'. apply lt_iff_le_apart in H'. destruct H' as [H' H1].
apply Htr in H1. apply H1. assumption.
left. apply lt_iff_le_apart. split. assumption. apply Htr;assumption.
right;intro H';apply lt_iff_le_apart in H';destruct H';auto.
Defined.

(* we use neq_apart more often but this justifies that neq is the only apartness on decidable sets *)
Global Instance apartdec_trivial {Hap : Apartness (<>)} {Hdec : Decidable (<>)}
 : TrivialApart (<>).
Proof.
red. intros. split.
intros H H'.
destruct H'.
eapply irrefl. apply H.
intros H. destruct (Hdec x y). assumption.
destruct H. apply Hap. assumption.
Defined.

Lemma linear_dec_trichotomic {Hdec : Decidable (<=)} 
{Htr : TrivialApart (<>)} {Hlin : ConstrLinear (<=)}
{Hfull : FullPoset L} : Trichotomic (<).
Proof.
intros x y.
destruct (Hdec y x).
right.
destruct (Hdec x y).
left. apply antisymmetric;assumption.
right. apply lt_iff_le_apart. split.
assumption.
apply Htr. intro H'. destruct H'. auto.
left.
apply lt_iff_le_apart. split.
destruct (Hlin x y). assumption.
apply Empty_rect;auto.
apply Htr. intros p;destruct p. apply n;apply Hfull.
Defined.

End VarSec.

End DecOrder.

