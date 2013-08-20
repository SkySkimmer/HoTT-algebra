Require Import HoTT.

Require Import basics syntax quotient minus1Trunc.

Module Cauchy.
Import Distributive.
Export Field_pr OrderedRing OrderedMagma_pr.

Section VarSec.

Context {T : Type}.
Variable L : PreringFull T.
Context {Hdec : @Decidable T paths} {HpropLt : RelationProp (<)}
 {Hfield : IsDecField L}
 {Hfo : FullPseudoSemiringOrder L} {Htri : Trichotomic (<)}.

Let Hset : IsHSet T := hset_decidable Hdec.

Record Tpos := mkTpos { posV :> T; posP : ZeroV < posV }.

Local Inductive realU : Type :=
  | ratU : T -> realU
  | limU : forall (f : Tpos -> realU),
       (forall d e : Tpos, equivU ((d:T)+(e:T))) -> realU

with equivU : T -> Type :=
  | rat_rat_U : forall (q r : T) (e : Tpos),
       roppV (e:T) < q + (roppV r) -> q + (roppV r) < e -> equivU e
  | rat_lim_U : forall (q : T) (y : Tpos -> realU)
       (Hy : forall d e : Tpos, equivU ((d:T)+(e:T))) (e d : Tpos),
       equivU ((e:T) + (roppV (d:T))) -> equivU e
  | lim_rat_U : forall (x : Tpos -> realU) (Hx : forall e d : Tpos,
        equivU ((e:T)+(d:T))) (r : T) (e d : Tpos),
       equivU ((e:T) + (roppV (d:T))) -> equivU e
  | lim_lim_U : forall (x y : Tpos -> realU) (Hx : forall e d : Tpos,
        equivU ((e:T)+(d:T))) (Hy : forall e d : Tpos,
        equivU ((e:T)+(d:T))) (e d n : Tpos),
       equivU ((e:T) + (roppV ((d:T)+(n:T)))) -> equivU e
.

Local Inductive correctR : realU -> Type :=
  | co_rat : forall q, correctR (ratU q)
  | co_lim : forall (f : Tpos -> realU)
      (Hf : forall d e : Tpos, equivU ((d:T)+(e:T))),
      (forall d e, correctEq (f d) (f e) (Hf d e)) -> correctR (limU f Hf)

with correctEq : forall {e : T}, realU -> realU -> equivU e -> Type :=
  | co_rat_rat : forall (q r : T) (e : Tpos)
         (H : roppV (e:T) < q + (roppV r)) (H' : q + (roppV r) < e),
          correctEq (ratU q) (ratU r) (rat_rat_U q r e H H')
  | co_rat_lim : forall (q : T) (y : Tpos -> realU),
         (forall e, correctR (y e)) ->
         forall (Hy : forall e d : Tpos, equivU ((e:T) + (d:T))),
       (forall e d : Tpos, correctEq (y e) (y d) (Hy e d)) ->
       forall (e d : Tpos) (Heq : equivU ((e:T) + roppV (d:T))),
       correctEq (ratU q) (y d) Heq ->
       correctEq (ratU q) (limU y Hy) (rat_lim_U q y Hy e d Heq)
  | co_lim_rat : forall (x : Tpos -> realU),
          (forall e, correctR (x e)) ->
         forall (Hx : forall e d : Tpos, equivU ((e:T) + (d:T))),
       (forall e d : Tpos, correctEq (x e) (x d) (Hx e d)) ->
       forall (r : T) (e d : Tpos) (Heq : equivU ((e:T) + roppV (d:T))),
       correctEq (x d) (ratU r) Heq ->
       correctEq (limU x Hx) (ratU r) (lim_rat_U x Hx r e d Heq)
  | co_lim_lim : forall (x : Tpos -> realU),
          (forall e, correctR (x e)) ->
         forall (Hx : forall e d : Tpos, equivU ((e:T) + (d:T))),
       (forall e d : Tpos, correctEq (x e) (x d) (Hx e d)) ->
       forall (y : Tpos -> realU),
          (forall e, correctR (y e)) ->
         forall (Hy : forall e d : Tpos, equivU ((e:T) + (d:T))),
       (forall e d : Tpos, correctEq (y e) (y d) (Hy e d)) ->
       forall (e d n : Tpos) (Heq : equivU ((e:T) + roppV ((d:T) + (n:T)))),
       correctEq (x d) (y n) Heq ->
       correctEq (limU x Hx) (limU y Hy) (lim_lim_U x y Hx Hy e d n Heq)
.

Definition real := sigT correctR.
Definition equiv (e : T) (x y : real) := sigT (@correctEq e x.1 y.1).

Definition rat : T -> real.
Proof.
intros q;exists (ratU q). constructor.
Defined.

Instance plus_pos : Plus Tpos.
Proof.
intros x y. exists ((x:T)+(y:T)).
pattern ZeroV. apply transport with (ZeroV + ZeroV).
apply Zero.
pose (H := @iscompat T (+ <)).
unfold IsBinMorphism in H. unfold rrel,gop in H. simpl in H.
apply H;try apply posP.
clear H.
apply invariant_compat.
unfold rrel. simpl. apply (@fullpartial_trans T L).
apply fullpseudo_is_fullposet. apply _. split. apply Hfo.
apply Hfo.
apply linvariant_invariant. apply _.
red. apply _.
Defined.

Definition lim : forall f : Tpos -> real,
 (forall e d : Tpos, equiv ((e:T)+(d:T)) (f e) (f d)) -> real.
Proof.
intros f Hf.
exists (limU (fun e => (f e).1) (fun d e => (Hf d e).1)).
constructor.
intros. apply ((Hf d e).2).
Defined.

Definition rat_rat : forall (q r : T) (e : Tpos),
(roppV (e:T) < q + (roppV r)) -> (q + (roppV r) < e) -> equiv e (rat q) (rat r).
Proof.
intros q r e H H'.
exists (rat_rat_U q r e H H').
constructor.
Defined.

Definition rat_lim : forall (q : T) (y : Tpos -> real)
(Hy : forall e d : Tpos, equiv ((e:T)+(d:T)) (y e) (y d))
 (e d : Tpos),
equiv ((e:T)+(roppV (d:T))) (rat q) (y d) -> equiv e (rat q) (lim y Hy).
Proof.
intros ? ? ? ? ? H.
econstructor. constructor.
intros e'. apply ((y e') .2).
intros e' d'. apply ((Hy e' d').2).
apply (H.2).
Defined.

Definition lim_rat : forall (x : Tpos -> real)
 (Hx : forall e d : Tpos, equiv ((e:T)+(d:T)) (x e) (x d))
   (r : T) (e d : Tpos),
  equiv ((e:T)+(roppV (d:T))) (x d) (rat r) -> equiv e (lim x Hx) (rat r).
Proof.
intros ? ? ? ? ? H.
econstructor. constructor.
intros e'. apply ((x e').2).
intros e' d'. apply ((Hx e' d').2).
apply (H.2).
Defined.

Definition lim_lim : forall (x : Tpos -> real) Hx (y : Tpos -> real) Hy
  (e d n : Tpos), equiv ((e:T)+(roppV ((d:T)+(n:T)))) (x d) (y n) ->
  equiv e (lim x Hx) (lim y Hy).
Proof.
intros ? ? ? ? ? ? ? H.
econstructor.
apply co_lim_lim. Focus 5. apply (H.2).

intros e'. apply ((x e').2).
intros e' d'. apply ((Hx e' d').2).
intros e'. apply ((y e').2).
intros e' d'. apply ((Hy e' d').2).
Defined.

Definition cauchyApprox (f : Tpos -> real) :=
 forall e d : Tpos, equiv ((e:T)+(d:T)) (f e) (f d).

Axiom eqr : forall {x y : real}, (forall e : Tpos, equiv e x y) -> x=y.
Axiom eqequiv : forall e x y (u v : equiv e x y), u=v.


Axiom ADMIT : forall {P : Type}, P.

Section Rect0.

Variables (A : realU -> Type) (B : forall x, A x -> forall y, A y ->
      forall e, equivU e -> Type).

Fixpoint R_rect (r : realU) : A r := ADMIT

with E_rect x y e (He : equivU e) : B x (R_rect r) y (R_rect y) e He
 := ADMIT.

End Rect0.



Section Rect.

Variables (A : real -> Type) (B : forall x, A x -> forall y, A y ->
    forall e, equiv e x y -> Type).

Definition depCauchy x (Hx : cauchyApprox x)
 (a : forall e, A (x e)) := forall d e : Tpos,
     B (x d) (a d) (x e) (a e) ((d:T)+(e:T)) (Hx d e).

Variables (frat : forall q : T, A (rat q))
(flim : forall x (Hx : cauchyApprox x) a (Ha : depCauchy x Hx a),
     A (lim x Hx)).

Variable Heqr : forall (u v : real) (He : forall e : Tpos, equiv e u v)
   (a : A u) (b : A v) (He' : forall e : Tpos, B u a v b e (He e)),
      transport A (eqr He) a = b.

Variable Hrat_rat : forall q r (e:Tpos) H H',
    B (rat q) (frat q) (rat r) (frat r) e (rat_rat q r e H H').

Variable Hrat_lim : forall (q : T) y (Hy : cauchyApprox y)
 b (Hb : depCauchy y Hy b) (d e : Tpos) 
  (He : equiv ((e:T)+(roppV (d:T))) (rat q) (y d)),
    B (rat q) (frat q) (y d) (b d) ((e:T)+(roppV (d:T))) He ->
      B (rat q) (frat q) (lim y Hy) (flim y Hy b Hb) e (rat_lim q y Hy _ _ He).

Variable Hlim_rat : forall x (Hx : cauchyApprox x) a (Ha : depCauchy x Hx a)
  (r : T) (d e : Tpos)
    (He : equiv ((e:T)+(roppV (d:T))) (x d) (rat r)),
      B (x d) (a d) (rat r) (frat r) _ He ->
        B (lim x Hx) (flim x Hx a Ha) (rat r) (frat r) e (lim_rat x Hx r _ _ He).

Variable Hlim_lim : forall x (Hx : cauchyApprox x) a (Ha : depCauchy x Hx a)
y (Hy : cauchyApprox y) b (Hb: depCauchy y Hy b) (e d n : Tpos)
    (He : equiv ((e:T)+(roppV ((d:T)+(n:T)))) (x d) (y n)),
      B (x d) (a d) (y n) (b n) _ He ->
        B (lim x Hx) (flim x Hx a Ha) (lim y Hy) (flim y Hy b Hb) e
                   (lim_lim x Hx y Hy _ _ _ He).

Variable Heqequiv : forall (e : Tpos) (x y : real)
(eq eq' : equiv e x y) (a : A x) (b : A y)
(u : B x a y b e eq) (v : B x a y b e eq'),
  transport _ (eqequiv e x y _ _) u = v.

Fixpoint real_rect0 (x : realU) (Hx : correctR x) : A (existT _ x Hx)
 := ADMIT

with equiv_rect0 (x : realU) (Hx : correctR x) (y : realU) (Hy : correctR y)
(e : Tpos) (He : equivU e) (Hc : correctEq x y He)
 : B _ (real_rect0 x Hx) _ (real_rect0 y Hy) e (existT _ He Hc)
 := ADMIT.

End Rect.



End VarSec.






End Cauchy.