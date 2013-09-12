Require Import HoTT.
Require Import FunextAxiom.
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
  | co_lim : forall (f : Tpos -> realU) (Hc : forall e, correctR (f e))
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
intros;apply projT2.
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

(*
Fixpoint real_rectU (A : real -> Type) (frat : forall q, A (rat q))
(flim : forall x (Hx : cauchyApprox x) (a : forall e, A (x e)), A (lim x Hx))
(p : forall u v : real, forall (h : forall e : Tpos, equiv e u v),
forall a : A u, forall b : A v, transport _ (eqr h) a = b)
(x : realU) (Hx : correctR x) : A (x;Hx) :=
match Hx as Hx0 in (correctR x0) return _ -> (A (x0;Hx0)) with
  | co_rat q => fun _ => frat q
  | co_lim f fc Hf Hfc => fun p => flim (fun e => (f e; fc e))
                               (fun d e => (Hf d e ; Hfc d e)) 
                               (fun e => real_rectU A frat flim p (f e) (fc e))
  end p.

Definition real_rect (A : real -> Type) (frat : forall q, A (rat q))
(flim : forall x (Hx : cauchyApprox x) (a : forall e, A (x e)), A (lim x Hx))
(p : forall u v : real, forall (h : forall e : Tpos, equiv e u v),
forall a : A u, forall b : A v, transport _ (eqr h) a = b)
(X : real) : A X := match X with
  | existT x Hx => real_rectU A frat flim p x Hx
  end.

Lemma real_rect_rat : forall A frat flim p q,
real_rect A frat flim p (rat q) = frat q.
Proof.
intros;reflexivity.
Defined.

Lemma real_rect_lim : forall A frat flim p x Hx,
real_rect A frat flim p (lim x Hx) = flim x Hx
   (fun e => real_rect A frat flim p (x e)).
Proof.
intros;simpl.
admit.
Defined.

Axiom ADMIT : forall {P : Type}, P.


Definition real_rect (A : real -> Type) (frat : forall q, A (rat q))
(flim : forall x (Hx : cauchyApprox x) (a : forall e, A (x e)), A (lim x Hx))
(p : forall u v : real, forall (h : forall e : Tpos, equiv e u v),
forall a : A u, forall b : A v, transport _ (eqr h) a = b)
(X : real) : A X.
Proof.
destruct X as [x Hx].

Defined.
*)

(*
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


Local Inductive gA : real -> Type :=
  | rat_gA : forall q, gA (rat q)
  | lim_gA : forall 

with gB : 



Fixpoint real_rect0 (x : realU) (Hx : correctR x) : A (existT _ x Hx)
 := ADMIT

with equiv_rect0 (x : realU) (Hx : correctR x) (y : realU) (Hy : correctR y)
(e : Tpos) (He : equivU e) (Hc : correctEq x y He)
 : B _ (real_rect0 x Hx) _ (real_rect0 y Hy) e (existT _ He Hc)
 := ADMIT.

End Rect.

*)

(* I think these can be proven but will consider later *)
Global Instance correctR_is_prop : forall x, IsHProp (correctR x).
Admitted.
Global Instance correctEq_is_prop : forall e x y H, IsHProp (@correctEq e x y H).
Admitted.

Section OBS.

Variables (A : forall r : realU, correctR r -> Type)
  (B : forall (e : T) (x y : realU) (He : equivU e), correctEq x y He -> Type)

  (frat : forall q : T, A (ratU q) (co_rat q))
  (flim : forall (x : Tpos -> realU) (xc : forall e : Tpos, correctR (x e)),
        (forall e : Tpos, A (x e) (xc e)) ->
        forall (Hx : forall d e : Tpos, equivU ((d:T) + (e:T)))
          (Hxc : forall d e : Tpos, correctEq (x d) (x e) (Hx d e)),
        (forall d e : Tpos, B ((d:T) + (e:T)) (x d) (x e) (Hx d e) (Hxc d e)) ->
        A (limU x Hx) (co_lim x xc Hx Hxc))

  (Hrat_rat : forall (q r : T) (e : Tpos) (H : roppV (e:T) < q + roppV r)
          (H' : q + roppV r < e),
        B e (ratU q) (ratU r) (rat_rat_U q r e H H') (co_rat_rat q r e H H'))

  (Hrat_lim : forall (q : T) (y : Tpos -> realU) (yc : forall e : Tpos, correctR (y e)),
        (forall e : Tpos, A (y e) (yc e)) ->
        forall (Hy : forall e d : Tpos, equivU ((e:T) + (d:T)))
          (Hyc : forall e d : Tpos, correctEq (y e) (y d) (Hy e d)),
        (forall e d : Tpos, B ((e:T) + (d:T)) (y e) (y d) (Hy e d) (Hyc e d)) ->
        forall (e d : Tpos) (Heq : equivU ((e:T) + roppV (d:T)))
          (Heqc : correctEq (ratU q) (y d) Heq),
        B ((e:T) + roppV (d:T)) (ratU q) (y d) Heq Heqc ->
        B e (ratU q) (limU y Hy) (rat_lim_U q y Hy e d Heq)
          (co_rat_lim q y yc Hy Hyc e d Heq Heqc))

  (Hlim_rat : forall (x : Tpos -> realU) (xc : forall e : Tpos, correctR (x e)),
        (forall e : Tpos, A (x e) (xc e)) ->
        forall (Hx : forall e d : Tpos, equivU ((e:T) + (d:T)))
          (Hxc : forall e d : Tpos, correctEq (x e) (x d) (Hx e d)),
        (forall e d : Tpos, B ((e:T) + (d:T)) (x e) (x d) (Hx e d) (Hxc e d)) ->
        forall (r : T) (e d : Tpos) (Heq : equivU ((e:T) + roppV (d:T)))
          (Heqc : correctEq (x d) (ratU r) Heq),
        B ((e:T) + roppV (d:T)) (x d) (ratU r) Heq Heqc ->
        B e (limU x Hx) (ratU r) (lim_rat_U x Hx r e d Heq)
          (co_lim_rat x xc Hx Hxc r e d Heq Heqc))

  (Hlim_lim : forall (x : Tpos -> realU) (xc : forall e : Tpos, correctR (x e)),
        (forall e : Tpos, A (x e) (xc e)) ->
        forall (Hx : forall e d : Tpos, equivU ((e:T) + (d:T)))
          (Hxc : forall e d : Tpos, correctEq (x e) (x d) (Hx e d)),
        (forall e d : Tpos, B ((e:T) + (d:T)) (x e) (x d) (Hx e d) (Hxc e d)) ->
        forall (y : Tpos -> realU) (yc : forall e : Tpos, correctR (y e)),
        (forall e : Tpos, A (y e) (yc e)) ->
        forall (Hy : forall e d : Tpos, equivU ((e:T) + (d:T)))
          (Hyc : forall e d : Tpos, correctEq (y e) (y d) (Hy e d)),
        (forall e d : Tpos, B ((e:T) + (d:T)) (y e) (y d) (Hy e d) (Hyc e d)) ->
        forall (e d n : Tpos) (Heq : equivU ((e:T) + roppV ((d:T) + (n:T))))
          (Heqc : correctEq (x d) (y n) Heq),
        B ((e:T) + roppV ((d:T) + (n:T))) (x d) (y n) Heq Heqc ->
        B e (limU x Hx) (limU y Hy) (lim_lim_U x y Hx Hy e d n Heq)
          (co_lim_lim x xc Hx Hxc y yc Hy Hyc e d n Heq Heqc)).


Local Fixpoint real_rect0 (x : realU) (xc : correctR x) : A x xc :=
  match xc as xc0 in (correctR x0) return (A x0 xc0) with
  | co_rat q => frat q
  | co_lim x xc Hx Hxc =>
      flim x xc (fun e : Tpos => real_rect0 (x e) (xc e)) Hx Hxc
        (fun d e : Tpos => equiv_rect0 ((d:T) + (e:T)) (x d) (x e) (Hx d e) (Hxc d e))
  end
with equiv_rect0 (e : T) (x y : realU) (H : equivU e) (Hc : correctEq x y H) :
  B e x y H Hc :=
  match Hc as Hc0 in (@correctEq e0 x0 y0 H0) return (B e0 x0 y0 H0 Hc0) with
  | co_rat_rat q x e H H' => Hrat_rat q x e H H'
  | co_rat_lim q y yc Hy Hyc e d Heq Heqc =>
      Hrat_lim q y yc (fun e : Tpos => real_rect0 (y e) (yc e)) Hy Hyc
        (fun e d : Tpos =>
         equiv_rect0 ((e:T) + (d:T)) (y e) (y d) (Hy e d) (Hyc e d))
        e d Heq Heqc
        (equiv_rect0 ((e:T) + roppV (d:T)) (ratU q) (y d) Heq Heqc)
  | co_lim_rat x xc Hx Hxc r e d Heq Heqc =>
      Hlim_rat x xc (fun e : Tpos => real_rect0 (x e) (xc e)) Hx Hxc
        (fun e d : Tpos =>
         equiv_rect0 ((e:T) + (d:T)) (x e) (x d) (Hx e d) (Hxc e d))
        r e d Heq Heqc
        (equiv_rect0 ((e:T) + roppV (d:T)) (x d) (ratU r) Heq Heqc)
  | co_lim_lim x xc Hx Hxc y yc Hy Hyc e d n Heq Heqc =>
      Hlim_lim x xc (fun e : Tpos => real_rect0 (x e) (xc e)) Hx Hxc
        (fun e d : Tpos =>
         equiv_rect0 ((e:T) + (d:T)) (x e) (x d) (Hx e d) (Hxc e d))
        y yc (fun e : Tpos => real_rect0 (y e) (yc e)) Hy Hyc
        (fun e d : Tpos =>
         equiv_rect0 ((e:T) + (d:T)) (y e) (y d) (Hy e d) (Hyc e d))
        e d n Heq Heqc
        (equiv_rect0 ((e:T) + roppV ((d:T) + (n:T))) (x d) (y n) Heq Heqc)
  end.

End OBS.

Lemma correctEq_left : forall {e x y H}, @correctEq e x y H -> correctR x.
Proof.
intros. destruct X;constructor;auto.
Defined.

Lemma correctEq_right : forall {e x y H}, @correctEq e x y H -> correctR y.
Proof.
intros;destruct X;constructor;auto.
Defined.


Section Rect.

Variables (A : real -> Type)
  (B : forall (e : T) (x y : real) (He : equiv e x y), Type)

  (frat : forall q : T, A (rat q))
  (flim : forall (x : Tpos -> real),
        (forall e : Tpos, A (x e)) ->
         forall (Hx : cauchyApprox x),
        (forall d e : Tpos, B ((d:T) + (e:T)) (x d) (x e) (Hx d e)) ->
        A (lim x Hx))

  (Hrat_rat : forall (q r : T) (e : Tpos) (H : roppV (e:T) < q + roppV r)
          (H' : q + roppV r < e),
        B e (rat q) (rat r) (rat_rat q r e H H'))

  (Hrat_lim : forall (q : T) (y : Tpos -> real),
        (forall e : Tpos, A (y e)) ->
        forall (Hy : cauchyApprox y),
        (forall e d : Tpos, B ((e:T) + (d:T)) (y e) (y d) (Hy e d)) ->
        forall (e d : Tpos) (Heq : equiv ((e:T) + roppV (d:T)) (rat q) (y d)),
        B ((e:T) + roppV (d:T)) (rat q) (y d) Heq ->
        B e (rat q) (lim y Hy) (rat_lim q y Hy e d Heq))

  (Hlim_rat : forall (x : Tpos -> real),
        (forall e : Tpos, A (x e)) ->
        forall (Hx : cauchyApprox x),
        (forall e d : Tpos, B ((e:T) + (d:T)) (x e) (x d) (Hx e d)) ->
        forall (r : T) (e d : Tpos)
         (Heq : equiv ((e:T) + roppV (d:T)) (x d) (rat r)),
        B ((e:T) + roppV (d:T)) (x d) (rat r) Heq ->
        B e (lim x Hx) (rat r) (lim_rat x Hx r e d Heq))

  (Hlim_lim : forall (x : Tpos -> real),
        (forall e : Tpos, A (x e)) ->
        forall (Hx : cauchyApprox x),
        (forall e d : Tpos, B ((e:T) + (d:T)) (x e) (x d) (Hx e d)) ->
        forall (y : Tpos -> real),
        (forall e : Tpos, A (y e)) ->
        forall (Hy : cauchyApprox y),
        (forall e d : Tpos, B ((e:T) + (d:T)) (y e) (y d) (Hy e d)) ->
        forall (e d n : Tpos)
         (Heq : equiv ((e:T) + roppV ((d:T) + (n:T))) (x d) (y n)),
        B ((e:T) + roppV ((d:T) + (n:T))) (x d) (y n) Heq ->
        B e (lim x Hx) (lim y Hy) (lim_lim x Hx y Hy e d n Heq)).

Let A0 : forall x : realU, correctR x -> Type := fun x xc => A (x;xc).
Let B0 : forall (e : T) (x y : realU) (He : equivU e), correctEq x y He -> Type.
Proof.
intros ? ? ? ? Hec.
apply B with e (x;correctEq_left Hec) (y;correctEq_right Hec).
exists He.
simpl. assumption.
Defined.

Definition real_rect : forall x, A x.
Proof.
intros x. destruct x as [x xc].
eapply (real_rect0 A0 B0);unfold A0;unfold B0;simpl;clear xc;clear x A0 B0.
- apply frat.
- intros ? ? ? ? ? IH.
  change (A (lim (fun e => (x e; xc e)) (fun d e => (Hx d e; Hxc d e)))).
  apply flim; auto.
  intros.
  pattern (xc e);eapply transport;
  [|pattern (xc d);eapply transport;[|apply IH]];
  apply allpath_hprop.

- auto.

- intros ? ? ? IHy ? ? IH ? ? ? ? IH0.
  change (ratU q; co_rat q) with (rat q).
  change (limU y Hy; co_lim y yc Hy Hyc) with
     (lim (fun e => (y e; yc e)) (fun d e => (Hy d e; Hyc d e))).
  change (rat_lim_U q y Hy e d Heq; co_rat_lim q y yc Hy Hyc e d Heq Heqc)
  with (rat_lim q (fun e => (y e; yc e)) (fun d e => (Hy d e; Hyc d e))
    e d (Heq;Heqc)).
  apply Hrat_lim. auto.
  clear IH0 Heqc Heq d e.
  intros e d;pattern (yc d);eapply transport;
  [|pattern (yc e);eapply transport;[|apply IH]];
  apply allpath_hprop.
  unfold rat. pattern (co_rat q);eapply transport;
  [|pattern (yc d);eapply transport;[|apply IH0]];apply allpath_hprop.

- intros ? ? IHx ? ? IH ? ? ? ? ? IH0.
  change (B e (lim (fun e => (x e; xc e)) (fun d e => (Hx d e; Hxc d e)))
    (rat r) (lim_rat (fun e => (x e; xc e)) (fun d e => (Hx d e; Hxc d e))
        r e d (Heq;Heqc))).
  apply Hlim_rat. auto.
  clear IH0 Heqc Heq d e.
  intros d e. pattern (xc d);eapply transport;
  [|pattern (xc e);eapply transport;[|apply IH]];
  apply allpath_hprop.
  unfold rat. pattern (co_rat r);eapply transport;
  [|pattern (xc d);eapply transport;[|apply IH0]];apply allpath_hprop.

- intros ? ?  IHx ? ? IHx' ? ? IHy ? ? IHy' ? ? ? ? ? IH.
  change (B e (lim (fun e => (x e; xc e)) (fun d e => (Hx d e; Hxc d e)))
              (lim (fun e => (y e; yc e)) (fun d e => (Hy d e; Hyc d e)))
              (lim_lim (fun e => (x e; xc e)) (fun d e => (Hx d e; Hxc d e))
                       (fun e => (y e; yc e)) (fun d e => (Hy d e; Hyc d e))
                       e d n (Heq;Heqc))).
  apply Hlim_lim;auto;[clear IH Heqc Heq n d e|clear IH Heqc Heq n d e|];
  intros.
  pattern (xc e);eapply transport;
  [|pattern (xc d);eapply transport;[|apply IHx']];apply allpath_hprop.
  pattern (yc e);eapply transport;
  [|pattern (yc d);eapply transport;[|apply IHy']];apply allpath_hprop.
  pattern (xc d);eapply transport;
  [|pattern (yc n);eapply transport;[|apply IH]];apply allpath_hprop.
Defined.

Definition equiv_rect : forall e x y H, B e x y H.
Proof.
intros e [x xc] [y yc] [H Hc].
simpl in Hc.
pattern xc;apply transport with (correctEq_left Hc). apply allpath_hprop.
pattern yc;apply transport with (correctEq_right Hc). apply allpath_hprop.
eapply (equiv_rect0 A0 B0);unfold A0;unfold B0;simpl;
clear Hc H yc y xc x e A0 B0.
- apply frat.
- intros ? ? ? ? ? IH.
  change (A (lim (fun e => (x e; xc e)) (fun d e => (Hx d e; Hxc d e)))).
  apply flim; auto.
  intros.
  pattern (xc e);eapply transport;
  [|pattern (xc d);eapply transport;[|apply IH]];
  apply allpath_hprop.

- auto.

- intros ? ? ? IHy ? ? IH ? ? ? ? IH0.
  change (ratU q; co_rat q) with (rat q).
  change (limU y Hy; co_lim y yc Hy Hyc) with
     (lim (fun e => (y e; yc e)) (fun d e => (Hy d e; Hyc d e))).
  change (rat_lim_U q y Hy e d Heq; co_rat_lim q y yc Hy Hyc e d Heq Heqc)
  with (rat_lim q (fun e => (y e; yc e)) (fun d e => (Hy d e; Hyc d e))
    e d (Heq;Heqc)).
  apply Hrat_lim. auto.
  clear IH0 Heqc Heq d e.
  intros e d;pattern (yc d);eapply transport;
  [|pattern (yc e);eapply transport;[|apply IH]];
  apply allpath_hprop.
  unfold rat. pattern (co_rat q);eapply transport;
  [|pattern (yc d);eapply transport;[|apply IH0]];apply allpath_hprop.

- intros ? ? IHx ? ? IH ? ? ? ? ? IH0.
  change (B e (lim (fun e => (x e; xc e)) (fun d e => (Hx d e; Hxc d e)))
    (rat r) (lim_rat (fun e => (x e; xc e)) (fun d e => (Hx d e; Hxc d e))
        r e d (Heq;Heqc))).
  apply Hlim_rat. auto.
  clear IH0 Heqc Heq d e.
  intros d e. pattern (xc d);eapply transport;
  [|pattern (xc e);eapply transport;[|apply IH]];
  apply allpath_hprop.
  unfold rat. pattern (co_rat r);eapply transport;
  [|pattern (xc d);eapply transport;[|apply IH0]];apply allpath_hprop.

- intros ? ?  IHx ? ? IHx' ? ? IHy ? ? IHy' ? ? ? ? ? IH.
  change (B e (lim (fun e => (x e; xc e)) (fun d e => (Hx d e; Hxc d e)))
              (lim (fun e => (y e; yc e)) (fun d e => (Hy d e; Hyc d e)))
              (lim_lim (fun e => (x e; xc e)) (fun d e => (Hx d e; Hxc d e))
                       (fun e => (y e; yc e)) (fun d e => (Hy d e; Hyc d e))
                       e d n (Heq;Heqc))).
  apply Hlim_lim;auto;[clear IH Heqc Heq n d e|clear IH Heqc Heq n d e|];
  intros.
  pattern (xc e);eapply transport;
  [|pattern (xc d);eapply transport;[|apply IHx']];apply allpath_hprop.
  pattern (yc e);eapply transport;
  [|pattern (yc d);eapply transport;[|apply IHy']];apply allpath_hprop.
  pattern (xc d);eapply transport;
  [|pattern (yc n);eapply transport;[|apply IH]];apply allpath_hprop.
Defined.


End Rect.




End VarSec.






End Cauchy.
Import Cauchy.


