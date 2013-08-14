Require Import HoTT.
Require Import structures.

Module NEList.
Export Magma.

Inductive NEList (A : Type) : Type :=
  | single : A -> NEList A
  | cons : A -> NEList A -> NEList A
.
Arguments single {_} _.
Arguments cons {_} _ _.

Fixpoint Napp {A} (l l' : (NEList A)) : (NEList A) := 
  match l with
    | single i => cons i l'
    | cons i l => cons i (Napp l l')
    end.

Section VarSec.

Context {A} {G : Gop A}.

Definition someOp : Gop (option A) := fun a b => match a,b with
  | Some x, Some y => Some (gop x y)
  | _, _ => None
  end.

Fixpoint evalNE {B} (f : B -> option A) (l : (NEList B))
 : option A := match l with
    | cons i l => someOp (f i) (evalNE f l)
    | single i => f i
    end.

Global Instance someOp_assoc : forall {Hassoc : Associative G},
Associative someOp.
Proof.
red. destruct x,y,z;simpl;auto.
unfold gop;simpl. apply ap;apply Hassoc.
Defined.

Global Instance someOp_comm : forall {Hcomm : Commutative G},
Commutative someOp.
Proof.
red;destruct x,y;simpl;auto.
apply (ap (@Some _));apply Hcomm.
Defined.

Lemma evalNE_app : forall {Hassoc : Associative G},
  forall {B} (f : B -> option A) l l', 
  evalNE f (Napp l l') = someOp (evalNE f l) (evalNE f l').
Proof.
induction l;intros;simpl in *.
reflexivity.
path_via (someOp (f a) (someOp (evalNE f l) (evalNE f l'))).
apply ap. apply IHl.
apply someOp_assoc.
Defined.

Lemma NEList_eq_dec : decidable_paths A ->
 decidable_paths (NEList A).
Proof.
red. intros Ha.
induction x;destruct y.
destruct (Ha a a0);[left|right].
apply ap;assumption.
exact (fun H => n (ap (fun s => match s with 
  | single x => x | _ => a end) H)).
right;exact (fun H => transport (fun s => match s with
  | single _ => Unit | _ => Empty end) H tt).
right;exact (fun H => transport (fun s => match s with
  | single _ => Empty | _ => Unit end) H tt).
destruct (Ha a a0).
destruct (IHx y).
left;apply ap11;[apply ap|];assumption.
right;exact (fun H => n (ap (fun s => match s with
  | cons _ z => z | single _ => x end) H)).
right;exact (fun H => n (ap (fun s => match s with
  | cons z _ => z | _ => a end) H)).
Defined.

End VarSec.

Section Sort.

Context {A : Type}.
Variable order_dec : A -> A -> Bool.

Fixpoint sortInsert i l := match l with
  | single j => if order_dec i j
    then cons i (single j)
    else cons j (single i)
  | cons j l => if order_dec i j
    then cons i (cons j l)
    else cons j (sortInsert i l)
  end.

Fixpoint sort l := match l with
  | single i => single i
  | cons i l => sortInsert i (sort l)
  end.

Lemma sortInsert_correct : forall {B} {G:Gop B} {Hsg : IsSemigroup G}, 
forall (f : A -> option B) i l,
 evalNE f (sortInsert i l) = evalNE f (cons i l).
Proof.
simpl. induction l.
- simpl. destruct (order_dec i a);simpl;first [reflexivity | apply someOp_comm].
- simpl. destruct (order_dec i a);simpl.
  reflexivity.
  path_via (someOp (f a) (someOp (f i) (evalNE f l))).
  apply ap. assumption.
  path_via (someOp (someOp (f a) (f i)) (evalNE f l)).
  apply someOp_assoc.
  path_via (someOp (someOp (f i) (f a)) (evalNE f l)).
  apply ap10. apply ap. apply someOp_comm.
  apply inverse;apply someOp_assoc.
Defined.

Lemma sort_correct : forall {B} {G:Gop B} {Hsg : IsSemigroup G}, 
  forall (f : A -> option B) l, evalNE f (sort l) = evalNE f l.
Proof.
induction l;simpl.
- reflexivity.
- eapply concat.
  apply sortInsert_correct. simpl.
  apply ap. assumption.
Defined.

End Sort.

Arguments sort_correct {_} _ {_ _ _} _ _.

Definition nat_order_dec : nat -> nat -> Bool.
Proof.
intros n;induction n;intros m.
- (*0 < m *) destruct m;[exact false | exact true].
- (* S n < m *) destruct m.
  (* S n < 0 *) exact false.
  (* S n < S m *) exact (IHn m).
Defined.

Definition NEList_order_dec : forall {A} (order_dec : A -> A -> Bool), 
forall l l' : NEList A, Bool.
Proof.
intros ? ? l;induction l as [x | x l];intro l';destruct l' as [y | y l'].
- (* [x] < [y] *) exact (order_dec x y).
- (* [x] < y::l', l' <> [] *) exact (negb (order_dec y x)).
- (* x::l < [y], l <> [] *) exact (negb (order_dec x y)).
- (* x::l < y::l', IHl is l < _ *) exact (orb (order_dec x y)
                             (andb (negb (order_dec y x)) (IHl l'))).
Defined.

Definition NEList_nat_order_dec := NEList_order_dec nat_order_dec.

End NEList.

Export NEList.

Module BinOpTree.
Import ListNotations.

Inductive T (A : Type) : Type := 
  | Op : T A -> T A -> T A
  | Val : A -> T A
.

Arguments Op {_} _ _.
Arguments Val {_} _.

Fixpoint evalTree {A} {G:Gop A} {B} (f : B -> option A) (t : T B) : option A :=
  match t with
    | Op t1 t2 => someOp (evalTree f t1) (evalTree f t2)
    | Val i => f i
    end.

Section Nota.

Notation onth := nth_error.

Fixpoint T2list {A} (t : T A) : (NEList A) :=
  match t with
    | Op t1 t2 => Napp (T2list t1) (T2list t2)
    | Val i => single i
    end.

Lemma T2list_correct : forall {A} {G : Gop A} {Hassoc : Associative G}
{B} (f : B -> option A) t, evalNE f (T2list t) = evalTree f t.
Proof.
induction t.
- simpl. path_via (someOp (evalNE f (T2list t1))
                  (evalNE f (T2list t2))).
  apply evalNE_app.
  apply ap11;[apply ap|];assumption.
- simpl. reflexivity.
Defined.

Section SortUse.

Context {A} {G : Gop A} {Hsg : IsSemigroup G}.
Context {B} {order_dec : B -> B -> Bool}.

Lemma sort_full : forall (f : B -> option A) t,
    evalNE f (sort order_dec (T2list t)) = evalTree f t.
Proof.
intros.
path_via (evalNE f (T2list t)).
apply sort_correct. assumption.
apply T2list_correct.
Defined.

Lemma sort_inj : forall (f : B -> option A) t1 t2,
 evalNE f (sort order_dec (T2list t1)) = evalNE f (sort order_dec (T2list t2)) ->
  evalTree f t1 = evalTree f t2.
Proof.
intros ? ? ? H. eapply concat;[symmetry;apply sort_full|].
eapply concat;[apply H|]. apply sort_full.
Defined.

End SortUse.

Section Prefix.

Context {A : Type}.

Notation onth := nth_error.

(* prefix stuff should be moved so that it may work for types not in magmas *)
Inductive prefix : relation (list A) := 
  | pref_nil : forall l, prefix nil l
  | pref_cons : forall l l', prefix l l' -> forall x, prefix (x::l) (x::l')
.

Instance prefix_refl : Reflexive prefix.
Proof.
red. intro l;induction l;constructor;auto.
Defined.

Lemma cons_pref : forall x l l', prefix (x::l) l' -> 
(l' = x::(tl l') /\ prefix l (tl l')).
Proof.
assert (H : forall l l', prefix l l' -> forall x l1, l = x::l1 -> 
l' = x::(tl l') /\ prefix l1 (tl l')).
intros ? ? H;induction H.
- intros ? ? H.
  destruct (nil_cons H).
- intros ? ? H0.
  apply cons_inj in H0.
  destruct H0 as [[] []]. simpl. split;auto.
- intros. apply H with (x::l);auto.
Defined.

Global Instance prefix_trans : Transitive prefix.
Proof.
red. intros l1 l2 l3 H H'.
revert H'. revert l3.
induction H.
- constructor.
- intros l3 H'. apply cons_pref in H'. destruct H' as [H0 H1].
  destruct l3;simpl in *. destruct (nil_cons H0).
  apply cons_inj in H0. destruct H0 as [[] _].
  constructor. auto.
Defined.

Lemma app_prefix : forall l l', prefix l (l++l').
Proof.
induction l;intros;constructor;auto.
Defined.

Lemma prefix_app : forall l l', prefix l l' -> exists l0, l' = l++l0.
Proof.
induction 1 as [| ? ? ? IH].
econstructor;reflexivity.
destruct IH. econstructor. simpl; apply ap. apply p. 
Defined.

Lemma prefix_nth : forall l l', prefix l l' ->
 forall i v, onth l i = Some v -> onth l' i = Some v.
Proof.
intros ? ? H;induction H.
- intros ? ? H;intros.
  destruct i;simpl in H;destruct (transport (fun s => match s with
    | None => Unit | _ => Empty end) H tt).
- intros ? ? H'. destruct i. apply H'.
  apply IHprefix. apply H'.
Defined.

Global Instance prefix_antisymm : Relation.Antisymmetric prefix.
Proof.
intros ? ? H;induction H;intros H'.
destruct l;auto.
apply cons_pref in H'. destruct H' as [H _].
destruct (nil_cons H).
apply cons_pref in H'. destruct H' as [_ H'].
simpl in *. apply ap. auto.
Defined.

End Prefix.

Arguments prefix_trans {_ _ _ _} _ _.

Section XFind.

Notation onth := nth_error.

Variable A : Type.

Definition invariant s r i (e : A) := onth r i = Some e /\ prefix s r.

(* Tagging for controlling the search of instances *)
Structure xtagged := XTag {xuntag :> A}.

Definition extend_tag := XTag.
Definition recurse_tag := extend_tag.
Canonical Structure found_tag x := recurse_tag x.

(* Main structure
   s : input sequence
   r : output sequence. If elem_of is in the sequence, then it's equal to s, 
       otherwise it's equal to (elem_of :: s)
   i : output index of elem_of in r *)
Structure xfind (s r : list A) (i : nat) := XFind {
  elem_of :> xtagged; 
  x_nth :> onth r i = @Some A elem_of;
  x_prefix :> prefix s r
}.

Implicit Arguments XFind [].

Canonical Structure found_struct x t := 
  XFind (x :: t) (x :: t) 0 (found_tag x) (idpath) (prefix_refl _).

Lemma recurse_pf {i : nat} (y : A) {s r : list A} (f : xfind s r i) :
        invariant (y :: s) (y :: r) (S i) f.
Proof. red.
simpl. split. apply f.
constructor. apply f.
Defined.

Canonical Structure recurse_struct i y t r (f : xfind t r i) :=
  XFind (y :: t) (y :: r) (S i) (recurse_tag f) f (pref_cons _ _ f _).

Canonical Structure extend_struct x := 
  XFind [] [ x] 0 (extend_tag x) idpath (pref_nil _).

End XFind.

Arguments elem_of {_ _ _ _} _.
Arguments xuntag {_} _.
Arguments xfind {_} _ _ _.

Section Ast.

Context {A : Type} {G : Gop A}.

Notation onth := nth_error.

Structure tagged := Tag { untag :> A }.

Definition ctx := list A.

Inductive valid : ctx -> T nat -> Type := 
  | valid_op : forall c t1, valid c t1 -> forall t2, valid c t2 ->
                valid c (Op t1 t2)
  | valid_val : forall c i v (Hv : onth c i = Some v),
                valid c (Val i).

Arguments valid_op {_ _} _ {_} _.
Arguments valid_val {_ _ _} _.

Lemma valid_prefix : forall c t, valid c t -> forall c', prefix c c' ->
  valid c' t.
Proof.
intros ? ? H;induction H;intros ? H'.
constructor;auto.
econstructor.
eapply prefix_nth. apply H'. apply Hv.
Defined.

Arguments valid_prefix {_ _} _ {_} _.

Lemma valid_prefix_eval : forall c t, valid c t -> 
forall c', prefix c c' ->
 evalTree (onth c) t = evalTree (onth c') t.
Proof.
intros ? ? H;induction H;intros ? H';simpl in *.
apply ap11;[apply ap;apply IHvalid1|apply IHvalid2];auto.
path_via (Some v).
symmetry;eapply prefix_nth. apply H'. assumption.
Defined.

Lemma valid_ext : forall c t, valid c t -> 
  sigT (fun v => evalTree (onth c) t = Some v).
Proof.
intros ? ? H;induction H.
destruct IHvalid1 as [v1 H1].
destruct IHvalid2 as [v2 H2].
exists (gop v1 v2). simpl.
path_via (someOp (Some v1) (Some v2)).
intros;apply ap11;[apply ap|];auto.
simpl. exists v;assumption.
Defined.

Arguments valid_ext {_ _} _.

Lemma ext_valid : forall c t v, evalTree (onth c) t = Some v -> valid c t.
Proof.
induction t;intros ? H.
simpl in H. destruct (evalTree (onth c) t1), (evalTree (onth c) t2);
 try solve [destruct
(transport (fun s => match s with | None => Unit | _ => Empty end) H tt)].
constructor;eauto.
eapply valid_val. apply H.
Defined.

Lemma prefix_eval : forall c c', prefix c c' -> forall t (v : A), 
evalTree (onth c) t = Some v -> evalTree (onth c') t = Some v.
Proof.
intros. path_via (evalTree (onth c) t).
symmetry. apply valid_prefix_eval.
apply ext_valid with v. assumption.
assumption.
Defined.

Structure ast (c c' : ctx) (t : T nat) := Ast {
val :> tagged;
ast_prefix :> prefix c c';
ast_pr :> evalTree (onth c') t = @Some A val
}.

Arguments ast_prefix {_ _ _} _.
Arguments val {_ _ _} _.


Definition var_tag t := Tag t.
Canonical Structure op_tag t := var_tag t.

Lemma ast_pr_op : forall {i j k : ctx} {t1 t2 : T nat}
 (a1 : ast i j t1) (a2 : ast j k t2),
        evalTree (onth k) (Op t1 t2) = @Some A (op_tag (G a1 a2)).
Proof.
intros ? ? ? ? ? ? ?.
change (someOp (evalTree (onth k) t1) (evalTree (onth k) t2) =
   someOp (@Some A a1) (@Some A a2)).
apply ap11;[apply ap|].
eapply prefix_eval. apply a2. apply a1.
apply a2.
Defined.

Canonical Structure ast_op (i j k : ctx) (t1 t2 : T nat)
 (a1 : ast i j t1) (a2 : ast j k t2) :=
  Ast i k (Op t1 t2) (op_tag (G a1 a2)) (prefix_trans a1 a2)
   (ast_pr_op a1 a2).

Canonical Structure ast_var (i j : ctx) (n : nat) (f : xfind i j n) :=
  Ast i j (Val n) (var_tag (xuntag (elem_of f))) f f. 

Lemma untag_injective : forall x y, untag x = untag y -> x=y.
Proof.
intros. destruct x,y.
apply ap;assumption.
Defined.

Context {Hsg : IsSemigroup G}.

Definition someRel {T T' : Type} (R : T -> T' -> Type)
 : option T -> option T' -> Type := fun x y => match x,y with
    | Some a, Some b => R a b
    | _, _ => Empty
    end.

Lemma some_injective : forall {T T' : Type} (R : T -> T' -> Type)
 x y, someRel R (Some x) (Some y) -> R x y.
Proof.
intros ? ? ? ? ? H.
apply H.
Defined.

Lemma ast_use : forall (R : relation A) {i j : ctx} {t1 t2 : T nat}
 (f1 : ast [] i t1) (f2 : ast i j t2), 
  someRel R (evalNE (onth j) (sort nat_order_dec (T2list t1)))
            (evalNE (onth j) (sort nat_order_dec (T2list t2))) ->
  R (untag (val f1)) (untag (val f2)).
Proof.
intros ? ? ? ? ? ? ? H.
apply some_injective.
pattern (Some (untag (val f1)));eapply transport;[|eapply transport;[|apply H]];
(eapply concat;[apply sort_full|]);[eapply prefix_eval;[apply f2|apply f1]|apply f2].
Defined.

End Ast.

End Nota.

Ltac ssrapply l :=
first
[refine l
|refine (l _)
|refine (l _ _)
|refine (l _ _ _)
|refine (l _ _ _ _)
|refine (l _ _ _ _ _)
|refine (l _ _ _ _ _ _)
|refine (l _ _ _ _ _ _ _)
|refine (l _ _ _ _ _ _ _ _)
].

End BinOpTree.

Module Distributive.
Export BinOpTree.
Export Ring.
Import ListNotations.

Inductive T2 : Type := 
  | Plus : T2 -> T2 -> T2
  | Mult : T2 -> T2 -> T2
  | Val2 : nat -> T2
.

Definition somePlus {A} {G : Symbols.Plus A} : Symbols.Plus (option A) := someOp.
Definition someMult {A} {G : Symbols.Mult A} : Symbols.Mult (option A) := someOp.

Fixpoint evalT2 {A} {G : Prering A} (f : _ -> option A) (t : T2) : option A :=
match t with
  | Plus x y => somePlus (evalT2 f x) (evalT2 f y)
  | Mult x y => someMult (evalT2 f x) (evalT2 f y)
  | Val2 i => f i
  end.

Notation Flat2 := (T (NEList nat)).

Notation FPlus := (@Op (NEList nat)).
Notation ValL  := (@Val (NEList nat)).

Definition evalFlat2 {A} {G : Prering A} (f : nat -> option A) (t : Flat2)
 : option A := @evalTree A (+) _
          (fun l => @evalNE _ (°) _ f l) t.

(* eval (distribute t1 t2) = (eval t1) * (eval t2) *)
Fixpoint distribute (t1 : Flat2) : Flat2 -> Flat2 := fix f (t2 : Flat2) :=
match t1, t2 with
  | Op x y, Op x' y' => FPlus (f x') (f y')
  | Op x y, Val l' => FPlus (distribute x (ValL l')) (distribute y (ValL l'))
  | Val l', Op x y => FPlus (f x) (f y)
  | Val l1, Val l2 => ValL (Napp l1 l2)
  end.

Fixpoint flatten (t : T2) : Flat2 := match t with
  | Plus x y => FPlus (flatten x) (flatten y)
  | Mult x y => distribute (flatten x) (flatten y)
  | Val2 i => ValL (single i)
  end.

Fixpoint Flat2_order_in (t : Flat2) : Flat2 := match t with
  | Op x y => Op (Flat2_order_in x) (Flat2_order_in y)
  | Val l => Val (sort nat_order_dec l)
  end.

Section Mag2.

Notation onth := nth_error.

Context {A} {G : Prering A}.
Context {Hadd : @IsSemigroup A (+)} {Hmult : @IsSemigroup A (°)}
 {Hdistrib : Distributes G}.

Lemma some_distrib_right : forall a b c : option A, 
someMult (somePlus b c) a = somePlus (someMult b a) (someMult c a).
Proof.
destruct a,b,c;try reflexivity.
simpl. apply ap. apply Hdistrib.
Defined.

Lemma some_distrib_left :  forall a b c : option A, 
someMult a (somePlus b c) = somePlus (someMult a b) (someMult a c).
Proof.
destruct a,b,c;try reflexivity.
simpl. apply ap. apply Hdistrib.
Defined.

Lemma distribute_ok : forall (f : _ -> option A) t1 t2,
evalFlat2 f (distribute t1 t2) = someMult (evalFlat2 f t1) (evalFlat2 f t2).
Proof.
assert (Hleft : forall (f : _ -> option A) l x,
 evalFlat2 f (distribute x (ValL l)) = 
someMult (evalFlat2 f x) (evalFlat2 f (ValL l))).
intros f l. simpl.
assert (X:(sigT (fun v => evalFlat2 f (ValL l) = Some v))
   + (evalFlat2 f (ValL l) = None)).
destruct (evalFlat2 f (ValL l));eauto.
destruct X as [[g Hl] | Hl];pattern (evalFlat2 f (ValL l));
apply (transport _ (inverse Hl)).
- induction x.
  simpl. path_via (someMult (somePlus (evalFlat2 f x1) (evalFlat2 f x2))
    (Some g)).
  destruct (evalFlat2 f x1);[destruct (evalFlat2 f x2)|].
  simpl. eapply concat.
  apply (@ap11 _ _ (somePlus (evalFlat2 f (distribute x1 (ValL l)))))
  ;[apply ap;apply IHx1|apply IHx2].
  simpl;apply ap;symmetry;apply Hdistrib.
  simpl. simpl in IHx2. path_via (somePlus (evalFlat2 f (distribute x1 (ValL l)))
    (evalFlat2 f (distribute x2 (ValL l)))).
  pattern (evalFlat2 f (distribute x2 (ValL l)));
  apply (transport _ (inverse IHx2)).
  destruct (evalFlat2 f (distribute x1 (ValL l)));reflexivity.
  simpl. simpl in IHx1. path_via (somePlus (evalFlat2 f (distribute x1 (ValL l)))
    (evalFlat2 f (distribute x2 (ValL l)))).
  pattern (evalFlat2 f (distribute x1 (ValL l)));
  apply (transport _ (inverse IHx1)). simpl. reflexivity.
  simpl. unfold someMult. eapply concat;[apply @evalNE_app|]. apply _.
  apply ap. apply Hl.

- induction x.
  simpl. path_via (somePlus (evalFlat2 f (distribute x1 (ValL l)))
    (evalFlat2 f (distribute x2 (ValL l)))).
  path_via (someMult (somePlus (evalFlat2 f x1) (evalFlat2 f x2)) None).
  destruct (evalFlat2 f x1), (evalFlat2 f x2);
  simpl in *; (path_via (@somePlus A _ None None);
  apply ap11;[apply ap|];assumption).
  simpl.
  eapply concat. apply (@evalNE_app A (°)). apply _.
  apply ap. assumption.

(* Hleft done *)
- intros l t1 t2;revert t1.
  induction t2;auto.
  induction t1.
  path_via (somePlus (evalFlat2 l (distribute (FPlus t1_1 t1_2) t2_1))
    (evalFlat2 l (distribute (FPlus t1_1 t1_2) t2_2))).
  pattern (evalFlat2 l (distribute (FPlus t1_1 t1_2) t2_2)).
  eapply transport. symmetry;apply IHt2_2.
  pattern (evalFlat2 l (distribute (FPlus t1_1 t1_2) t2_1)).
  eapply transport. symmetry;apply IHt2_1.
  path_via (somePlus (someMult (somePlus (evalFlat2 l t1_1) (evalFlat2 l t1_2))
     (evalFlat2 l t2_1))
  (someMult (somePlus (evalFlat2 l t1_1) (evalFlat2 l t1_2)) (evalFlat2 l t2_2))).
  path_via (someMult (somePlus (evalFlat2 l t1_1) (evalFlat2 l t1_2))
    (somePlus (evalFlat2 l t2_1) (evalFlat2 l t2_2))).
  repeat first [rewrite some_distrib_left | rewrite some_distrib_right].
  reflexivity.

  path_via (somePlus 
    (someMult (evalFlat2 l (ValL a)) (evalFlat2 l t2_1))
    (someMult (evalFlat2 l (ValL a)) (evalFlat2 l t2_2))).
  path_via (somePlus (evalFlat2 l (distribute (ValL a) t2_1))
    (evalFlat2 l (distribute (ValL a) t2_2))).
  apply ap11;[apply ap|]; auto.
  symmetry. apply some_distrib_left.
Defined.

Lemma flatten_ok : forall (l : _ -> option A) t,
 evalFlat2 l (flatten t) = evalT2 l t.
Proof.
induction t.
simpl. path_via (somePlus (evalFlat2 l (flatten t1)) (evalFlat2 l (flatten t2))).
 apply ap11;[apply ap|];assumption.
simpl. eapply concat;[apply distribute_ok|].
apply ap11;[apply ap|];assumption.
reflexivity.
Defined.

Lemma order_in_ok : forall (f : _ -> option A) t,
 evalFlat2 f (Flat2_order_in t) = evalFlat2 f t.
Proof.
induction t.
path_via (somePlus (evalFlat2 f (Flat2_order_in t1))
 (evalFlat2 f (Flat2_order_in t2))).
path_via (somePlus (evalFlat2 f t1) (evalFlat2 f t2)).
apply ap11;[apply ap|];assumption.
unfold evalFlat2;simpl. apply (@sort_correct _ _ A (°)). exact _.
Defined.

End Mag2.

Section Ast2.

Context {A} {G : Prering A}.

(*note: cannot reuse BinOpTree.tagged because its canonical projections would override our new ones *)
Structure tagged := Tag { untag :> A }.

Notation onth := nth_error.

Lemma prefix_eval2 : forall c c', prefix c c' -> forall (t : T2) (v : A), 
evalT2 (onth c) t = Some v -> evalT2 (onth c') t = Some v.
Proof.
induction t;intros.
- simpl in *.
  destruct (evalT2 (onth c) t1) as [v1 |];
  [destruct (evalT2 (onth c) t2) as [v2 |]|].
  eapply concat;[|apply X0]. apply ap11;[apply ap|];auto.
  simpl in X0. destruct (transport (fun s => match s with
    | None => Unit | _ => Empty end) X0 tt).
  simpl in X0. destruct (transport (fun s => match s with
    | None => Unit | _ => Empty end) X0 tt).
- simpl in *.
  destruct (evalT2 (onth c) t1) as [v1 |];
  [destruct (evalT2 (onth c) t2) as [v2 |]|].
  eapply concat;[|apply X0]. apply ap11;[apply ap|];auto.
  simpl in X0. destruct (transport (fun s => match s with
    | None => Unit | _ => Empty end) X0 tt).
  simpl in X0. destruct (transport (fun s => match s with
    | None => Unit | _ => Empty end) X0 tt).
- simpl in *. eapply prefix_nth;eauto.
Defined.

Structure ast2 (c c' : ctx) (t : T2) := Ast2 {
val2 :> tagged;
ast2_prefix :> prefix c c';
ast2_pr :> evalT2 (onth c') t = Some (untag val2)
}.

Arguments ast2_prefix {_ _ _} _.
Arguments val2 {_ _ _} _.


Definition var_tag (t:A) := Tag t.
Definition mult_tag (t:A) := var_tag t.
Canonical Structure plus_tag (t:A) := mult_tag t.

Lemma ast2_pr_plus : forall {i j k : ctx} {t1 t2 : T2}
 (a1 : ast2 i j t1) (a2 : ast2 j k t2),
        evalT2 (onth k) (Plus t1 t2)
        = Some (untag (plus_tag (untag a1 + untag a2))).
Proof.
intros ? ? ? ? ? ? ?.
change (somePlus (evalT2 (onth k) t1) (evalT2 (onth k) t2) =
   somePlus (Some (untag a1)) (Some (untag a2))).
apply ap11;[apply ap|].
apply prefix_eval2 with j. apply a2. apply a1.
apply a2.
Defined.

Canonical Structure ast2_plus (i j k : ctx) (t1 t2 : T2)
 (a1 : ast2 i j t1) (a2 : ast2 j k t2) :=
  Ast2 i k (Plus t1 t2) (plus_tag ((untag a1) + (untag a2)))
   (prefix_trans _ _ _ a1 a2) (ast2_pr_plus a1 a2).

Lemma ast2_pr_mult : forall {i j k : ctx} {t1 t2 : T2}
 (a1 : ast2 i j t1) (a2 : ast2 j k t2),
        evalT2 (onth k) (Mult t1 t2)
        = Some (untag (mult_tag ((untag a1) ° (untag a2)))).
Proof.
intros ? ? ? ? ? ? ?.
change (someMult (evalT2 (onth k) t1) (evalT2 (onth k) t2) =
   someMult (Some (untag a1)) (Some (untag a2))).
apply ap11;[apply ap|].
apply prefix_eval2 with j. apply a2. apply a1.
apply a2.
Defined.

Canonical Structure ast2_mult (i j k : ctx) (t1 t2 : T2)
 (a1 : ast2 i j t1) (a2 : ast2 j k t2) :=
  Ast2 i k (Mult t1 t2) (mult_tag ((untag a1) ° (untag a2)))
   (prefix_trans _ _ _ a1 a2) (ast2_pr_mult a1 a2).

Canonical Structure ast2_var (i j : ctx) (n : nat) (f : xfind _ i j n) :=
  Ast2 i j (Val2 n) (var_tag (xuntag _ (elem_of _ _ _ _ f))) f f. 

Section Minimal.

Context {Hadd : @IsSemigroup A (+)} {Hmult : @IsSemigroup A (°)}
 {Hdistrib : Distributes G}.

Lemma ast2_use : forall R {i j : ctx} {t1 t2 : T2}
 (f1 : ast2 [] i t1) (f2 : ast2 i j t2), 
  someRel R (evalFlat2 (onth j) (Flat2_order_in (flatten t1)))
            (evalFlat2 (onth j) (Flat2_order_in (flatten t2))) ->
  R (untag (val2 f1)) (untag (val2 f2)).
Proof.
intros ? ? ? ? ? ? ? H.
apply some_injective.
pattern (Some (untag (val2 f1)));eapply transport;[|eapply transport;[|apply H]];
(eapply concat;[ apply order_in_ok|
eapply concat;[ apply flatten_ok|]]).
eapply prefix_eval2. apply f2. apply f1.
apply f2.
Defined.

End Minimal.

Lemma ast2_semiring : forall {Hsemir : IsSemiring G},
forall R {i j : ctx} {t1 t2 : T2}
 (f1 : ast2 [] i t1) (f2 : ast2 i j t2), 
  someRel R (evalFlat2 (onth j) (Flat2_order_in (flatten t1)))
            (evalFlat2 (onth j) (Flat2_order_in (flatten t2))) ->
  R (untag (val2 f1)) (untag (val2 f2)).
Proof.
intro.
apply @ast2_use;apply _.
Defined.

Definition full_simplify (t : T2) := 
  sort NEList_nat_order_dec (T2list (Flat2_order_in (flatten t))).

Lemma ast2_full_semiring : forall {Hsemir : IsSemiring G},
forall R {i j : ctx} {t1 t2 : T2}
 (f1 : ast2 [] i t1) (f2 : ast2 i j t2), 
  someRel R (@evalNE A (+) _ (fun l => @evalNE A (°) _ (onth j) l)
               (full_simplify t1))
            (@evalNE A (+) _ (fun l => @evalNE A (°) _ (onth j) l)
               (full_simplify t2))
  -> R (untag (val2 f1)) (untag (val2 f2)).
Proof.
intros ? ? ? ? ? ? ? ? H.
apply (ast2_semiring R).
unfold evalFlat2.
eapply transport;[|pattern (@evalTree A (@plus A G) (NEList nat)
     (fun l : NEList nat => @evalNE A (@mult A G) nat (onth j) l)
     (Flat2_order_in (flatten t1))); eapply transport;[|apply H]];
(unfold full_simplify;
eapply concat;[ apply sort_correct; apply _|
apply T2list_correct]).
Defined.

End Ast2.

Lemma test2 : forall A (G : Prering A) {Hsemir : IsSemiring G},
forall a b c : A, a°(b+c) = a°c + a°b.
Proof.
intros.
ssrapply (@ast2_full_semiring A (+ °) Hsemir paths).
reflexivity.
Fail idtac.
Abort.

End Distributive.





