(** HoTT-Algebra reserved notations *)
(** This file sets levels and associativity for new notations (and some old ones).
  Notations are ordered by decreasing level. *)

Global Generalizable All Variables.

(** Notations for propositional connectives *)

Reserved Notation "x -> y" (at level 99, right associativity, y at level 200).

Reserved Notation "x <-> y" (at level 95, no associativity).

Reserved Notation "x \/ y" (at level 85, right associativity).

Reserved Notation "x /\ y" (at level 80, right associativity).

Reserved Notation "~ x" (at level 75, right associativity).

(** Notations for equality and inequalities *)

Reserved Notation "x = y  :>  T"
(at level 70, y at next level, no associativity).
Reserved Notation "x = y" (at level 70, no associativity).
Reserved Notation "x = y = z"
(at level 70, no associativity, y at next level).

Reserved Notation "x <> y  :>  T"
(at level 70, y at next level, no associativity).
Reserved Notation "x <> y" (at level 70, no associativity).

Reserved Notation "x <= y" (at level 70, no associativity).
Reserved Notation "x < y" (at level 70, no associativity).
Reserved Notation "x >= y" (at level 70, no associativity).
Reserved Notation "x > y" (at level 70, no associativity).

Reserved Notation "x <= y <= z" (at level 70, y at next level).
Reserved Notation "x <= y < z" (at level 70, y at next level).
Reserved Notation "x < y < z" (at level 70, y at next level).
Reserved Notation "x < y <= z" (at level 70, y at next level).

(** Arithmetical notations (also used for type constructors) *)

Reserved Notation "x + y" (at level 50, left associativity).
Reserved Notation "x - y" (at level 50, left associativity).

Reserved Notation "x * y" (at level 40, left associativity).
Reserved Notation "x / y" (at level 40, left associativity).

Reserved Notation "- x" (at level 35, right associativity).
Reserved Notation "/ x" (at level 35, right associativity).

Reserved Notation "x ^ y" (at level 30, right associativity).
