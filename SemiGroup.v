Require Export HoTT.Basics.Overture.
Require Export HoTTMath.Notations.

Definition law A := A -> A -> A.

Class SgOp A := sgop : law A.

Infix "++" := sgop.

Class Associative A {op : SgOp A} := associative : forall x y z, (x ++ y) ++ z = x ++ y ++ z.

Class Commutative A {op : SgOp A} := commutative : forall x y, x ++ y = y ++ x.

Class SemiGroup A {op : SgOp A} :=
  { sg_assoc :> Associative A }.
