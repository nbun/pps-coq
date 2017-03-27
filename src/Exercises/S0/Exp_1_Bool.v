Set Implicit Arguments.

Inductive AExp : Type :=
| ANum   : nat    -> AExp
| APlus  : AExp -> AExp -> AExp
| AMinus : AExp -> AExp -> AExp
| AMult  : AExp -> AExp -> AExp.

Inductive BExp : Type :=
| BTrue  : BExp
| BFalse : BExp
| BLess  : AExp -> AExp -> BExp.

Notation "e1 :<: e2" := (BLess e1 e2) (at level 40, left associativity).
Notation "e1 :+: e2" := (APlus e1 e2) (at level 40, left associativity).
Notation "e1 :-: e2" := (AMinus e1 e2) (at level 40, left associativity).
Notation "e1 :*: e2" := (AMult e1 e2) (at level 40, left associativity).

Fixpoint aeval (e : AExp) : nat :=
  match e with
  | ANum n       => n
  | APlus e1 e2  => aeval e1 + aeval e2
  | AMinus e1 e2 => aeval e1 - aeval e2
  | AMult e1 e2  => aeval e1 * aeval e2
  end.

Fixpoint beval (e : BExp) : bool :=
  match e with
  | BTrue       => true
  | BFalse      => false
  | BLess e1 e2 => Nat.leb (aeval e1) (aeval e2)
  end.
