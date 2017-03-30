Inductive AExp : Type :=
| ANum  : nat  -> AExp
| AVar  : nat -> AExp
| APlus  : AExp -> AExp -> AExp
| AMinus : AExp -> AExp -> AExp
| AMult  : AExp -> AExp -> AExp
(* >>>>>>>>>>>>>>>>>>>>> *)
| ALet   : nat  -> AExp -> AExp -> AExp.
(* <<<<<<<<<<<<<<<<<<<<< *)

Inductive BExp : Type :=
| BTrue  : BExp
| BFalse : BExp
| BLess  : AExp -> AExp -> BExp.

Notation "e1 :<: e2" := (BLess e1 e2) (at level 40, left associativity).
Notation "e1 :+: e2" := (APlus e1 e2) (at level 40, left associativity).
Notation "e1 :-: e2" := (AMinus e1 e2) (at level 40, left associativity).
Notation "e1 :*: e2" := (AMult e1 e2) (at level 40, left associativity).
(* >>>>>>>>>>>>>>>>>>>>> *)
Notation "'Let' x :=: v 'In' y" := (ALet x v y) (at level 50).
(* <<<<<<<<<<<<<<<<<<<<< *)
