Require Import PPS.Env.

Set Implicit Arguments.

Inductive AExp : Type :=
| AVar   : nat    -> AExp
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

Definition Env := listMap nat nat.

Fixpoint aeval (e : AExp) (Sigma : Env) : option nat :=
  match e with
  | ANum n       => Some n
  | AVar ident   => lookup Nat.eqb Sigma ident
  | APlus e1 e2  =>
    match aeval e1 Sigma, aeval e2 Sigma with
    | Some v1, Some v2 => Some (v1 + v2)
    | _, _ => None
    end
  | AMinus e1 e2 =>
    match aeval e1 Sigma, aeval e2 Sigma with
    | Some v1, Some v2 => Some (v1 - v2)
    | _, _ => None
    end
  | AMult e1 e2  =>
    match aeval e1 Sigma, aeval e2 Sigma with
    | Some v1, Some v2 => Some (v1 * v2)
    | _, _ => None
    end
  end.

Fixpoint beval (e : BExp) (Sigma : Env) : option bool :=
  match e with
  | BTrue       => Some true
  | BFalse      => Some false
  | BLess e1 e2 =>
    match aeval e1 Sigma, aeval e2 Sigma with
    | Some v1, Some v2 => Some (Nat.leb v1 v2)
    | _, _ => None
    end
  end.
