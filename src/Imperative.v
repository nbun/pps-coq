Require Import EqNat Lists.List.
Import ListNotations.

Definition Ref := nat.

Inductive Ty : Type :=
  | TInt  : Ty
  | TBool : Ty.

Inductive Val : Type :=
  | VInt  : nat  -> Val
  | VBool : bool -> Val
  | Undefined : Val.

Definition Name := nat.

Definition Env := list (Name * (Ref * Ty)).

Definition Memory := list (Ref * Val).

Fixpoint envLookup (E : Env) (n : Name) : option (Ref * Ty) :=
  match E with
  | []           => None
  | (k, v) :: es => if (beq_nat n k) then Some v else envLookup es n
  end.

Definition envAdd (E : Env) (n : Name) (v : (Ref * Ty)) : Env :=
  (n, v) :: E.

Fixpoint memLookup (M : Memory) (r : Ref) : Val :=
  match M with
  | [] => Undefined
  | (k, v) :: ms => if (beq_nat r k) then v else memLookup ms r
  end.
 
Definition memAdd (M : Memory) (r : Ref) (v : Val) : Memory :=
  (r, v) :: M.

Inductive Ops : Type :=
  | plus : Ops
  | mult : Ops.

Inductive Exp : Type :=
  | Number : Val  -> Exp
  | Var    : Name -> Exp
  | Op    : Exp   -> Ops -> Exp -> Exp.

Reserved Notation "EM '|-R' x ':::' v" (at level 40).
Inductive evalR : (Env * Memory) -> Exp -> Val -> Prop :=
  | EvVarR  : forall E M x l T v,
               envLookup E x = Some (l,T) ->
               memLookup M l = v ->
               (E,M) |-R (Var x) ::: v
              
  | EvNumR  : forall E M n, (E,M) |-R (Number n) ::: n
  
  | EvPlusR : forall E M e1 e2 v1 v2 v,
               (E,M) |-R e1 ::: (VInt v1) ->
               (E,M) |-R e2 ::: (VInt v2) -> 
               v = VInt (v1 + v2) ->
               (E,M) |-R (Op e1 plus e2) ::: v
               
  | EvMultR : forall E M e1 e2 v1 v2 v,
               (E,M) |-R e1 ::: (VInt v1) ->
               (E,M) |-R e2 ::: (VInt v2) -> 
               v = VInt (v1 * v2) ->
               (E,M) |-R (Op e1 mult e2) ::: v
               
  where "EM '|-R' x ':::' v" := (evalR EM x v).

Reserved Notation "EM '|-L' x ':::' v" (at level 40).
Inductive evalL : (Env * Memory) -> Exp -> Ref -> Prop :=
  | EvVarL : forall E M x l T,
              envLookup E x = Some (l,T) ->
              (E,M) |-L (Var x) ::: l

  where "EM '|-L' x ':::' v" := (evalL EM x v).
