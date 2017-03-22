Require Import ImperativeOp.

Fixpoint maxT (T1 T2 : Ty) : Ty :=
  match T1, T2 with
  | Int,    Int    => Int
  | Int,    Float  => Float
  | Float,  Int    => Float
  | Float,  Float  => Float
  | _,      _      => Double
  end.

Reserved Notation "E '|-T' x ':::' t" (at level 40).
Inductive evalT : Env -> Exp -> Ty -> Prop :=
  | EvTInt  : forall E i, E |-T Num (VInt i)  ::: Int
  | EvTBool : forall E b, E |-T Num (VBool b) ::: Bool
  | EvTVar  : forall E x T l,
                envLookup E x = Some (VarType l T) ->
                E |-T (Var x) ::: T
 
  | EvTOp   : forall E e1 e2 T op,
                E |-T e1 ::: T ->
                E |-T e2 ::: T ->
                E |-T (Op e1 op e2) ::: T

  | EvTOpCast : forall E e1 e2 T1 T2 op,
                E |-T e1 ::: T1 ->
                E |-T e2 ::: T2 ->
                E |-T (Op e1 op e2) ::: (maxT T1 T2)

  where "E '|-T' x ':::' t" := (evalT E x t).

(* c? *)