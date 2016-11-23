(* Chapter 2.2.3 *)

Require Import EqNat Lists.List.
Import ListNotations.

Definition ID := nat.

Definition Val := nat.

Definition Context := list (ID * Val).

Fixpoint lookup (Sigma : Context) (i : ID) : option Val :=
  match Sigma with
  | []          => None
  | (k,v) :: ps => if (beq_nat i k) then Some v
                                    else lookup ps i
  end.

Definition add (Sigma : Context) (i : ID) (v : Val) : Context :=
  (i, v) :: Sigma.

Inductive Ops : Type :=
  | plus : Ops
  | mult : Ops.

Inductive Exp : Type :=
  | Number : Val -> Exp
  | Var    : ID  -> Exp
  | Op     : Exp -> Ops -> Exp -> Exp
  | Let    : ID  -> Exp -> Exp -> Exp.

Reserved Notation "Sigma '|-' e ':::' v" (at level 40).
Inductive eval (Sigma : Context) : Exp -> Val -> Prop :=
  | EvNum  : forall n, Sigma |- (Number n) ::: n
  
  | EvVar  : forall x v,
               lookup Sigma x = Some v ->
               Sigma |- (Var x) ::: v
               
  | EvPlus : forall e1 e2 v1 v2 v,
               Sigma |- e1 ::: v1 ->
               Sigma |- e2 ::: v2 ->
               v = v1 + v2 ->
               Sigma |- (Op e1 plus e2) ::: v
               
  | EvMult : forall e1 e2 v1 v2 v,
               Sigma |- e1 ::: v1 ->
               Sigma |- e2 ::: v2 ->
               v = v1 * v2 ->
               Sigma |- (Op e1 mult e2) ::: v
  
  | EvLet  : forall Sigma' e1 e2 v1 v2 x,
               Sigma  |- e1 ::: v1 ->
               Sigma' = add Sigma x v1 ->
               Sigma' |- e2 ::: v2 -> 
               Sigma  |- (Let x e1 e2) ::: v2
  where "Sigma '|-' e ':::' v" := (eval Sigma e v).

Example e : [] |- (Op (Op (Number 2) mult (Number 3)) plus (Number 3)) ::: 9.
Proof. eapply EvPlus.
  - eapply EvMult.
    * apply EvNum.
    * apply EvNum.
    * reflexivity.
  - apply EvNum.
  - reflexivity.
Qed.

Example e2 : [(1, 6)] |- (Let 2 (Op (Number 2) plus (Number 2))
                                (Op (Var 2)    mult (Var 2))) ::: 16.
Proof. eapply EvLet.
  - eapply EvPlus.
    * apply EvNum.
    * apply EvNum.
    * reflexivity.
  - reflexivity.
  - eapply EvMult.
    * apply EvVar. reflexivity.
    * apply EvVar. reflexivity.
    * reflexivity.
Qed.
