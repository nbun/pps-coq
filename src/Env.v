Require Import PPS.Map Lists.List.
Import ListNotations.

Variable ID Val : Type.
Variable eqID : ID -> ID -> bool.
Notation "i '==' j" := (eqID i j) (at level 80, right associativity).

Definition EnvironmentP := partialMap ID Val.
Definition EnvironmentT := totalMap ID Val.
Definition EnvironmentL := list (ID * Val).

Fixpoint lookup (Sigma : EnvironmentL) (i : ID) : option Val :=
  match Sigma with
  | []          => None
  | (k,v) :: ps => if (k == i) then Some v
                  else lookup ps i
  end.

Fixpoint update (Sigma : EnvironmentL) (i : ID) (v' : Val) : EnvironmentL :=
  match Sigma with
  | []          => [(i,v')]
  | (k,v) :: ps => if (k == i) then (k,v') :: ps
                  else (k,v) :: update ps i v'
  end.