Require Import Nat Lists.List.
Require Import PPS.Env.

Set Implicit Arguments.

Section ImpModell.

  Inductive Val : Type :=
  | VInt      : nat -> Val
  | Undefined : Val.

  Definition Ref := nat.
  Definition Name := nat.

  Inductive Ty : Type :=
  | Int    : Ty.

  Definition Env := EnvironmentL Name Ref.

  Definition Memory := EnvironmentT Ref Val.

  Reserved Notation "E '|-l' val" (at level 80).

  Notation "E ; x" := (union Name Ref E (cons x nil)) (at level 40).

  Section EnvRelation.
    
    Inductive Lookup : Env -> (Name * Ref) -> Prop :=
    | LAxiom : forall E x beta,
        E; (x, beta) |-l (x, beta)
    | LRule : forall E x y beta gamma,
        E |-l (x,beta) ->
        E; (y, gamma) |-l (x, beta)
    where "E '|-l' val" := (Lookup E val).
      
  End EnvRelation.
  Notation "E '|-l' val" := (Lookup E val).

  Section Exp.

    Inductive ArithExp : Type :=
    | Num : nat -> ArithExp
    | Var : Name -> ArithExp
    | Op : ArithExp -> Ops -> ArithExp -> ArithExp
    with Ops : Type :=
         | plus : Ops
         | mult : Ops.
    
  End Exp.

  Reserved Notation "EM '|-R' e ⇓ v" (at level 80).
  Section EvalR.

    Inductive evalR : (Env * Memory) -> ArithExp -> nat -> Prop :=
    | EvVarR  : forall E M x l val,
        E |-l (x, l) ->
        M l = VInt val ->
        (E,M) |-R (Var x) ⇓ val
    | EvNumR  : forall E M n, (E,M) |-R Num n ⇓ n
                                  
    | EvPlusR : forall E M e1 e2 v1 v2 v,
        (E,M) |-R e1 ⇓ v1 ->
        (E,M) |-R e2 ⇓ v2 ->
        v = v1 + v2 ->
        (E,M) |-R Op e1 plus e2 ⇓ v
                               
    | EvMultR : forall E M e1 e2 v1 v2 v,
        (E,M) |-R e1 ⇓ v1 ->
        (E,M) |-R e2 ⇓ v2 ->
        v = v1 * v2 ->
        (E,M) |-R Op e1 mult e2 ⇓ v
               
    where "EM '|-R' e ⇓ v" := (evalR EM e v).

  End EvalR.
  Notation "EM '|-R' e ⇓ v" := (evalR EM e v).

  Section Stm.

    Inductive Stm : Type :=
    | Ass    : Name -> ArithExp -> Stm
    | Decl   : Name -> Stm
    | Seq    : Stm -> Stm -> Stm.

    Reserved Notation "'<' E '|' M '>' alpha '<' E' '|' M' '>'"
             (at level 40, E at level 39, M at level 39, M' at level 40,
              E' at level 39, alpha at level 39).
    Notation "M '[' var ↦ val ']'" := (updateTMap eqb M var val)
                                    (at level 40, right associativity).

    Inductive IsFree : Name -> Memory -> Prop :=
    | isFree : forall x M,
        M x = Undefined ->
        IsFree x M.

    Inductive eval : Env * Memory -> Stm -> Env * Memory -> Prop :=
    | EvDecl : forall E M l n,
        IsFree l M ->
        < E | M > Decl n < E; (n, l) | M [l ↦ VInt 0] >

    | EvAss   : forall E M n e l v,
        IsFree l M ->
        (E,M) |-R e ⇓ v ->
        < E | M > Ass n e < E | M [n ↦ VInt v] >

    | EvSeq   : forall E M E' M' E'' M'' S1 S2,
        < E | M > S1 < E' | M' > ->
        < E' | M' > S2 < E'' | M'' > ->
        < E | M > Seq S1 S2 < E'' | M'' >    
    where "'<' E '|' M '>' alpha '<' E' '|' M' '>'" := (eval (E,M) alpha (E',M')).
    
  End Stm.

End ImpModell.