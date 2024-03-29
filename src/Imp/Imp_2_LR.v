Require Import Nat.
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

  Definition Env := listMap Name Ref.

  Definition Memory := totalMap Ref Val.

  Reserved Notation "E '|-l' val" (at level 80).

  Notation "E ; x" := (union (cons x nil) E) (at level 40).

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
    | Plus : ArithExp -> ArithExp -> ArithExp
    | Mult : ArithExp -> ArithExp -> ArithExp.
    
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
        (E,M) |-R Plus e1 e2 ⇓ v
                               
    | EvMultR : forall E M e1 e2 v1 v2 v,
        (E,M) |-R e1 ⇓ v1 ->
        (E,M) |-R e2 ⇓ v2 ->
        v = v1 * v2 ->
        (E,M) |-R Mult e1 e2 ⇓ v
               
    where "EM '|-R' e ⇓ v" := (evalR EM e v).

  End EvalR.
  Notation "EM '|-R' e ⇓ v" := (evalR EM e v).

  (* >>>>>>>>>>>>>>>>>>>>> *)
  Reserved Notation "EM '|-L' e ⇓ v" (at level 80).
  Section EvalL.
    
    Inductive evalL : (Env * Memory) -> ArithExp -> Ref -> Prop :=
    | EvVarL : forall E M x l,
        E |-l (x, l) ->
        (E,M) |-L (Var x) ⇓ l
  where "EM '|-L' e ⇓ v" := (evalL EM e v).

  End EvalL.
  Notation "EM '|-L' e ⇓ v" := (evalL EM e v).
  (* <<<<<<<<<<<<<<<<<<<<< *)

  Section Stm.

    Inductive Stm : Type :=
    | Ass    : ArithExp -> ArithExp -> Stm
    | Decl   : Name -> Stm
    | Seq    : Stm -> Stm -> Stm.

    Reserved Notation "'<' E '|' M '>' alpha '<' E' '|' M' '>'"
             (at level 40, E at level 39, M at level 39, M' at level 40,
              E' at level 39, alpha at level 39).
    Notation "M '[' var ↦ val ']'" := (updateTMap eqb M var val)
                                    (at level 40, right associativity).

    Inductive IsFree : Ref -> Memory -> Prop :=
    | isFree : forall x M,
        M x = Undefined ->
        IsFree x M.

    Inductive eval : Env * Memory -> Stm -> Env * Memory -> Prop :=
    | EvDecl : forall E M l n,
        IsFree l M ->
        < E | M > Decl n < E; (n, l) | M [l ↦ VInt 0] >

    | EvAss : forall E M e1 e2 l v,
        (* >>>>>>>>>>>>>>>>>>>>> *)
        (E,M) |-L e1 ⇓ l ->
        (* <<<<<<<<<<<<<<<<<<<<< *)
        (E,M) |-R e2 ⇓ v ->
        < E | M > Ass e1 e2 < E | M [l ↦ VInt v] >

    | EvSeq : forall E M E' M' E'' M'' S1 S2,
        < E | M > S1 < E' | M' > ->
        < E' | M' > S2 < E'' | M'' > ->
        < E | M > Seq S1 S2 < E'' | M'' >    
    where "'<' E '|' M '>' alpha '<' E' '|' M' '>'" := (eval (E,M) alpha (E',M')).
    
  End Stm.

End ImpModell.