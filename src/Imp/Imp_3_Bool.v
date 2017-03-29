Require Import PPS.Env.

Set Implicit Arguments.

Section ImpModell.

  Inductive Val : Type :=
  | VInt      : nat -> Val
  (* >>>>>>>>>>>>>>>>>>>>> *)
  | VBool     : bool -> Val
  (* <<<<<<<<<<<<<<<<<<<<< *)
  | Undefined : Val.

  Definition Ref := nat.
  Definition Name := nat.

  Inductive Ty : Type :=
  | Int    : Ty
  (* >>>>>>>>>>>>>>>>>>>>> *)
  | Bool   : Ty.
  (* <<<<<<<<<<<<<<<<<<<<< *)

  Definition EnvEntry : Type := Ref * Ty.

  Definition Env := listMap Name EnvEntry.

  Definition Memory := totalMap Ref Val.

  Reserved Notation "E '|-l' val" (at level 80).

  Notation "E ; x" := (union E (cons x nil)) (at level 40).

  Section EnvRelation.
    
    Inductive Lookup : Env -> (Name * EnvEntry) -> Prop :=
    | LAxiom : forall E x beta,
        E; (x, beta) |-l (x, beta)
    | LRule : forall E x y beta gamma,
        E |-l (x,beta) ->
        E; (y, gamma) |-l (x, beta)
    where "E '|-l' val" := (Lookup E val).
      
  End EnvRelation.
  Notation "E '|-l' val" := (Lookup E val).

  Section Exp.

    Inductive Exp : Type :=
    | Num : nat -> Exp
    (* >>>>>>>>>>>>>>>>>>>>> *)
    | BoolE : bool -> Exp
    (* <<<<<<<<<<<<<<<<<<<<< *)
    | Var : Ty -> Name -> Exp
    | Plus : Exp -> Exp -> Exp
    | Mult : Exp -> Exp -> Exp
    (* >>>>>>>>>>>>>>>>>>>>> *)
    | Less : Exp -> Exp -> Exp.
    (* <<<<<<<<<<<<<<<<<<<<< *)
    
  End Exp.

  Reserved Notation "EM '|-R' e ⇓ v" (at level 80).
  Section EvalR.

    Inductive evalR : (Env * Memory) -> Exp -> Val -> Prop :=
    | EvVarR  : forall E M x l tau val,
        E |-l (x, (l,tau)) ->
        M l = val ->
        (E,M) |-R (Var tau x) ⇓ val

    | EvNumR  : forall E M n, (E,M) |-R Num n ⇓ VInt n

    (* >>>>>>>>>>>>>>>>>>>>> *)
    | EVBoolR : forall E M b, (E,M) |-R BoolE b ⇓ VBool b
    (* <<<<<<<<<<<<<<<<<<<<< *)

    | EvPlusR : forall E M e1 e2 v1 v2 v,
        (E,M) |-R e1 ⇓ VInt v1 ->
        (E,M) |-R e2 ⇓ VInt v2 ->
        v = VInt (v1 + v2) ->
        (E,M) |-R Plus e1 e2 ⇓ v
                               
    | EvMultR : forall E M e1 e2 v1 v2 v,
        (E,M) |-R e1 ⇓ VInt v1 ->
        (E,M) |-R e2 ⇓ VInt v2 ->
        v = VInt (v1 * v2) ->
        (E,M) |-R Mult e1 e2 ⇓ v

    (* >>>>>>>>>>>>>>>>>>>>> *)
    | EvLessR : forall E M e1 e2 v1 v2 b,
        (E,M) |-R e1 ⇓ VInt v1 ->
        (E,M) |-R e2 ⇓ VInt v2 ->
        b = VBool (Nat.leb v1 v2) ->
        (E,M) |-R Less e1 e2 ⇓ b
    (* <<<<<<<<<<<<<<<<<<<<< *)

    where "EM '|-R' e ⇓ v" := (evalR EM e v).

  End EvalR.
  Notation "EM '|-R' e ⇓ v" := (evalR EM e v).

  Reserved Notation "EM '|-L' e ⇓ v" (at level 80).
  Section EvalL.
    
    Inductive evalL : (Env * Memory) -> Exp -> Ref -> Prop :=
    | EvVarL : forall E M x l tau,
        E |-l (x, (l,tau)) ->
        (E,M) |-L (Var tau x) ⇓ l
  where "EM '|-L' e ⇓ v" := (evalL EM e v).

  End EvalL.
  Notation "EM '|-L' e ⇓ v" := (evalL EM e v).

  Section Stm.

    Inductive Stm : Type :=
    | Ass    : Exp -> Exp -> Stm
    | Decl   : Ty -> Name -> Stm
    | Seq    : Stm -> Stm -> Stm
    (* >>>>>>>>>>>>>>>>>>>>> *)
    | If     : Exp -> Stm -> Stm -> Stm
    | While  : Exp -> Stm -> Stm.
    (* <<<<<<<<<<<<<<<<<<<<< *)

    (* >>>>>>>>>>>>>>>>>>>>> *)
    Definition newVarVal (T : Ty) : Val :=
      match T with
      | Int    => VInt 0
      | Bool   => VBool false
      end.
    (* <<<<<<<<<<<<<<<<<<<<< *)

    Reserved Notation "'<' E '|' M '>' alpha '<' E' '|' M' '>'"
             (at level 40, E at level 39, M at level 39, M' at level 40,
              E' at level 39, alpha at level 39).
    Notation "M '[' var ↦ val ']'" := (updateTMap Nat.eqb M var val)
                                        (at level 40, right associativity).

    Inductive IsFree : Ref -> Memory -> Prop :=
    | isFree : forall x M,
        M x = Undefined ->
        IsFree x M.

    Inductive eval : Env * Memory -> Stm -> Env * Memory -> Prop :=
    | EvDecl : forall E M l tau n,
        IsFree l M ->
        < E | M > Decl tau n < E; (n, (l,tau)) | M [l ↦ newVarVal tau] >

     | EvAss : forall E M e1 e2 l v,
        (E,M) |-L e1 ⇓ l ->
        (E,M) |-R e2 ⇓ v ->
        < E | M > Ass e1 e2 < E | M [l ↦ v] >

    | EvSeq : forall E M E' M' E'' M'' S1 S2,
        < E | M > S1 < E' | M' > ->
        < E' | M' > S2 < E'' | M'' > ->
        < E | M > Seq S1 S2 < E'' | M'' >

    (* >>>>>>>>>>>>>>>>>>>>> *)
    | EvIfTrue : forall E M E' M' bexp S1 S2,
        (E,M) |-R bexp ⇓ VBool true ->
        < E | M > S1 < E' | M' > ->
        < E | M > If bexp S1 S2 < E' | M' >

    | EvIfFalse : forall E M E' M' bexp S1 S2,
        (E,M) |-R bexp ⇓ VBool false ->
        < E | M > S2 < E' | M' > ->
        < E | M > If bexp S1 S2 < E' | M' >

    | EvWhileTrue : forall E M E' M' bexp S,
        (E,M) |-R bexp ⇓ VBool true ->
        < E | M > Seq S (While bexp S) < E' | M' > ->
        < E | M > While bexp S < E' | M' >

    | EvWhileFalse : forall E M bexp S,
        (E,M) |-R bexp ⇓ VBool false ->
        < E | M > While bexp S < E | M >
    (* <<<<<<<<<<<<<<<<<<<<< *)

    where "'<' E '|' M '>' alpha '<' E' '|' M' '>'" := (eval (E,M) alpha (E',M')).
    
  End Stm.

End ImpModell.