Require Import PPS.SOS.SOS.
Require Export PPS.Exp.

Set Implicit Arguments.

Reserved Notation "Sigma '|-a' e ⇓ v" (at level 40).
Reserved Notation "Sigma '|-b' e ⇓ v" (at level 40).
  
Section ArithRelation.

  Inductive aevalR : AExp -> SOS_Context nat -> nat -> Prop :=
  | EvNum  : forall Sigma n, Sigma |-a ANum n ⇓ n
  | EvVar  : forall Sigma x v,
      SOS_lookup Sigma x = Some v ->
      Sigma |-a AVar x ⇓ v
  | EvPlus : forall Sigma e1 e2 v1 v2 v,
      Sigma |-a e1 ⇓ v1 ->
      Sigma |-a e2 ⇓ v2 ->
      v = v1 + v2 ->
      Sigma |-a APlus e1 e2 ⇓ v
  | EvSub : forall Sigma e1 e2 v1 v2 v,
      Sigma |-a e1 ⇓ v1 ->
      Sigma |-a e2 ⇓ v2 ->
      v = v1 - v2 ->
      Sigma |-a AMinus e1 e2 ⇓ v
  | EvMult : forall Sigma e1 e2 v1 v2 v,
      Sigma |-a e1 ⇓ v1 ->
      Sigma |-a e2 ⇓ v2 ->
      v = v1 * v2 ->
      Sigma |-a AMult e1 e2 ⇓ v
  where "Sigma '|-a' e ⇓ v" := (aevalR e Sigma v).

End ArithRelation.

Section ArithFunction.

  Fixpoint aevalF (e : AExp) (c0 : SOS_Context nat) : option nat :=
    match e with
    | ANum n => Some n
    | AVar x => SOS_lookup c0 x
    | APlus e1 e2 =>
      match aevalF e1 c0, aevalF e2 c0 with
      | Some v1, Some v2 =>
        Some (v1 + v2)
      | _,_ => None
      end
    | AMult e1 e2 =>
      match aevalF e1 c0, aevalF e2 c0 with
      | Some v1, Some v2 =>
        Some (v1 * v2)
      | _,_ => None
      end
    | AMinus e1 e2 =>
      match aevalF e1 c0, aevalF e2 c0 with
      | Some v1, Some v2 =>
        Some (v1 - v2)
      | _,_ => None
      end
    end.

End ArithFunction.

Notation "Sigma '|-a' e ⇓ v" := (aevalR e Sigma v).

Section BoolRelation.

  Inductive bevalR : BExp -> SOS_Context nat -> bool -> Prop :=
  | EvT : forall Sigma, Sigma |-b BTrue ⇓ true
  | EvF : forall Sigma, Sigma |-b BFalse ⇓ false
  | EvLess : forall Sigma e1 e2 v1 v2 b,
      Sigma |-a e1 ⇓ v1 ->
      Sigma |-a e2 ⇓ v2 ->
      b = Nat.leb v1 v2 ->
      Sigma |-b BLess e1 e2 ⇓ b
  where "Sigma '|-b' e ⇓ v" := (bevalR e Sigma v).

End BoolRelation.

Section BoolFunction.

  Fixpoint bevalF (be : BExp) (c0 : SOS_Context nat) : option bool :=
    match be with
    | BTrue => Some true
    | BFalse => Some false
    | BLess e1 e2 =>
      match aevalF e1 c0, aevalF e2 c0 with
      | Some v1, Some v2 => Some (Nat.leb v1 v2)
      | _,_ => None
      end
    end.

End BoolFunction.

Notation "Sigma '|-b' e ⇓ v" := (bevalR e Sigma v).