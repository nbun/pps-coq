Require Import PPS.Exercises.SOS_2_For.
Require Import PPS.SOS.ABExp.

Require Import Lists.List.
Import ListNotations.

Import SOS_Notation.

Definition j := 0.
Definition n := 1.
Definition u := 2.
Definition v := 3.
Definition w := 4.

Definition P : S_ BExp AExp :=
  j ::= ANum 1;;
  n ::= ANum 3;;
  u ::= ANum 1;;
  v ::= ANum 1;;
  w ::= ANum 1;;
  While AVar j :<: AVar n Do (
    w ::= AVar u :+: AVar v;;
    u ::= AVar v;;
    v ::= AVar w;;
    j ::= AVar j :+: ANum 1
  ).

Definition P2 : S_ BExp AExp :=
  SSkip BExp AExp;;
  n ::= ANum 3;;
  u ::= ANum 1;;
  v ::= ANum 1;;
  w ::= ANum 1;;
  While AVar j :<: AVar n Do (
    w ::= AVar u :+: AVar v;;
    u ::= AVar v;;
    v ::= AVar w;;
    j ::= AVar j :+: ANum 1
  ).

Definition C1 := [(0,0); (1,0); (2,0); (3,0); (4, 0)].
Definition C2 := [(0,1); (1,0); (2,0); (3,0); (4,0)].

Notation "<| S , o |> --> <| S' , o' |>" := (stepR aevalR bevalR S o S' o').

Definition Prop1 := <| P, C1  |> --> <| P2, C2 |>.

Example e1 : Prop1.
Proof.
  unfold Prop1.
  unfold P, P2.
  apply StSeq.
  apply StAss with (o := C1) (v := j).
  apply EvNum.
Qed.

Definition P21 :=
  n ::= ANum 3;;
  u ::= ANum 1;;
  v ::= ANum 1;;
  w ::= ANum 1;;
  While AVar j :<: AVar n Do (
    w ::= AVar u :+: AVar v;;
    u ::= AVar v;;
    v ::= AVar w;;
    j ::= AVar j :+: ANum 1
  ).

Definition P3 :=
  SSkip BExp AExp;;
  u ::= ANum 1;;
  v ::= ANum 1;;
  w ::= ANum 1;;
  While AVar j :<: AVar n Do (
    w ::= AVar u :+: AVar v;;
    u ::= AVar v;;
    v ::= AVar w;;
    j ::= AVar j :+: ANum 1
  ).

Definition C3 := [(0,1); (1,3); (2,0); (3,0); (4,0)].
Definition Prop2 := <| P21, C2 |> --> <| P3, C3 |>.

Example e2 : Prop2.
Proof.
  unfold Prop2.
  unfold P21, P3.
  apply StSeq.
  apply StAss with (o := C2) (v := n).
  apply EvNum.
Qed.
