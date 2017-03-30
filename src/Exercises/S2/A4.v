Require Import PPS.Exercises.S2.ABExp_Let.
Require Import PPS.SOS.SOS.
Require Import Lists.List.
Set Implicit Arguments.

Import SOS_Notation.
Import ListNotations.

Definition x := 0.
Definition y := 1.
Definition z := 2.

Definition Sigma := [(x, 5); (y, 3)].
Definition exp := (AVar y) :*: (Let z :=: (ANum 4) :+: (AVar x)
                                In (AVar z) :-: (ANum 7)).

Example e : Sigma |-a exp ⇓ 6.
Proof. apply EvMult with (v1 := 3) (v2 := 2).
       - apply EvVar. reflexivity.
       - eapply EvLet.
         + apply EvPlus with (v1 := 4) (v2 := 5).
           * apply EvNum.
           * apply EvVar. reflexivity.
           * reflexivity.
         + apply EvSub with (v1 := 9) (v2 := 7).
           * apply EvVar. reflexivity.
           * apply EvNum.
           * reflexivity.
       - reflexivity.
Qed.

Example e2 : Sigma |-a exp ⇓ 6.
Proof. repeat econstructor. Qed.