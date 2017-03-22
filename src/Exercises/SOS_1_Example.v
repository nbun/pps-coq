Require Import PPS.SOS.ABExp.
Require Import PPS.SOS.SOS.

Set Implicit Arguments.

Import SOS_Notation.

Section Example1.

  Definition P1 : S_ BExp AExp := 0 ::= ANum 1.

  Definition P2 : S_ BExp AExp :=
    If AVar 0 :<: ANum 42
       Then 0 ::= ANum 42 :+: AVar 0
       Else SSkip BExp AExp.

  Lemma isTerminatingP1 :
    terminating_computation aevalF bevalF P1 nil.
  Proof.
    unfold terminating_computation.
    exists 0.
    simpl.
    reflexivity.
  Qed.

  Lemma isNotTerminatingP2 :
    ~ terminating_computation aevalF bevalF P2 nil.
  Proof.
    unfold terminating_computation.
    intro H.
    destruct H.
    destruct x; simpl in H.
    - inversion H.
    - inversion H.
  Qed.

  Definition C2 : SOS_Context nat := cons (0, 31) nil.

  Lemma isTerminatingP2 :
    terminating_computation aevalF bevalF P2 C2.
  Proof.
    unfold terminating_computation.
    exists 1.
    simpl.
    reflexivity.
  Qed.

End Example1.
Section Example2.
      
  Definition P3 : S_ BExp AExp := 0 ::= ANum 42 :+: AVar 0.
  Definition C3 : SOS_Context nat := cons (0,73) nil.

  Notation "<| S , o |> --> <| S' , o' |>" := (stepR aevalR bevalR S o S' o').

  Definition Prop1 := <| P2, C2 |> -->
                      <| P3, C2 |>.
  Definition Prop2 := <| P3, C2 |> -->
                      <| SSkip BExp AExp, C3 |>.

  Example e : Prop1 /\ Prop2.
  Proof.
    split; unfold Prop1, Prop2.
    - unfold P2.
      apply StIfT.
      apply EvLess with (v1 := 31) (v2 := 42).
      * apply EvVar. reflexivity.
      * apply EvNum.
      * simpl. reflexivity.
    - unfold P3.
      apply StAss with (val := 73).
      apply EvPlus with (v1 := 42) (v2 := 31).
      * apply EvNum.
      * apply EvVar. unfold C2. reflexivity.
      * reflexivity.
  Qed.

End Example2.
    
