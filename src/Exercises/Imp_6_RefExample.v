Require Import PPS.Exercises.Imp_5_Ref PPS.Env EqNat Lists.List.
Import ListNotations.

Notation "E ; x" := (union E (cons x nil)) (at level 40).
Notation "EM '|-R' e ⇓ v" := (evalR EM e v) (at level 80).

Definition x := 0.
Definition y := 1.
Definition E : Env := [] ; (x, (42, Numeric Int)) ; (y, (32, Numeric Int)).
Definition updTM := @updateTMap Ref Val beq_nat.
Definition M : Memory := updTM (updTM (emptyTMap Null) 42 (VNum (VInt 2)))
                               32 (VNum (VInt 5)).
Definition exp : Exp := Op (Op (Num (VInt 3)) mult (Var (Numeric Int) y))
                           plus
                           (Var (Numeric Int) x).

Example e : (E,M) |-R exp ⇓ (VNum (VInt 17)).
Proof. eapply EvPlusR with (v1 := VInt 15) (v2 := VInt 2).
       - eapply EvMultR with (v1 := VInt 3) (v2 := VInt 5).
         + apply EvNumR.
         + eapply EvVarR. apply LAxiom. reflexivity.
         + apply EvTMult.
           * apply EvTInt.
           * eapply EvTVar. apply LAxiom.
         + reflexivity.
       - eapply EvVarR. apply LRule. apply LAxiom. reflexivity.
       - apply EvTPlus.
         + apply EvTMult.
           * apply EvTInt.
           * eapply EvTVar. apply LAxiom.
         + eapply EvTVar. apply LRule. apply LAxiom.
       - reflexivity.
Qed.

Example e2 : (E,M) |-R exp ⇓ (VNum (VInt 17)).
Proof. repeat econstructor. Qed.