Require Import PPS.Exercises.Imp_5_Ref PPS.Env.

Notation "EM '|-R' e ⇓ v" := (evalR EM e v) (at level 80).
Notation "M '[' var ↦ val ']'" := (updateTMap ref_eqb M var val)
                                    (at level 40, right associativity).

Definition x := 0.
Definition y := 1.
Definition E : Env := cons (y, (RefAddr 32, Numeric Int))
                           (cons (x, (RefAddr 42, Numeric Int)) nil).

(* Definition upd := @updateTMap Ref Val ref_eqb. *)

Definition M : Memory :=
  (emptyTMap Undefined) [ RefAddr 42 ↦ VNum (VInt 2) ] [ RefAddr 32 ↦ VNum (VInt 5) ].

Definition exp : Exp := Op (Op (Num (VInt 3)) mult (Var (Numeric Int) y))
                           plus
                           (Var (Numeric Int) x).

Example e : (E,M) |-R exp ⇓ VNum (VInt 17).
Proof.
  unfold exp.
  apply EvPlusR with (v1 := VInt 15) (v2 := VInt 2) (tau := Int).
  - apply EvMultR with (v1 := VInt 3) (v2 := VInt 5) (tau := Int).
    + apply EvNumR.
    + apply EvVarR with (l := RefAddr 32).
      * apply LAxiom.
      * reflexivity.
    + apply EvTMult.
      * apply EvTInt.
      * apply EvTVar with (l := RefAddr 32).
        apply LAxiom.
    + reflexivity.
  - apply EvVarR with (l := RefAddr 42).
    + apply LRule.
      apply LAxiom.
    + reflexivity.
  - apply EvTPlus.
    + apply EvTMult.
      * apply EvTInt.
      * apply EvTVar with (l := RefAddr 32).
        apply LAxiom.
    + apply EvTVar with (l := RefAddr 42).
      apply LRule.
      apply LAxiom.
  - reflexivity.
Qed.

Example e2 : (E,M) |-R exp ⇓ VNum (VInt 17).
Proof. repeat econstructor. Qed.