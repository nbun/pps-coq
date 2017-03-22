Require Import ImperativeOp Lists.List.
Import ListNotations.

Definition x := 0.
Definition y := 1.
Definition E := [(x, VarType 42 Int); (y, VarType 32 Int)].
Definition M := [(42, VInt 2); (32, VInt 5)].
Definition exp := Op (Op (Num (VInt 3)) mult (Var y))
                         plus
                         (Var x).

Example e : (E,M) |-R exp ::: VInt 17.
Proof. apply EvPlusR with (v1 := 15) (v2 := 2).
       - apply EvMultR with (v1 := 3) (v2 := 5).
         * apply EvNumR.
         * apply EvVarR with (l := 32) (T := Int). reflexivity. reflexivity.
         * reflexivity.
       - apply EvVarR with (l := 42) (T := Int). reflexivity. reflexivity.
       - reflexivity.
Qed.

Example e2 : (E,M) |-R exp ::: VInt 17.
Proof. repeat econstructor. Qed.