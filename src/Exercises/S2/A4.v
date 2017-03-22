Require Import SOS Lists.List.
Import ListNotations.

Definition x := 0.
Definition y := 1.
Definition z := 2.

Definition Sigma := [(x,(VInt 5)); (y,(VInt 3))].
Definition exp := Op (Var y) mult (Let z (Op (Num (VInt 4)) plus (Var x))
                                         (Op (Var z) sub (Num (VInt 7)))).

Example e : Sigma |- exp ::: VInt 6.
Proof. apply EvMult with (v1 := 3) (v2 := 2).
       - apply EvVar. reflexivity.
       - eapply EvLet.
         * apply EvPlus with (v1 := 4) (v2 := 5).
           + apply EvNum.
           + apply EvVar. reflexivity.
           + reflexivity.
         * reflexivity.
         * apply EvSub with (v1 := 9) (v2 := 7).
           + apply EvVar. reflexivity.
           + apply EvNum.
           + reflexivity.
       - reflexivity.
Qed.

Example e2 : Sigma |- exp ::: VInt 6.
Proof. repeat econstructor. Qed.