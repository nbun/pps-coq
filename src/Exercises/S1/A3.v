Require Import ImperativeOp Lists.List.
Import ListNotations.


Definition P :=
    Int const 0 :=: (VInt 1);;
    Int  var 1;; 
    Bool var 2;;
    (Var 1) ::= Num (VInt 0);;
    
    While (Op (Var 1) neq  (Num (VInt 1)))
      (Var 1) ::= (Op (Var 1) plus (Const 0)).

  Definition E := [(2, VarType 1 Bool);
                   (1, VarType 0 Int);
                   (0, ConstType Int (VInt 1))].

  Definition M := [(1, VBool false); (0, VInt 1)].

  Example e : ([],[]) {{P}} (E,M).
   Proof. eapply EvSeq.
     - apply EvDeclC.
     - eapply EvSeq.
       * apply EvDecl.
       * eapply EvSeq.
         + apply EvDecl.
         + eapply EvSeq.
           -- apply EvAss.
              ** eapply EvVarL. reflexivity.
              ** apply EvNumR.
           -- eapply EvWhileT.
                ** eapply EvNeqTR.
                   ++ eapply EvVarR.
                      --- reflexivity.
                      --- reflexivity.
                   ++ apply EvNumR.
                   ++ intros H. inversion H.
                ** eapply EvSeq.
                   ++ apply EvAss.
                      --- eapply EvVarL. reflexivity.
                      --- eapply EvPlusR.
                          *** eapply EvVarR. reflexivity. reflexivity.
                          *** eapply EvConstR. reflexivity.
                          *** reflexivity.
                   ++ eapply EvWhileF.
                     --- eapply EvNeqFR.
                         *** eapply EvVarR.
                             +++ reflexivity.
                             +++ reflexivity.
                         *** apply EvNumR.
                         *** reflexivity.
  Qed.
  
  Example e2 : ([],[]) {{P}} (E,M).
  Proof. repeat econstructor. auto. Qed.