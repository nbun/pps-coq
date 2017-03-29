Require Import PPS.Imp.Imp_3_Bool PPS.Env.

Notation "t 'var' n" := (Decl t n) (at level 30).
Notation "S ;; S'" := (Seq S S') (at level 50).
Notation "L ::= R" := (Ass L R) (at level 30).
Notation "'While' E 'Do' S" := (While E S) (at level 40).
Notation "'<' E '|' M '>' alpha '<' E' '|' M' '>'" := (eval (E,M) alpha (E',M'))     (at level 40, E at level 39, M at level 39, M' at level 40, E' at level 39,
   alpha at level 39).

Definition P :=
  Int var 1;; 
  Bool var 2;;
  Var Int 1 ::= (Num 1);;

  While (Less (Var Int 1) (Num 1)) Do
    (Var Int 1) ::= (Plus (Var Int 1) (Num 1)).

Definition E : Env := cons (2, (2, Bool)) (cons (1, (1, Int)) nil).
Definition eTM := @emptyTMap Ref Val Undefined.
Definition M := updateTMap Nat.eqb
                  (updateTMap Nat.eqb
                    (updateTMap Nat.eqb
                      (updateTMap Nat.eqb eTM 1 (VInt 0))
                    2 (VBool false))
                  1 (VInt 1))
                1 (VInt 2).

Example e : < nil | eTM > P < E | M >.
Proof.
  unfold P.
  eapply EvSeq; simpl.
  - eapply EvSeq.
    + eapply EvSeq.
      * apply EvDecl with (l := 1).
        apply isFree.
        reflexivity.
      * apply EvDecl with (l := 2).
        apply isFree.
        reflexivity.
    + apply EvAss; simpl.
      * apply EvVarL with (l := 1).
        apply LRule.
        apply LAxiom.
      * apply EvNumR.
  - apply EvWhileTrue; simpl.
    + eapply EvLessR.
      * apply EvVarR with (l := 1).
        -- apply LRule.
           apply LAxiom.
        -- reflexivity.
      * apply EvNumR.
      * reflexivity.
    + eapply EvSeq.
      * apply EvAss; simpl.
        -- apply EvVarL.
           apply LRule.
           apply LAxiom.
        -- eapply EvPlusR.
           ++ apply EvVarR with (l := 1).
              ** apply LRule.
                 apply LAxiom.
              ** reflexivity.
           ++ apply EvNumR.
           ++ reflexivity.
      * apply EvWhileFalse.
        eapply EvLessR.
        -- apply EvVarR with (l := 1).
           ** apply LRule. apply LAxiom.
           ** reflexivity.
        -- apply EvNumR. 
        -- reflexivity.
Qed.