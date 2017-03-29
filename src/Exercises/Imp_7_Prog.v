Require Import PPS.Imp.Imp_3_Bool PPS.Env Lists.List EqNat. 
Import ListNotations.

Notation "E ; x" := (union E (cons x nil)) (at level 40).
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

Definition E : Env := [] ; (1, (1, Int)) ; (2, (2, Bool)).
Definition eTM := @emptyTMap Ref Val Undefined.
Definition M := updateTMap Nat.eqb
                  (updateTMap Nat.eqb
                    (updateTMap Nat.eqb
                      (updateTMap Nat.eqb eTM 1 (VInt 0))
                    2 (VBool false))
                  1 (VInt 1))
                1 (VInt 2).

Example e : <[]|eTM> P <E|M>.
Proof. eapply EvSeq; simpl.
       - eapply EvSeq.
         + eapply EvSeq.
           * apply EvDecl. apply isFree. instantiate (1 := 1). reflexivity.
           * apply EvDecl. apply isFree. instantiate (1 := 2).  reflexivity.
         + apply EvAss.
           * eapply EvVarL. apply LRule. apply LAxiom.
           * apply EvNumR.
       - eapply EvWhileTrue.
         + eapply EvLessR.
           * eapply EvVarR.
             -- apply LRule. apply LAxiom.
             -- reflexivity.
           * apply EvNumR.
           * reflexivity.
         + eapply EvSeq.
           * eapply EvAss.
             -- eapply EvVarL. apply LRule. apply LAxiom.
             -- eapply EvPlusR.
                ++ eapply EvVarR.
                   ** apply LRule. apply LAxiom.
                   ** reflexivity.
                ++ apply EvNumR.
                ++ reflexivity.
           * simpl. eapply EvWhileFalse. eapply EvLessR.
             -- eapply EvVarR.
                ** apply LRule. apply LAxiom.
                **  reflexivity.
             -- apply EvNumR. 
             -- reflexivity.
Qed.