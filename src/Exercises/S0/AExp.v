Set Implicit Arguments.

Inductive Exp : Type :=
| Num : nat -> Exp
| Plus : Exp -> Exp -> Exp
| Mult : Exp -> Exp -> Exp.

Fixpoint eval (e : Exp) : nat :=
  match e with
  | Num n => n
  | Plus e1 e2 => eval e1 + eval e2
  | Mult e1 e2 => eval e1 * eval e2
  end.

Example e1 :
  eval (Plus (Num 1) (Num 2)) = 3.
Proof.
  unfold eval.
  unfold "+".
  reflexivity.
Qed.

Example e2 :
  eval (Mult (Plus (Num 1) (Num 2)) (Num 0)) = 0.
Proof.
  unfold eval.
  unfold "+".
  unfold "*".
  reflexivity.
Qed.

Fixpoint optimise_0plus (e : Exp) : Exp :=
  match e with
  | Num n => Num n
  | Plus (Num 0) e2 => optimise_0plus  e2
  | Plus e1 e2 => Plus (optimise_0plus e1) (optimise_0plus e2)
  | Mult e1 e2 => Mult (optimise_0plus e1) (optimise_0plus e2)
  end.

Example e3 :
  eval (optimise_0plus (Mult (Plus (Num 1) (Num 2)) (Num 0))) = 0.
Proof.
  unfold optimise_0plus.
  unfold eval.
  unfold "+".
  unfold "*".
  reflexivity.
Qed.

Theorem optimise_0plus_sound :
  forall exp,
    eval (optimise_0plus exp) = eval exp.
Proof.
  intros.
  induction exp.
  - simpl optimise_0plus.
    reflexivity.
  - simpl optimise_0plus.
    destruct exp1.
    + destruct n.
      * simpl eval at 2.
        apply IHexp2.
      * simpl optimise_0plus.
        simpl eval.
        rewrite IHexp2.
        reflexivity.
    + simpl optimise_0plus.
      simpl eval.
      simpl in IHexp1.
      rewrite IHexp1.
      rewrite IHexp2.
      reflexivity.
    + simpl optimise_0plus.
      simpl eval.
      simpl in IHexp1.
      rewrite IHexp1.
      rewrite IHexp2.
      reflexivity.
  -  simpl optimise_0plus.
     simpl eval.
     rewrite IHexp1.
     rewrite IHexp2.
     reflexivity.
Qed.
