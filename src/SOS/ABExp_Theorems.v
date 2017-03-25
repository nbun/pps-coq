Require Import PPS.SOS.ABExp.
Require Import PPS.Env.
Require Import EqNat.

Set Implicit Arguments.

Lemma eq_cons_poly: forall (T1 : Type) (T2 : Type -> Type) (C : T1 -> (T2 T1)) (x y : T1),
    x = y <-> C x = C y.
Proof.
  split.
  - intros. rewrite H. reflexivity.
  - intros. inversion H. Admitted.

Lemma eq_cons_opt: forall (T : Type) (x y : T),
    x = y <-> Some x = Some y.
Proof.
  split.
  - intros. rewrite H. reflexivity.
  - intros. inversion H. reflexivity.
Qed.

Theorem aevalR_deterministic :
  forall Sigma e v1 v2,
    Sigma |-a e ⇓ v1 -> 
    Sigma |-a e ⇓ v2 ->
    v1 = v2.
Proof.
  intros. destruct e eqn:t.
  - inversion H. inversion H0. rewrite <- H3. rewrite <- H6. reflexivity.
  - apply eq_cons_opt. apply lookup_deterministic with (A := nat) (eqA := beq_nat)
                                                       (Sigma := Sigma) (k := n).
    + inversion H. assumption.
    + inversion H0. assumption.
  - Admitted.

Theorem bevalR_deterministic :
  forall Sigma e v1 v2,
    Sigma |-b e ⇓ v1 ->
    Sigma |-b e ⇓ v2 ->
    v1 = v2.
Proof.
  intros. destruct e eqn:t; try (inversion H; inversion H0; reflexivity).
  Admitted.