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

Lemma evplus_O : forall Sigma e1 e2 v,    
    Sigma |-a e1 :+: e2 ⇓ v ->
    Sigma |-a e1 ⇓ v ->
    Sigma |-a e2 ⇓ 0.
Proof.
Admitted.

Lemma evplus_v : forall Sigma e1 e2 v,
    Sigma |-a e1 :+: e2 ⇓ v ->
    Sigma |-a e2 ⇓ 0 ->
    Sigma |-a e1 ⇓ v.
Proof.
Admitted.

Theorem aevalR_deterministic :
  forall Sigma e v1 v2,
    Sigma |-a e ⇓ v1 -> 
    Sigma |-a e ⇓ v2 ->
    v1 = v2.
Proof.
  intros Sigma e v1 v2 H H0. generalize dependent v2. induction H.
  - intros. inversion H0. reflexivity.
  - intros. inversion H0. apply eq_cons_opt.
    apply lookup_deterministic with
      (A := nat) (eqA := beq_nat) (Sigma := Sigma) (k := x).
    + rewrite <- H. reflexivity.
    + rewrite <- H2. reflexivity.
  - intros. rewrite H1. apply evplus_O with (e2 := e2) in H.
    + apply IHaevalR2 in H. rewrite H. rewrite <- plus_n_O. apply IHaevalR1.
      rewrite H in H0. apply evplus_v with (e2 := e2) in H2.
      * assumption.
      * assumption.
    + econstructor. apply H. apply H0. Admitted.
 
Theorem bevalR_deterministic :
  forall Sigma e v1 v2,
    Sigma |-b e ⇓ v1 ->
    Sigma |-b e ⇓ v2 ->
    v1 = v2.
Proof.
  intros. destruct e eqn:t; try (inversion H; inversion H0; reflexivity).
  inversion H. inversion H0.
  rewrite H7. rewrite H14.
  replace v0 with v4. replace v3 with v5. reflexivity.
  eapply aevalR_deterministic. apply H11. apply H4.
  eapply aevalR_deterministic. apply H10. apply H3.
Qed.