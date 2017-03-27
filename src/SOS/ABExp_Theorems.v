Require Import PPS.SOS.ABExp.
Require Import PPS.Env.
Require Import EqNat.

Set Implicit Arguments.

Theorem aevalR_iff_aevalF :
  forall Sigma e v,
    Sigma |-a e ⇓ v <->
    aevalF e Sigma = Some v.
Proof.
  split.
  - intros; induction H; subst; simpl.
    + reflexivity.
    + apply H.
    + rewrite IHaevalR1.
      rewrite IHaevalR2.
      reflexivity.
    + rewrite IHaevalR1.
      rewrite IHaevalR2.
      reflexivity.
    + rewrite IHaevalR1.
      rewrite IHaevalR2.
      reflexivity.
  - intros. generalize dependent v.
    induction e; intros; simpl in H.
    + inversion H; subst.
      apply EvNum.
    + apply EvVar.
      apply H.
    + destruct (aevalF e1 Sigma).
      * destruct (aevalF e2 Sigma).
        -- apply EvPlus with (v1 := n) (v2 := n0).
           ++ apply IHe1.
              reflexivity.
           ++ apply IHe2.
              reflexivity.
           ++ inversion H.
              reflexivity.
        -- inversion H.
      * inversion H.
    + destruct (aevalF e1 Sigma); [ | inversion H].
      * destruct (aevalF e2 Sigma); [ | inversion H].
        -- apply EvSub with (v1 := n) (v2 := n0).
           ++ apply IHe1; reflexivity.
           ++ apply IHe2; reflexivity.
           ++ inversion H; reflexivity.
    + destruct (aevalF e1 Sigma); [ | inversion H].
      * destruct (aevalF e2 Sigma); [ | inversion H].
        -- apply EvMult with (v1 := n) (v2 := n0).
           ++ apply IHe1; reflexivity.
           ++ apply IHe2; reflexivity.
           ++ inversion H; reflexivity.
Qed.

Theorem bevalR_iff_bevalF :
  forall Sigma e v,
    Sigma |-b e ⇓ v <->
    bevalF e Sigma = Some v.
Proof.
  split.
  - intros; induction H; simpl.
    + reflexivity.
    + reflexivity.
    + apply aevalR_iff_aevalF in H; rewrite H.
      apply aevalR_iff_aevalF in H0; rewrite H0.
      subst.
      reflexivity.
  - intros. generalize dependent v.
    induction e; intros.
    + inversion H; subst.
      apply EvT.
    + inversion H; subst.
      apply EvF.
    + simpl in H.
      destruct (aevalF a Sigma) eqn:Ha; [ | inversion H].
      * destruct (aevalF a0 Sigma) eqn:Ha0; [ | inversion H].
        -- apply EvLess with (v1 := n) (v2 := n0).
           ++ apply aevalR_iff_aevalF.
              apply Ha.
           ++ apply aevalR_iff_aevalF.
              apply Ha0.
           ++ inversion H; subst; reflexivity.
Qed.

Theorem aevalR_deterministic :
  forall Sigma e v1 v2,
    Sigma |-a e ⇓ v1 -> 
    Sigma |-a e ⇓ v2 ->
    v1 = v2.
Proof.
  intros.
  generalize dependent v2.
  induction H; intros.
  - inversion H0; subst.
    reflexivity.
  - inversion H0; subst.
    pose proof (lookup_deterministic beq_nat Sigma x H H2).
    inversion H1.
    reflexivity.
  - inversion H2; subst.
    f_equal.
    + apply IHaevalR1.
      apply H5.
    + apply IHaevalR2.
      apply H6.
  - inversion H2; subst.
    f_equal.
    + apply IHaevalR1.
      apply H5.
    + apply IHaevalR2.
      apply H6.
  - inversion H2; subst.
    f_equal.
    + apply IHaevalR1.
      apply H5.
    + apply IHaevalR2.
      apply H6.
Qed.
 
Theorem bevalR_deterministic :
  forall Sigma e v1 v2,
    Sigma |-b e ⇓ v1 ->
    Sigma |-b e ⇓ v2 ->
    v1 = v2.
Proof.
  intros.
  induction e.
  - inversion H; inversion H0; subst.
    reflexivity.
  - inversion H; inversion H0; subst.
    reflexivity.
  - inversion H; inversion H0; subst.
    pose proof (aevalR_deterministic H3 H10).
    pose proof (aevalR_deterministic H4 H11).
    subst.
    reflexivity.
Qed.