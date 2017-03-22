Require Import PPS.SOS.SOS.

Set Implicit Arguments.

Section Theorems.

  Variable Exp : Type.
  Variable BExp : Type.
  Variable Val : Type.
  Variable IExp : Exp -> SOS_Context Val -> Val -> Prop.
  Variable IBExp : BExp -> SOS_Context Val -> bool -> Prop.

  Notation "<| S , o |> --> <| S' , o' |>" := (stepR IExp IBExp S o S' o').

  Variable IExp_deterministic :
  forall e c v1 v2, IExp e c v1 -> IExp e c v2 -> v1 = v2.
      
  Theorem stepR_deterministic_context :
    forall stm stm1 stm2 c c1 c2,
      <| stm, c |> --> <| stm1, c1 |> ->
      <| stm, c |> --> <| stm2, c2 |> ->
      c1 = c2.
  Proof.
    intros.
    generalize dependent stm2.
    (* generalize dependent c2. *)
    induction H; intros.
    - inversion H0; subst.
      specialize (IExp_deterministic H H6).
      rewrite <- IExp_deterministic.
      reflexivity.
    - inversion H0; subst.
      + reflexivity.
      + inversion H5; subst.
    - inversion H0; subst.
      + inversion H.
      + apply IHstepR with (stm2 := S4).
        apply H6.
    - inversion H0; subst.
      + reflexivity.
      + reflexivity.
    - inversion H0; subst.
      + reflexivity.
      + reflexivity.
    - inversion H0; subst.
      + reflexivity.
      + reflexivity.
    - inversion H0; subst.
      + reflexivity.
      + reflexivity.
  Qed.

  Variable IBExp_deterministic :
    forall e c v1 v2, IBExp e c v1 -> IBExp e c v2 -> v1 = v2.

  Theorem stepR_deterministic_stm :
    forall stm stm1 stm2 c c1 c2,
      <| stm, c |> --> <| stm1, c1 |> ->
      <| stm, c |> --> <| stm2, c2 |> ->
      stm1 = stm2.
  Proof.
    intros.
    generalize dependent stm2.
    induction H; intros.
    - inversion H0; subst.
      reflexivity.
    - inversion H0; subst.
      + reflexivity.
      + inversion H5; subst.
    - inversion H0; subst.
      + inversion H.
      + f_equal.
        apply IHstepR with (stm2 := S4).
        apply H6.
    - inversion H0; subst.
      + reflexivity.
      + specialize (IBExp_deterministic H H7).
        inversion IBExp_deterministic.
    - inversion H0; subst.
      + specialize (IBExp_deterministic H H7).
        inversion IBExp_deterministic.
      + reflexivity.
    - inversion H0; subst.
      + reflexivity.
      + specialize (IBExp_deterministic H H6).
        inversion IBExp_deterministic.
    - inversion H0; subst.
      + specialize (IBExp_deterministic H H6).
        inversion IBExp_deterministic.
      + reflexivity.
  Qed.
      
  Theorem stepR_deterministic :
    forall stm stm1 stm2 c c1 c2,
      <| stm, c |> --> <| stm1, c1 |> ->
      <| stm, c |> --> <| stm2, c2 |> ->
      stm1 = stm2 /\ c1 = c2.
  Proof.
    split.
    - apply stepR_deterministic_stm
      with (c := c) (c1 := c1) (c2 := c2) (stm := stm).
      + apply H.
      + apply H0.
    - apply stepR_deterministic_context
      with (stm := stm) (stm1 := stm1) (stm2 := stm2) (c := c).
      + apply H.
      + apply H0.
  Qed.

End Theorems.