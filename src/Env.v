Require Export PPS.Map.
Require Import Lists.List.
Import ListNotations.

Set Implicit Arguments.

Section Env.

  Variable ID Val : Type.
  Variable eqID : ID -> ID -> bool.
  Notation "i '==' j" := (eqID i j) (at level 80, right associativity).

  Definition EnvironmentP := partialMap ID Val.
  Definition EnvironmentT := totalMap ID Val.
  Definition EnvironmentL := list (ID * Val).

  Fixpoint lookup (Sigma : EnvironmentL) (i : ID) : option Val :=
    match Sigma with
    | []          => None
    | (k,v) :: ps => if (k == i) then Some v
                    else lookup ps i
    end.

  Fixpoint update (Sigma : EnvironmentL) (i : ID) (v' : Val) : EnvironmentL :=
    match Sigma with
    | []          => [(i,v')]
    | (k,v) :: ps => if (k == i) then (k,v') :: ps
                    else (k,v) :: update ps i v'
    end.

  Definition union (Sigma Delta : EnvironmentL) := app Sigma Delta.

End Env.

Section Properties.

  Lemma lookup_deterministic :
    forall (A B : Type) (eqA : A -> A -> bool) (Sigma : EnvironmentL A B) (k : A) (v1 v2 : option B),
      lookup eqA Sigma k = v1 ->
      lookup eqA Sigma k = v2 ->
      v1 = v2.
  Proof.
    intros.
    rewrite H in H0.
    apply H0.
  Qed.

  Lemma lookupT_deterministic :
    forall (A B : Type) (Sigma : EnvironmentT A B) (k : A) (v1 v2 : B),
      Sigma k = v1 ->
      Sigma k = v2 ->
      v1 = v2.
  Proof.
    intros.
    rewrite H in H0.
    apply H0.
  Qed.

  Lemma lookupP_deterministic :
    forall (A B : Type) (Sigma : EnvironmentP A B) (k : A) (v1 v2 : option B),
      Sigma k = v1 ->
      Sigma k = v2 ->
      v1 = v2.
  Proof.
    intros.
    rewrite H in H0.
    apply H0.
  Qed.

    Lemma update_lookup1 :
    forall (A B : Type) (eqA : A -> A -> bool) (Sigma : EnvironmentL A B) (k : A) (v : B),
      (forall x : A, eqA x x = true) ->
      lookup eqA (update eqA Sigma k v) k = Some v.
  Proof.
    intros.
    induction Sigma; simpl.
    - rewrite (H k).
      reflexivity.
    - destruct a.
      remember (eqA a k) as akBool.
      destruct akBool.
      + simpl.
        rewrite <- HeqakBool.
        reflexivity.
      + simpl.
        rewrite <- HeqakBool.
        apply IHSigma.
  Qed.

  Lemma update_lookup2 :
    forall (A B : Type) (eqA : A -> A -> bool) (Sigma : EnvironmentL A B) (k1 k2 : A) (v1 v2 : B),
      (forall x y z : A, eqA x y = eqA x z -> true = eqA y z) ->
      eqA k2 k1 = false ->
      lookup eqA (update eqA Sigma k2 v2) k1 = lookup eqA Sigma k1.
  Proof.
    intros.
    induction Sigma; simpl.
    - rewrite H0.
      reflexivity.
    - destruct a as [ k v ].
      remember (eqA k k2) as kk2Bool.
      destruct kk2Bool.
      + simpl.
        remember (eqA k k1) as kk1Bool.
        destruct kk1Bool.
        * rewrite Heqkk2Bool in Heqkk1Bool.
          specialize (H k k2 k1 Heqkk1Bool).
          congruence.
        * reflexivity.
      + simpl.
        remember (eqA k k1) as kk1Bool.
        destruct kk1Bool.
        * reflexivity.
        * apply IHSigma.
  Qed.

  Lemma union_lookup :
    forall (A B : Type) (eqA : A -> A -> bool) (Sigma Delta : EnvironmentL A B) (k : A),
      lookup A B eqA Delta k = None ->
      lookup A B eqA (union A B Delta Sigma ) k = lookup A B eqA Sigma k.
  Proof.
    intros.
    induction Delta; simpl.
    - reflexivity.
    - destruct a as [k0 v].
      inversion H.
      destruct (eqA k0 k).
      + inversion H1.
      + apply IHDelta.
        apply H1.
  Qed.

End Properties.