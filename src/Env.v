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
    intros A B eqA Sigma k v1 v2 H H0.
    rewrite <- H. rewrite <- H0. reflexivity.
  Qed.

  Lemma lookupP_deterministic :
    forall (A B : Type) (Sigma : EnvironmentP A B) (k : A) (v1 v2 : option B),
      Sigma k = v1 ->
      Sigma k = v2 ->
      v1 = v2.
  Proof.
    intros A B Sigma k v1 v2 H H0. rewrite <- H. auto.
  Qed.

  Lemma update_lookup1 :
    forall (A B : Type) (eqA : A -> A -> bool) (Sigma : EnvironmentL A B) (k : A) (v : B),
      (forall x : A, eqA x x = true) ->
      lookup eqA (update eqA Sigma k v) k = Some v.
  Proof.
    intros A B eqA Sigma k v H. induction Sigma.
    - simpl. rewrite H. reflexivity.
    - destruct a. simpl. destruct (eqA a k) eqn:H0.
      * simpl. rewrite H0. reflexivity.
      * simpl. rewrite H0. apply IHSigma.
  Qed.

  Lemma update_lookup2 :
    forall (A B : Type) (eqA : A -> A -> bool) (Sigma : EnvironmentL A B) (k1 k2 : A) (v1 v2 : B),
      (forall x y z : A, eqA x y = eqA x z -> true = eqA y z) ->
      eqA k2 k1 = false ->
      lookup eqA (update eqA Sigma k2 v2) k1 = lookup eqA Sigma k1.
  Proof.
    intros A B eqA Sigma k1 k2 v1 v2 H H0. induction Sigma.
    - simpl. rewrite H0. reflexivity.
    - destruct a. simpl. destruct (eqA a k2) eqn:H1.
      * assert (eqA a k1 = false). Focus 2.
      * rewrite H2. simpl. rewrite H2. reflexivity. Admitted.

  Lemma union_lookup :
    forall (A B : Type) (eqA : A -> A -> bool) (Sigma Delta : EnvironmentL A B) (k : A),
      lookup eqA Delta k = None ->
      lookup eqA (union Delta Sigma ) k = lookup eqA Sigma k.
  Proof.
    intros A B eqA Sigma Delta k H. induction Delta.
    - unfold union. rewrite app_nil_l. reflexivity.
    - unfold union. rewrite <- app_comm_cons. destruct a.
      * simpl. assert (eqA a k = false). Focus 2.
      * rewrite H0. apply IHDelta. rewrite <- H. simpl. rewrite H0. reflexivity.
  Admitted.

End Properties.