Set Implicit Arguments.

Section TotalMap.

  Variable K V : Type.
  Variable eqK : K -> K -> bool.
  Notation "i '==' j" := (eqK i j) (at level 80, right associativity).

  Definition totalMap := K -> V.

  Definition emptyTMap (v : V) : totalMap := fun _ => v.

  Definition updateTMap (m : totalMap) (k : K) (v : V) :=
    fun k' => if k == k' then v else m k'.

End TotalMap.

Section PartialMap.

  Variable K V : Type.
  Variable eqK : K -> K -> bool.

  Definition partialMap := totalMap K (option V).

  Definition emptyPMap : partialMap := emptyTMap None.

  Definition updatePMap (m : partialMap) (k : K) (v : V) :=
    updateTMap eqK m k (Some v).

End PartialMap.

Section ListMap.

  Variable K V : Type.
  Variable eqK : K -> K -> bool.
  Notation "i '==' j" := (eqK i j) (at level 80, right associativity).

  Definition listMap := list (K * V).

  Definition add (kvs : listMap) (k : K) (v : V) : listMap :=
    cons (k,v) kvs.

  Fixpoint update (kvs : listMap) (k : K) (v : V) : listMap :=
    match kvs with
    | nil               => cons (k,v) nil
    | cons (k',v') kvs' => if (k' == k) then cons (k',v) kvs'
                          else cons (k',v') (update kvs' k v)
    end.

  Fixpoint lookup (kvs : listMap) (k : K) : option V :=
    match kvs with
    | nil              => None
    | cons (k',v) kvs' => if (k' == k) then Some v
                         else lookup kvs' k
    end.

  Definition union (kvs1 kvs2 : listMap) : listMap := app kvs1 kvs2.

End ListMap.

Section Properties.

  Lemma lookup_deterministic :
    forall (A B : Type) (eqA : A -> A -> bool) (Sigma : listMap A B) (k : A) (v1 v2 : option B),
      lookup eqA Sigma k = v1 ->
      lookup eqA Sigma k = v2 ->
      v1 = v2.
  Proof.
    intros.
    rewrite H in H0.
    apply H0.
  Qed.

  Lemma lookupT_deterministic :
    forall (A B : Type) (Sigma : totalMap A B) (k : A) (v1 v2 : B),
      Sigma k = v1 ->
      Sigma k = v2 ->
      v1 = v2.
  Proof.
    intros.
    rewrite H in H0.
    apply H0.
  Qed.

  Lemma lookupP_deterministic :
    forall (A B : Type) (Sigma : partialMap A B) (k : A) (v1 v2 : option B),
      Sigma k = v1 ->
      Sigma k = v2 ->
      v1 = v2.
  Proof.
    intros.
    rewrite H in H0.
    apply H0.
  Qed.


  Lemma update_lookupT1 :
    forall (A B : Type) (eqA : A -> A -> bool) (Sigma : totalMap A B) (k : A) (v : B),
      (forall x : A, eqA x x = true) ->
      (updateTMap eqA Sigma k v) k = v.
  Proof.
    intros.
    unfold updateTMap.
    rewrite (H k).
    reflexivity.
  Qed.

  Lemma update_lookupT2 :
    forall (A B : Type) (eqA : A -> A -> bool) (Sigma : totalMap A B) (k1 k2 : A) (v1 v2 : B),
      eqA k2 k1 = false ->
      (updateTMap eqA Sigma k2 v2) k1 = Sigma k1.
  Proof.
    intros.
    unfold updateTMap.
    rewrite H.
    reflexivity.
  Qed.

  Lemma add_lookupL1 :
    forall (A B : Type) (eqA : A -> A -> bool) (Sigma : listMap A B) (k : A) (v : B),
      (forall x : A, eqA x x = true) ->
      lookup eqA (add Sigma k v) k = Some v.
  Proof.
    intros.
    unfold add.
    simpl lookup.
    rewrite (H k).
    reflexivity.
  Qed.

  Lemma add_lookupL2 :
    forall (A B : Type) (eqA : A -> A -> bool) (Sigma : listMap A B) (k1 k2 : A) (v  : B),
      eqA k2 k1 = false ->
      lookup eqA (add Sigma k2 v) k1 = lookup eqA Sigma k1.
  Proof.
    intros.
    unfold add.
    simpl lookup.
    rewrite H.
    reflexivity.
  Qed.    

  Lemma update_lookup1 :
    forall (A B : Type) (eqA : A -> A -> bool) (Sigma : listMap A B) (k : A) (v : B),
      (forall x : A, eqA x x = true) ->
      lookup eqA (update eqA Sigma k v) k = Some v.
  Proof.
    intros.
    induction Sigma; simpl.
    - rewrite (H k).
      reflexivity.
    - destruct a as [k' v'].
      destruct (eqA k' k) eqn:HeqKK.
      + simpl lookup.
        rewrite HeqKK.
        reflexivity.
      + simpl lookup.
        rewrite HeqKK.
        apply IHSigma.
  Qed.

  Lemma update_lookup2 :
    forall (A B : Type) (eqA : A -> A -> bool) (Sigma : listMap A B) (k1 k2 : A) (v : B),
      (forall x y z : A, eqA x y = eqA x z -> true = eqA y z) ->
      eqA k2 k1 = false ->
      lookup eqA (update eqA Sigma k2 v) k1 = lookup eqA Sigma k1.
  Proof.
    intros.
    induction Sigma; simpl.
    - rewrite H0.
      reflexivity.
    - destruct a as [k' v'].
      destruct (eqA k' k2) eqn:HeqKK2.
      + simpl lookup.
        destruct (eqA k' k1) eqn:HeqKK1.
        * rewrite <- HeqKK1 in HeqKK2.
          specialize (H k' k2 k1 HeqKK2).
          congruence.
        * reflexivity.
      + simpl lookup.
        destruct (eqA k' k1) eqn:HeqKK1.
        * reflexivity.
        * apply IHSigma.
  Qed.

  Lemma union_lookup :
    forall (A B : Type) (eqA : A -> A -> bool) (Sigma Delta : listMap A B) (k : A),
      lookup eqA Delta k = None ->
      lookup eqA (union Delta Sigma ) k = lookup eqA Sigma k.
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