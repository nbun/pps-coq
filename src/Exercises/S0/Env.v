Set Implicit Arguments.

Section TotalMap.

  Variable K V : Type.
  Variable eqK : K -> K -> bool.

  Definition totalMap := K -> V.

  Definition emptyTMap (v : V) : totalMap := fun _ => v.

  Definition updateTMap (m : totalMap) (k : K) (v : V) :=
    fun k' => if eqK k k' then v else m k'.

End TotalMap.

Section PartialMap.

  Variable K V : Type.
  Variable eqK : K -> K -> bool.

  Definition partialMap := totalMap K (option V).

  Definition emptyPMap : partialMap := emptyTMap None.

  Definition updatePMap (m : partialMap) (k : K) (v : V) :=
    updateTMap eqK m k (Some v).

End PartialMap.

Section Env.

  Variable K V : Type.
  Variable eqK : K -> K -> bool.
  Notation "i '==' j" := (eqK i j) (at level 80, right associativity).

  Definition listMap := list (K * V).

  Fixpoint lookup (Sigma : listMap) (k : K) : option V :=
    match Sigma with
    | nil          => None
    | cons (k',v) Delta => if (k' == k) then Some v
                      else lookup Delta k
    end.

  Definition add (Sigma : listMap) (k : K) (v' : V) : listMap :=
    cons (k,v') Sigma.
  
  Fixpoint update (Sigma : listMap) (k : K) (v : V) : listMap :=
    match Sigma with
    | nil            => cons (k,v) nil
    | cons (k',v') Delta => if (k' == k) then cons (k',v) Delta
                    else cons (k',v') (update Delta k v)
    end.

  Definition union (Sigma Delta : listMap) : listMap := app Sigma Delta.

End Env.

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

End Properties.