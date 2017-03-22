Require Import PPS.SOS.ABExp.

Set Implicit Arguments.

Theorem aevalR_deterministic :
  forall Sigma e v1 v2,
    Sigma |-a e ⇓ v1 ->
    Sigma |-a e ⇓ v2 ->
    v1 = v2.
Proof.
Admitted.

Theorem bevalR_deterministic :
  forall Sigma e v1 v2,
    Sigma |-b e ⇓ v1 ->
    Sigma |-b e ⇓ v2 ->
    v1 = v2.
Proof.
Admitted.