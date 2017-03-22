Require Import PPS.Env.
Require Import Nat.

Set Implicit Arguments.

Reserved Notation "<| S , o |> --> <| S' , o' |>".

Section SOS.

  Variable BExp : Type.
  Variable Exp : Type.

  Inductive S_ : Type :=
  | SSkip  : S_
  | SAss   : nat -> Exp -> S_
  | SSeq   : S_   -> S_   -> S_
  | SIf    : BExp -> S_   -> S_ -> S_
  | SWhile : BExp -> S_  -> S_
  (* >>>>>>>>>>>>>>>>>>>>> *)
  | SFor   : S_ -> BExp -> S_ -> S_ -> S_.
  (* <<<<<<<<<<<<<<<<<<<<< *)

  Notation "V ::= E" := (SAss V E) (at level 60).
  Notation "S1 ;; S2" := (SSeq S1 S2) (at level 80, right associativity).
  Notation "'If' E 'Then' S1 'Else' S2" :=
    (SIf E S1 S2) (at level 200, right associativity).
  Notation "'While' E 'Do' S" := (SWhile E S) (at level 200, right associativity).
  Notation "'For' ( InitS ; TestS ; UpdS ) S" :=
    (SFor InitS TestS UpdS S) (at level 80, right associativity). 

  Section Step.

    Variable Val : Type.

    Definition SOS_Context := EnvironmentL nat Val.
    Definition SOS_replace := @update nat Val eqb.
    Definition SOS_lookup := @lookup nat Val eqb.

    Notation "o [ var ↦ val ]" := (SOS_replace o var val) (at level 80, right associativity).

    Section StepRelation.

      Variable IExp : Exp -> SOS_Context -> Val -> Prop.
      Variable IBExp : BExp -> SOS_Context -> bool -> Prop.

      Reserved Notation "<| S , o |> --> <| S' , o' |>".

      Inductive stepR : S_ -> SOS_Context -> S_ -> SOS_Context -> Prop :=
      | StAss : forall o v e val,
          IExp e o val ->
          <| v ::= e, o |> --> <| SSkip, o [v ↦ val] |>
      | StSeqSkip : forall S o,
          <| SSkip ;; S, o |> --> <| S, o |>
      | StSeq : forall S S1 S2 o o',
          <| S1,      o |> --> <| S2,      o' |> ->
          <| S1 ;; S, o |> --> <| S2 ;; S, o' |>
      | StIfT : forall b S1 S2 o,
          IBExp b o true ->
          <| If b Then S1 Else S2, o |> --> <| S1, o |>
      | StIfF : forall b S1 S2 o,
          IBExp b o false ->  
          <| If b Then S1 Else S2, o |> --> <| S2, o |>
      | StWT : forall b S o,
          IBExp b o true ->
          <| While b Do S, o |> --> <| S ;; While b Do S, o |>
      | StWF : forall b S o,
          IBExp b o false ->  
          <| While b Do S, o |> --> <| SSkip, o |>
      (* >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>> *)
      | StFor: forall iS tS uS S o,
          <| For (iS ; tS ; uS) S, o |> --> <| iS ;; While tS Do (S ;; uS), o |>
      (* <<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<< *)
      where "<| S , o |> --> <| S' , o' |>" := (stepR S o S' o').

    End StepRelation.

    Section StepFunction.

      Variable iexp : Exp -> SOS_Context -> option Val.
      Variable ibexp : BExp -> SOS_Context -> option bool.
      
      Fixpoint stepF (stm: S_) (c: SOS_Context) : option (S_ * SOS_Context) :=
        match stm with
        | SAss v e => match iexp e c with
                    | None => None
                    | Some val => Some (SSkip, c [ v ↦ val ])
                    end
        | SSeq SSkip stm => Some (stm, c)
        | SSeq s1 s2 => match stepF s1 c with
                      | None => None
                      | Some (s',c') => Some (s' ;; s2, c')
                      end
        | SIf b s1 s2 => match ibexp b c with
                        | Some true => Some (s1, c)
                        | Some false => Some (s2, c)
                        | _ => None
                        end
        | SWhile b s1 => match ibexp b c with
                        | Some true => Some (SSeq s1 (SWhile b s1), c)
                        | Some false => Some (SSkip, c)
                        | _ => None
                        end
        (* >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>> *)
        | SFor iS tS uS s => Some (iS ;; While tS Do s ;; uS, c)
        (* >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>> *)
        | _ => Some (stm,c)
        end.

      Fixpoint computation (fuel: nat) (prog : S_) (c0 : SOS_Context)
        : list (S_ * SOS_Context) :=
        match fuel with
        | 0 => nil
        | S n =>
          match stepF prog c0 with
          | None => nil
          | Some ((s,c) as v) => cons v (computation n s c)
          end
        end.

      Fixpoint nth (A : Type) (xs : list A) (n : nat) : option A :=
        match xs, n with
        | nil, _ => None
        | cons y ys, 0 => Some y
        | cons y ys, S n' => nth ys n'
        end.
        
      Definition terminating_computation (prog : S_) (c0 : SOS_Context): Prop :=
        exists i, option_map fst (nth (computation (S i) prog c0) i) = Some SSkip.
      
      Definition nonTerminating_computation (prog : S_) (c0 : SOS_Context): Prop :=
        forall i, option_map fst (nth (computation (S i) prog c0) i) <> Some SSkip.

    End StepFunction.

  End Step.

End SOS.

Module SOS_Notation.

  Notation "V ::= E" := (SAss _ V E) (at level 60).
  Notation "S1 ;; S2" := (SSeq S1 S2) (at level 80, right associativity).
  Notation "'If' E 'Then' S1 'Else' S2" := (SIf E S1 S2) (at level 200, right associativity).
  Notation "'While' E 'Do' S" := (SWhile E S) (at level 200, right associativity).
  Notation "'For' ( InitS ; TestS ; UpdS ) S" :=
    (SFor InitS TestS UpdS S) (at level 80, right associativity). 

End SOS_Notation.