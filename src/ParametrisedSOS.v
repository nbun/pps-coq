Require Import List.
Require Import Nat.

Set Implicit Arguments.

Section Context.

  Import ListNotations.
  
  Variable ID : Type.
  Variable Val : Type.
  Variable eqID : ID -> ID -> bool.
  Notation "i '==' j" := (eqID i j) (at level 80, right associativity).

  Definition Context := list (ID * Val).

  Fixpoint lookup (Sigma : Context) (i : ID) : option Val :=
    match Sigma with
    | []          => None
    | (k,v) :: ps => if (k == i) then Some v
                    else lookup ps i
    end.

  Fixpoint update (Sigma : Context) (i : ID) (v' : Val) : Context :=
    match Sigma with
    | []          => [(i,v')]
    | (k,v) :: ps => if (k == i) then (k,v') :: ps
                    else (k,v) :: update ps i v'
    end.

End Context.

Reserved Notation "<| S , o |> --> <| S' , o' |>".

Section SOS.

  Variable BExp : Type.
  Variable Exp : Type.

  Inductive S_ : Type :=
  | Skip  : S_
  | Ass   : nat -> Exp -> S_
  | Seq   : S_   -> S_   -> S_
  | IIf    : BExp -> S_   -> S_ -> S_
  | WWhile : BExp -> S_  -> S_.

  Notation "V ::= E" := (Ass V E) (at level 60).
  Notation "S1 ;; S2" := (Seq S1 S2) (at level 80, right associativity).
  Notation "'If' E 'Then' S1 'Else' S2" := (IIf E S1 S2) (at level 200, right associativity).
  Notation "'While' E 'Do' S" := (WWhile E S) (at level 200, right associativity).
  
  Section Step.

    Variable Val : Type.

    Definition SOS_Context := Context nat Val.
    Definition SOS_replace := @update nat Val eqb.
    Definition SOS_lookup := @lookup nat Val eqb.

    Notation "o [ var ↦ val ]" := (SOS_replace o var val) (at level 80, right associativity).

    Section stepAsRelation.

      Variable IExp : Exp -> SOS_Context -> Val -> Prop.
      Variable IBExp : BExp -> SOS_Context -> bool -> Prop.

      Reserved Notation "<| S , o |> --> <| S' , o' |>".

      Inductive stepP : S_ -> SOS_Context -> S_ -> SOS_Context -> Prop :=
      | SAss : forall o v e val,
          IExp e o val ->
          <| v ::= e, o |> --> <| Skip, o [v ↦ val] |>
      | SSeqk : forall S o,
          <| Skip ;; S, o |> --> <| S, o |>
      | SSeq : forall S S1 S2 o o',
          <| S1,      o |> --> <| S2,      o' |> ->
          <| S1 ;; S, o |> --> <| S2 ;; S, o' |>
      | SIfT : forall b S1 S2 o,
          IBExp b o true ->
          <| If b Then S1 Else S2, o |> --> <| S1, o |>
      | SIfF : forall b S1 S2 o,
          IBExp b o false ->  
          <| If b Then S1 Else S2, o |> --> <| S2, o |>
      | SWT : forall b S o,
          IBExp b o true ->
          <| While b Do S, o |> --> <| S ;; While b Do S, o |>
      | SWF : forall b S o,
          IBExp b o false ->  
          <| While b Do S, o |> --> <| Skip, o |>
      where "<| S , o |> --> <| S' , o' |>" := (stepP S o S' o').

    End stepAsRelation.

    Section stepAsFunction.

      Variable iexp : Exp -> SOS_Context -> option Val.
      Variable ibexp : BExp -> SOS_Context -> option bool.
      
      Fixpoint stepF (stm: S_) (c: SOS_Context) : option (S_ * SOS_Context) :=
        match stm with
        | Ass v e => match iexp e c with
                    | None => None
                    | Some val => Some (Skip, c [ v ↦ val ])
                    end
        | Seq Skip stm => Some (stm, c)
        | Seq s1 s2 => match stepF s1 c with
                      | None => None
                      | Some (s',c') => Some (s' ;; s2, c')
                      end
        | IIf b s1 s2 => match ibexp b c with
                        | Some true => Some (s1, c)
                        | Some false => Some (s2, c)
                        | _ => None
                        end
        | WWhile b s1 => match ibexp b c with
                        | Some true => Some (Seq s1 (WWhile b s1), c)
                        | Some false => Some (Skip, c)
                        | _ => None
                        end
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

      Definition terminating_computation (prog : S_) (c0 : SOS_Context): Prop :=
        exists i, option_map fst (nth_error (computation (S i) prog c0) i) = Some Skip.
      
      Definition nonTerminating_computation (prog : S_) (c0 : SOS_Context): Prop :=
        forall i, option_map fst (nth_error (computation (S i) prog c0) i) <> Some Skip.

    End stepAsFunction.

  End Step.

End SOS.

Section ExampleA.

  Inductive ArithE : Type :=
  | Num : nat -> ArithE
  | Var : nat -> ArithE
  | Op  : ArithE -> Ops -> ArithE -> ArithE
  with Ops : Type :=
       | plus : Ops
       | sub  : Ops
       | mult : Ops.

  Reserved Notation "Sigma '|-' e ':n:' v" (at level 40).
  Reserved Notation "Sigma '|-' e ':b:' v" (at level 40).
  
  Section ArithInterpretation.

    Inductive aevalR : ArithE -> SOS_Context nat -> nat -> Prop :=
    | EvNum  : forall Sigma n, Sigma |- Num n :n: n
    | EvVar  : forall Sigma x v,
        SOS_lookup Sigma x = Some v ->
        Sigma |- Var x :n: v
    | EvPlus : forall Sigma e1 e2 v1 v2 v,
        Sigma |- e1 :n: v1 ->
        Sigma |- e2 :n: v2 ->
        v = v1 + v2 ->
        Sigma |- Op e1 plus e2 :n: v
    | EvSub : forall Sigma e1 e2 v1 v2 v,
        Sigma |- e1 :n: v1 ->
        Sigma |- e2 :n: v2 ->
        v = v1 - v2 ->
        Sigma |- Op e1 sub e2 :n: v              
    | EvMult : forall Sigma e1 e2 v1 v2 v,
        Sigma |- e1 :n: v1 ->
        Sigma |- e2 :n: v2 ->
        v = v1 * v2 ->
        Sigma |- Op e1 mult e2 :n: v
    where "Sigma '|-' e ':n:' v" := (aevalR e Sigma v).

    Fixpoint aevalF (e : ArithE) (c0 : SOS_Context nat) : option nat :=
      match e with
      | Num n => Some n
      | Var x => SOS_lookup c0 x
      | Op e1 op e2 =>
        match aevalF e1 c0, aevalF e2 c0 with
        | Some v1, Some v2 =>
          Some (match op with
                | plus => v1 + v2
                | mult => v1 * v2
                | sub => v1 - v2
                end)
        | _,_ => None
        end
      end.

  End ArithInterpretation.

  Notation "Sigma '|-' e ':n:' v" := (aevalR e Sigma v).

  Inductive BoolE : Type :=
  | TT : BoolE
  | FF : BoolE
  | Less : ArithE -> ArithE -> BoolE.

  Section BoolInterpretation.

    Inductive bevalR : BoolE -> SOS_Context nat -> bool -> Prop :=
    | EvT : forall Sigma, Sigma |- TT :b: true
    | EvF : forall Sigma, Sigma |- FF :b: false
    | EvLess : forall Sigma e1 e2 v1 v2 b,
        Sigma |- e1 :n: v1 ->
        Sigma |- e2 :n: v2 ->
        b = leb v1 v2 ->
        Sigma |- Less e1 e2 :b: b
    where "Sigma '|-' e ':b:' v" := (bevalR e Sigma v).

    Fixpoint bevalF (be : BoolE) (c0 : SOS_Context nat) : option bool :=
      match be with
      | TT => Some true
      | FF => Some false
      | Less e1 e2 =>
        match aevalF e1 c0, aevalF e2 c0 with
        | Some v1, Some v2 => Some (leb v1 v2)
        | _,_ => None
        end
      end.

  End BoolInterpretation.

  Notation "Sigma '|-' e ':n:' v" := (bevalR e Sigma v).
    

  Definition P1 : S_ BoolE ArithE := Ass BoolE 0 (Num 1).

  Definition P2 : S_ BoolE ArithE :=
    IIf (Less (Var 0) (Num 42))
        (Ass BoolE 0 (Op (Num 42) plus (Var 0)))
        (Skip BoolE ArithE).

  Definition C2 : SOS_Context nat := cons (0, 31) nil.

  Eval compute in (computation aevalF bevalF 1 P1 nil).
  Eval compute in (computation aevalF bevalF 2 P2 C2).

  Lemma isTerminatingP1 :
    terminating_computation aevalF bevalF P1 nil.
  Proof.
    unfold terminating_computation.
    exists 0.
    simpl.
    reflexivity.
  Qed.

  Lemma isNotTerminatingP2 :
    ~ terminating_computation aevalF bevalF P2 nil.
  Proof.
    unfold terminating_computation.
    intro H.
    destruct H.
    destruct x; simpl in H.
    - inversion H.
    - inversion H.
  Qed.

  Lemma isTerminatingP2 :
    terminating_computation aevalF bevalF P2 C2.
  Proof.
    unfold terminating_computation.
    exists 1.
    simpl.
    reflexivity.
  Qed.
      
  Definition P3 : S_ BoolE ArithE :=  Ass BoolE 0 (Op (Num 42) plus (Var 0)).
  Definition C3 : SOS_Context nat := cons (0,73) nil.

  Notation "<| S , o |> --> <| S' , o' |>" := (stepP aevalR bevalR S o S' o').

  Definition Prop1 := <| P2, C2 |> -->
                      <| P3, C2 |>.
  Definition Prop2 := <| P3, C2 |> -->
                      <| Skip BoolE ArithE, C3 |>.

  Example e : Prop1 /\ Prop2.
  Proof.
    split; unfold Prop1, Prop2.
    - unfold P2.
      apply SIfT.
      apply EvLess with (v1 := 31) (v2 := 42).
      * apply EvVar. reflexivity.
      * apply EvNum.
      * simpl. reflexivity.
    - unfold P3.
      apply SAss with (val := 73).
      apply EvPlus with (v1 := 42) (v2 := 31).
      * apply EvNum.
      * apply EvVar. unfold C2. reflexivity.
      * reflexivity.
  Qed.

End ExampleA.
    
