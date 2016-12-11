(* Chapter 2.2.3 *)

Require Import BinNums ZArith EqNat Lists.List.
Import ListNotations.
Local Open Scope Z_scope.

Definition ID := Z.
Inductive Val : Type :=
  | VInt  : Z  -> Val
  | VBool : bool -> Val
  | Undefined : Val.

Definition Context := list (ID * Val).

Fixpoint lookup (Sigma : Context) (i : ID) : option Val :=
  match Sigma with
  | []          => None
  | (k,v) :: ps => if (k =? i) then Some v
                                    else lookup ps i
  end.

Definition add (Sigma : Context) (i : ID) (v : Val) : Context :=
  (i, v) :: Sigma.
 
Inductive Ops : Type :=
| plus : Ops
| sub  : Ops
| mult : Ops
| less  : Ops.

Inductive Exp : Type :=
  | Num : Val -> Exp
  | Var : ID  -> Exp
  | Op  : Exp -> Ops -> Exp -> Exp
  | Let : ID  -> Exp -> Exp -> Exp.

Reserved Notation "Sigma '|-' e ':::' v" (at level 40).
Inductive eval (Sigma : Context) : Exp -> Val -> Prop :=
  | EvNum  : forall n, Sigma |- (Num n) ::: n
  
  | EvVar  : forall x v,
               lookup Sigma x = Some v ->
               Sigma |- (Var x) ::: v
               
  | EvPlus : forall e1 e2 v1 v2 v,
               Sigma |- e1 ::: (VInt v1) ->
               Sigma |- e2 ::: (VInt v2) ->
               v = v1 + v2 ->
               Sigma |- (Op e1 plus e2) ::: (VInt v)
                                       
   | EvSub : forall e1 e2 v1 v2 v,
               Sigma |- e1 ::: (VInt v1) ->
               Sigma |- e2 ::: (VInt v2) ->
               v = v1 - v2 ->
               Sigma |- (Op e1 sub e2) ::: (VInt v)              
                                       
  | EvMult : forall e1 e2 v1 v2 v,
               Sigma |- e1 ::: (VInt v1) ->
               Sigma |- e2 ::: (VInt v2) ->
               v = v1 * v2 ->
               Sigma |- (Op e1 mult e2) ::: (VInt v)
                                       
  | EvLess  : forall e1 e2 v1 v2,
               Sigma |- e1 ::: (VInt v1) ->
               Sigma |- e2 ::: (VInt v2) ->
               v1 < v2 ->
               Sigma |- (Op e1 less e2) ::: (VBool true)
                                       
  | EvLet  : forall Sigma' e1 e2 v1 v2 x,
               Sigma  |- e1 ::: v1 ->
               Sigma' = add Sigma x v1 ->
               Sigma' |- e2 ::: v2 -> 
               Sigma  |- (Let x e1 e2) ::: v2
  where "Sigma '|-' e ':::' v" := (eval Sigma e v).

Inductive S : Type :=
| Skip  : S
| Ass   : Exp -> Exp -> S
| Seq   : S   -> S   -> S
| If    : Exp -> S   -> S -> S
| While : Exp -> S   -> S.

Notation "V ::= E" := (Ass V E) (at level 60).
Notation "S1 ;; S2" := (Seq S1 S2) (at level 80, right associativity).
Notation "'If' E 'Then' S1 'Else' S2" := (If E S1 S2) (at level 80, right associativity).
Notation "'While' E 'Do' S" := (While E S) (at level 80, right associativity).

Reserved Notation "<| S , o |> --> <| S' , o' |>".
Inductive step : S -> Context -> S -> Context -> Prop :=
| SAss : forall o v e w,
    o |- e ::: w ->
    let o' := (add o v w) in
    <| (Var v) ::= e, o |> --> <| Skip, o' |>

| SSeqk : forall S o, <| Skip ;; S, o |> --> <| S, o |>

| SSeq : forall S S1 S2 o o',
    <| S1,      o |> --> <| S2,      o' |> ->
    <| S1 ;; S, o |> --> <| S2 ;; S, o' |>

| SIfT : forall b S1 S2 o,
    o |- b ::: (VBool true) ->
    <| If b Then S1 Else S2, o |> --> <| S1, o |>
                                             
| SIfF : forall b S1 S2 o,
    o |- b ::: (VBool false) ->
    <| If b Then S1 Else S2, o |> --> <| S2, o |>
   
| SWT : forall b S o,
    o |- b ::: (VBool true) ->
    <| While b Do S, o |> --> <| S ;; While b Do S, o |>

| SWF : forall b S o,
    o |- b ::: (VBool false) ->
    <| While b Do S, o |> --> <| Skip, o |>

where "<| S , o |> --> <| S' , o' |>" := (step S o S' o').

Definition P := If (Op (Var 0) less (Num (VInt 0)))
                   Then ((Var 0) ::= (Op (Num (VInt 0)) sub (Var 0)))
                   Else Skip. 

Definition P2 :=  ((Var 0) ::= (Op (Num (VInt 0)) sub (Var 0))).

Definition Prop1 := <| P, [(0, VInt (-42))] |> -->
                    <| P2, [(0, VInt (-42))] |>.
Definition Prop2 := <| P2, [(0, VInt (-42))] |> -->
                    <| Skip, [(0, VInt 42); (0, VInt (-42))] |>.

Example e : Prop1 /\ Prop2.
Proof. repeat econstructor. Qed.
