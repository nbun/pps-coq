(* Chapter 2.2.3 *)

Require Import ZArith Lists.List.
Import ListNotations.

Definition ID := nat.

Inductive Val : Type :=
  | VInt  : nat -> Val
  | VBool : bool -> Val.

Definition Context := list (ID * Val).

Fixpoint lookup (Sigma : Context) (i : ID) : option Val :=
  match Sigma with
  | []          => None
  | (k,v) :: ps => if (k =? i) then Some v
                              else lookup ps i
  end.

Fixpoint replace (Sigma : Context) (i : ID) (v' : Val) : Context * bool :=
  match Sigma with
  | []          => ([], false)
  | (k,v) :: ps => if (k =? i) then ((k,v') :: ps, true)
                  else let (Sigma', b) := replace ps i v'
                        in ((k,v) :: Sigma', b)
  end.

Definition add (Sigma : Context) (i : ID) (v : Val) : Context :=
  let (Sigma', b) := replace Sigma i v
   in if b then Sigma'
           else (i, v) :: Sigma.
 
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
| While : Exp -> S   -> S
(* >>>>>>>>>>>>>>>>>>>>> *)
| For   : S   -> Exp -> S -> S -> S.
(* <<<<<<<<<<<<<<<<<<<<< *)

Notation "V ::= E" := (Ass V E) (at level 60).
Notation "S1 ;; S2" := (Seq S1 S2) (at level 80, right associativity).
Notation "'If' E 'Then' S1 'Else' S2" := (If E S1 S2) (at level 80, right associativity).
Notation "'While' E 'Do' S" := (While E S) (at level 80, right associativity).
Notation "'For' ( InitS ; TestS ; UpdS ) S" := (For InitS TestS UpdS S) (at level 80, right associativity). 

Reserved Notation "<| S , o |> --> <| S' , o' |>".
Inductive step : S -> Context -> S -> Context -> Prop :=
| SAss : forall o o' v e w,
    o |- e ::: w ->
    o' = (add o v w) ->
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
(* >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>> *)
| SFor: forall iS tS uS S o,
    <| For (iS ; tS ; uS) S, o |> --> <| iS ;; While tS Do (S ;; uS), o |>
(* <<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<< *)
where "<| S , o |> --> <| S' , o' |>" := (step S o S' o').

Definition j := Var 0. Definition n := Var 1. Definition u := Var 2.
Definition v := Var 3. Definition w := Var 4.

Definition P :=
  j ::= Num (VInt 1);;
  n ::= Num (VInt 3);;
  u ::= Num (VInt 1);;
  v ::= Num (VInt 1);;
  w ::= Num (VInt 1);;
  While (Op j less n) Do (
    w ::= (Op u plus v);;
    u ::= v;;
    v ::= w;;
    j ::= (Op j plus (Num (VInt 1)))
  ).

Definition P2 :=
  Skip;;
  n ::= Num (VInt 3);;
  u ::= Num (VInt 1);;
  v ::= Num (VInt 1);;
  w ::= Num (VInt 1);;
  While (Op j less n) Do (
    w ::= (Op u plus v);;
    u ::= v;;
    v ::= w;;
    j ::= (Op j plus (Num (VInt 1)))
  ).

Definition Prop1 := <| P, [(0, VInt 0); (1, VInt 0); (2, VInt 0); (3, VInt 0);
                           (4, VInt 0)] |> -->
                    <| P2, [(0, VInt 1); (1, VInt 0); (2, VInt 0); (3, VInt 0);
                           (4, VInt 0)] |>.
Example e1 : Prop1.
Proof. repeat econstructor. Qed.

Definition P21 :=
  n ::= Num (VInt 3);;
  u ::= Num (VInt 1);;
  v ::= Num (VInt 1);;
  w ::= Num (VInt 1);;
  While (Op j less n) Do (
    w ::= (Op u plus v);;
    u ::= v;;
    v ::= w;;
    j ::= (Op j plus (Num (VInt 1)))
  ).

Definition P3 :=
  Skip;;
  u ::= Num (VInt 1);;
  v ::= Num (VInt 1);;
  w ::= Num (VInt 1);;
  While (Op j less n) Do (
    w ::= (Op u plus v);;
    u ::= v;;
    v ::= w;;
    j ::= (Op j plus (Num (VInt 1)))
  ).

Definition Prop2 := <| P21, [(0, VInt 1); (1, VInt 0); (2, VInt 0); (3, VInt 0);
                           (4, VInt 0)] |> -->
                    <| P3, [(0, VInt 1); (1, VInt 3); (2, VInt 0); (3, VInt 0);
                           (4, VInt 0)] |>.
Example e2 : Prop2.
Proof. repeat econstructor. Qed.

(* ... *)