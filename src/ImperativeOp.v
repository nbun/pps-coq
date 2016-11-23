(* Chapter 3.1.1 folgende *)

Require Import EqNat Lists.List.
Import ListNotations.

Definition Ref := nat.

Inductive Ty : Type :=
  | Int  : Ty
  | Bool : Ty.

Inductive Lang : Type := C | Java.

Inductive Val : Type :=
  | VInt  : nat  -> Val
  | VBool : bool -> Val
  | Undefined : Val.

Definition newVarVal (L : Lang) (T : Ty) : Val :=
  match L, T with
  | Java, Int  => VInt 0
  | Java, Bool => VBool false
  | C,    _    => Undefined
  end.

Definition Name := nat.

Inductive EnvEntry : Type :=
  | VarType : Ref -> Ty  -> EnvEntry
  | Const   : Ty  -> Val -> EnvEntry.

Definition Env := list (Name * EnvEntry).

Definition Memory := list (Ref * Val).

Fixpoint envLookup (E : Env) (n : Name) : option EnvEntry :=
  match E with
  | []           => None
  | (k, v) :: es => if (beq_nat n k) then Some v else envLookup es n
  end.

Definition envAdd (E : Env) (n : Name) (v : (EnvEntry)) : Env :=
  (n, v) :: E.

Fixpoint memLookup (M : Memory) (r : Ref) : Val :=
  match M with
  | [] => Undefined
  | (k, v) :: ms => if (beq_nat r k) then v else memLookup ms r
  end.
 
Definition memAdd (M : Memory) (r : Ref) (v : Val) : Memory :=
  (r, v) :: M.

Fixpoint isFree (M : Memory) (r : Ref) : bool :=
  match M with
  | []          => true
  | (s,_) :: ms => if (beq_nat r s) then false else (isFree ms r)
  end.

Definition free (M : Memory) : Ref :=
  match M with
  | [] => 0
  | (r,_) :: _ => r + 1
  end.

Inductive Ops : Type :=
  | plus : Ops
  | mult : Ops
  | neq  : Ops.

Inductive Exp : Type :=
  | Num    : Val  -> Exp
  | Var    : Name -> Exp
  | Op     : Exp  -> Ops  -> Exp -> Exp.

Reserved Notation "EM '|-R' x ':::' v" (at level 40).
Inductive evalR : (Env * Memory) -> Exp -> Val -> Prop :=
  | EvVarR  : forall E M x l T v,
               envLookup E x = Some (VarType l T) ->
               memLookup M l = v ->
               (E,M) |-R (Var x) ::: v
              
  | EvNumR  : forall E M n, (E,M) |-R (Num n) ::: n
  
  | EvPlusR : forall E M e1 e2 v1 v2 v,
               (E,M) |-R e1 ::: (VInt v1) ->
               (E,M) |-R e2 ::: (VInt v2) -> 
               v = VInt (v1 + v2) ->
               (E,M) |-R (Op e1 plus e2) ::: v
               
  | EvMultR : forall E M e1 e2 v1 v2 v,
               (E,M) |-R e1 ::: (VInt v1) ->
               (E,M) |-R e2 ::: (VInt v2) -> 
               v = VInt (v1 * v2) ->
               (E,M) |-R (Op e1 mult e2) ::: v
               
  | EvNeqTR : forall E M e1 e2 v1 v2,
               (E,M) |-R e1 ::: (VInt v1) ->
               (E,M) |-R e2 ::: (VInt v2) ->
               v1 <> v2 ->
               (E,M) |-R (Op e1 neq e2) ::: (VBool true)
                
  | EvNeqFR : forall E M e1 e2 v1 v2,
               (E,M) |-R e1 ::: (VInt v1) ->
               (E,M) |-R e2 ::: (VInt v2) ->
               v1 = v2 ->
               (E,M) |-R (Op e1 neq e2) ::: (VBool false)
               
  | EvConstR: forall E M x T v,
                envLookup E x = Some (Const T v)  ->
                (E,M) |-R (Var x) ::: v

  where "EM '|-R' x ':::' v" := (evalR EM x v).

Reserved Notation "EM '|-L' x ':::' v" (at level 40).
Inductive evalL : (Env * Memory) -> Exp -> Ref -> Prop :=
  | EvVarL : forall E M x l T,
              envLookup E x = Some (VarType l T) ->
              (E,M) |-L (Var x) ::: l

  where "EM '|-L' x ':::' v" := (evalL EM x v).

Section Command.

  Inductive Cmnd : Type :=
    | Ass    : Exp  -> Exp  -> Cmnd
    | Decl   : Ty   -> Name -> Cmnd
    | DeclC  : Ty   -> Name -> Val  -> Cmnd
    | Seq    : Cmnd -> Cmnd -> Cmnd
    | If     : Exp  -> Cmnd -> Cmnd -> Cmnd
    | While  : Exp  -> Cmnd -> Cmnd.

  Notation "T 'var'   N" := (Decl T N) (at level 60).
  Notation "T 'const' N :=: V" := (DeclC T N V) (at level 60).
  Notation "E1 ::= E2" := (Ass E1 E2) (at level 60).
  Notation "C1 ;; C2" := (Seq C1 C2) (at level 80, right associativity).
  Notation "'If' ( B ) C1 'Else' C2" := (If B C1 C2) (at level 80, right associativity).
  Notation "'While' ( B ) C1" := (While B C1) (at level 80, right associativity).

  Reserved Notation "EM '{{' a '}}' Em'" (at level  40).
  Inductive eval : (Env * Memory) -> Cmnd -> (Env * Memory) -> Prop :=

    | EvDecl  : forall E M T x L,
                  let l  := free M in
                  let E' := envAdd E x (VarType l T) in
                  let M' := memAdd M l (newVarVal L T)
                   in (E,M) {{Decl T x}} (E', M')

    | EvDeclC : forall E M T x n,
                  let E' := envAdd E x (Const T n)
                   in (E,M) {{DeclC T x n}} (E', M)

    | EvAss   : forall E M e1 e2 l v,
                  (E,M) |-L e1 ::: l ->
                  (E,M) |-R e2 ::: v ->
                  let M' := memAdd M l v
                   in (E,M) {{Ass e1 e2}} (E, M')

    | EvSeq   : forall E M E' M' E'' M'' S1 S2,
                  (E,M)   {{S1}} (E',M')   ->
                  (E',M') {{S2}} (E'',M'') ->
                  (E,M)   {{S1;;S2}} (E'',M'')
                
    | EvIfT   : forall E M E' M' B S1 S2,
                  (E,M) |-R B ::: VBool true ->
                  (E,M) {{S1}} (E',M') ->
                  (E,M) {{If (B) S1 Else S2}} (E',M')
  
    | EvIfF   : forall E M E' M' B S1 S2,
                  (E,M) |-R B ::: VBool false ->
                  (E,M) {{S2}} (E',M') ->
                  (E,M) {{If (B) S1 Else S2}} (E',M')
    
    | EvWhileF : forall E M B S,
                   (E,M) |-R B ::: VBool false ->
                   (E,M) {{While (B) S}} (E,M)
    
    | EvWhileT : forall E M E' M' B S,
                   (E,M) |-R B ::: VBool true ->
                   (E,M) {{S;; While (B) S}} (E',M') ->
                   (E,M) {{While (B) S}} (E,M')
                   
    where "EM '{{' a '}}' EM'" := (eval EM a EM').
    
  Definition P :=
    Int const 0 :=: (VInt 1);;
    Int  var 1;; 
    Bool var 2;;
    (Var 1) ::= Num (VInt 0);;
    
    While (Op (Var 1) neq  (Num (VInt 1)))
      (Var 1) ::= (Op (Var 1) plus (Var 0)).

  Definition E := [(2, VarType 1 Bool);
                   (1, VarType 0 Int);
                   (0, Const Int (VInt 1))].

  Definition M := (* [(0, VInt 1); (1, VBool false)]. 
                     Speicherwerte werden neu angelegt, statt überschrieben zu werden *)
     [(0, VInt 1); (0, VInt 0); (1, VBool false); (0, VInt 0)].
     
   Example e : ([],[]) {{P}} (E,M).
   Proof. eapply EvSeq.
     - apply EvDeclC.
     - eapply EvSeq.
       * apply EvDecl with (L := Java).
       * eapply EvSeq.
         + apply EvDecl with (L := Java).
         + eapply EvSeq.
           -- apply EvAss.
              ** eapply EvVarL. reflexivity.
              ** apply EvNumR.
           -- eapply EvWhileT.
                ** eapply EvNeqTR.
                   ++ eapply EvVarR.
                      --- reflexivity.
                      --- reflexivity.
                   ++ apply EvNumR.
                   ++ unfold not. intros H. inversion H.
                ** eapply EvSeq.
                   ++ apply EvAss.
                      --- eapply EvVarL. reflexivity.
                      --- eapply EvPlusR.
                          *** eapply EvVarR. reflexivity. reflexivity.
                          *** eapply EvConstR. reflexivity.
                          *** reflexivity.
                   ++ eapply EvWhileF.
                     --- eapply EvNeqFR.
                         *** eapply EvVarR.
                             +++ reflexivity.
                             +++ reflexivity.
                         *** apply EvNumR.
                         *** reflexivity.
  Qed.
  
  Example e2 : ([],[]) {{P}} (E,M).
  Proof. eapply EvSeq.
    repeat econstructor. (* repeat econstructor. rechnet sehr lange, Endlosschleife? *)
    econstructor. econstructor. econstructor. econstructor.
    econstructor. econstructor. econstructor. econstructor.
    econstructor. econstructor. econstructor. econstructor.
    econstructor. econstructor. econstructor.
    auto.
    econstructor. econstructor. econstructor. econstructor.
    econstructor. econstructor. econstructor. econstructor.
    econstructor. simpl. Admitted. 
    (* Falsche Regel angewendet durch mehrdeutigen Var Konstruktor *)
    
End Command.