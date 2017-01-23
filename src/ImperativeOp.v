(* Chapter 3.1.1 folgende *)

Require Import EqNat Lists.List.
Import ListNotations.

Definition Ref := nat.

Inductive Ty : Type :=
  | Int    : Ty
  | Float  : Ty
  | Double : Ty
  | Bool   : Ty.

Inductive Val : Type :=
  | VInt    : nat  -> Val
  | VFloat  : nat  -> Val
  | VDouble : nat  -> Val
  | VBool   : bool -> Val
  | Undefined : Val.

Definition newVarVal (T : Ty) : Val :=
  match T with
  | Int    => VInt 0
  | Float  => VFloat 0
  | Double => VDouble 0
  | Bool   => VBool false
  end.

Definition Name := nat.

Inductive EnvEntry : Type :=
  | VarType   : Ref -> Ty  -> EnvEntry
  | ConstType : Ty  -> Val -> EnvEntry.

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

Fixpoint memUpdate (M : Memory) (e : (Ref * Val)) : Memory :=
  match M, e with
  | [],          _     => []
  | (s,u) :: ms, (r,v) => if beq_nat r s then (r,v) :: ms 
                                         else (s,u) :: memUpdate ms e
  end.
  
Definition memAdd (M : Memory) (e : (Ref * Val)) : Memory :=
  match (find (beq_nat (fst e)) (map fst M)) with
  | None   => e :: M
  | Some _ => memUpdate M e
  end.
    

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
  | Const  : Name -> Exp
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
                envLookup E x = Some (ConstType T v)  ->
                (E,M) |-R (Const x) ::: v

  where "EM '|-R' x ':::' v" := (evalR EM x v).

Reserved Notation "EM '|-L' x ':::' v" (at level 40).
Inductive evalL : (Env * Memory) -> Exp -> Ref -> Prop :=
  | EvVarL : forall E M x l T,
              envLookup E x = Some (VarType l T) ->
              (E,M) |-L (Var x) ::: l

  where "EM '|-L' x ':::' v" := (evalL EM x v).

(* Command *)

Inductive Cmnd : Type :=
  | Ass    : Exp  -> Exp  -> Cmnd
  | Decl   : Ty   -> Name -> Cmnd
  | DeclC  : Ty   -> Name -> Val  -> Cmnd
  | Seq    : Cmnd -> Cmnd -> Cmnd
  | If     : Exp  -> Cmnd -> Cmnd -> Cmnd
  | While  : Exp  -> Cmnd -> Cmnd.

Notation "T 'var'   N"       := (Decl T N) (at level 60).
Notation "T 'const' N :=: V" := (DeclC T N V) (at level 60).
Notation "E1 ::= E2"         := (Ass E1 E2) (at level 60).
Notation "C1 ;; C2"          := (Seq C1 C2) (at level 80, right associativity).
Notation "'If' ( B ) C1 'Else' C2" := (If B C1 C2) (at level 80, right associativity).
Notation "'While' ( B ) C1"  := (While B C1) (at level 80, right associativity).

Reserved Notation "EM '{{' a '}}' Em'" (at level  40).
Inductive eval : (Env * Memory) -> Cmnd -> (Env * Memory) -> Prop :=
  | EvDecl  : forall E M T x,
                let l  := free M in
                let E' := envAdd E x (VarType l T) in
                let M' := memAdd M (l, (newVarVal T))
                 in (E,M) {{Decl T x}} (E', M')
  | EvDeclC : forall E M T x n,
                let E' := envAdd E x (ConstType T n)
                 in (E,M) {{DeclC T x n}} (E', M)

  | EvAss   : forall E M e1 e2 l v,
                (E,M) |-L e1 ::: l ->
                (E,M) |-R e2 ::: v ->
                let M' := memAdd M (l, v)
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
