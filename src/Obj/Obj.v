Require Import PPS.Env.
Require Import List.

Set Implicit Arguments.

Section ObjModell.

  Inductive Ref :=
  | RefAddr : nat -> Ref
  | RefNull : Ref.

  Definition ref_eqb (r1 r2 : Ref) : bool :=
    match r1, r2 with
    | RefAddr n1, RefAddr n2 => Nat.eqb n1 n2
    | _,_ => false
    end.

  Inductive Val : Type :=
  | VInt      : nat -> Val
  | VRef      : Ref -> Val
  | Undefined : Val.

  Definition Name := nat.
  Definition ClassName := nat.

  Inductive Ty : Type :=
  | Int     : Ty
  | RefT    : Ty -> Ty
  | ClassTy : ClassName -> Ty.

  Inductive Attribute := Attr : Ty -> Name -> Attribute.

  Definition attName (att : Attribute) :=
    match att with
    | Attr _ name => name
    end.
  
  Inductive Method := Mthd : Ty -> Name -> list (Ty * Name) -> Method.

  Inductive EnvEntry {Env : Type} : Type :=
  | VarE : Ref -> Ty -> EnvEntry
  | ClassE : ClassName -> list Attribute -> list Method -> Env -> EnvEntry.

  Inductive Env :=
  | env : listMap Name (@EnvEntry Env) -> Env.

  Definition Memory := totalMap Ref Val.

  Reserved Notation "E '|-l' val" (at level 80).

  Notation "E ; x" := (let 'env E' := E in
                       env (union E' (cons x nil))) (at level 40).

  Section EnvRelation.
    
    Inductive Lookup : Env -> (Name * @EnvEntry Env) -> Prop :=
    | LAxiom : forall E x beta,
        E; (x, beta) |-l (x, beta)
    | LRule : forall E x y beta gamma,
        E |-l (x,beta) ->
        E; (y, gamma) |-l (x, beta)
    where "E '|-l' val" := (Lookup E val).
      
  End EnvRelation.
  Notation "E '|-l' val" := (Lookup E val).

  Section Exp.

    Inductive Exp :=
    | Var : Ty -> Name -> Exp
    | Num : nat -> Exp
    | Clss : ClassName -> Exp
    | AttrAcc : Name -> Name -> Exp.

  End Exp.

  Reserved Notation "EM '|-R' e ⇓ v" (at level 80).
  Section EvalR.

    Fixpoint index_elem' (A : Type) (eqA : A -> A -> bool)
             (x : A) (xs : list A) (n : nat) : option nat :=
      match xs with
      | nil => None
      | cons y ys => if eqA x y then Some n else index_elem' eqA x ys (S n)
      end.

    Definition index_elem (A : Type) (eqA : A -> A -> bool)
               (x : A) (xs : list A) : option nat :=
      index_elem' eqA x xs 0.

    Inductive evalR : (Env * Memory) -> Exp -> Val -> Prop :=
      
    | EvVarR  : forall E M x l tau val,
        E |-l (x, VarE l tau) ->
        M l = val ->
        (E,M) |-R (Var tau x) ⇓ val

    | EvNumR  : forall E M n, (E,M) |-R Num n ⇓ VInt n

    | EvAttrR : forall E M x aName cName atts ms E' l l' l__ref i,
        E |-l (x, VarE (RefAddr l) (ClassTy cName)) ->
        E |-l (cName, ClassE cName atts ms E') ->
        Some i = index_elem Nat.eqb aName (map attName atts) ->
        VInt l' = M (RefAddr l) ->
        VRef l__ref = M (RefAddr (l' + i - 1)) ->
        (E, M) |-R AttrAcc x aName ⇓ M l__ref

    where "EM '|-R' e ⇓ v" := (evalR EM e v).

  End EvalR.
  Notation "EM '|-R' e ⇓ v" := (evalR EM e v).

  Reserved Notation "EM '|-L' e ⇓ v" (at level 80).
  Section EvalL.
    
    Inductive evalL : (Env * Memory) -> Exp -> Ref -> Prop :=
    | EvVarL : forall E M x l tau,
        E |-l (x, VarE l tau) ->
        (E,M) |-L (Var tau x) ⇓ l

    | EvAttrL : forall E M x aName cName atts ms E' l l' i,
        E |-l (x, VarE (RefAddr l) (ClassTy cName)) ->
        E |-l (cName, ClassE cName atts ms E') ->
        Some i = index_elem Nat.eqb aName (map attName atts) ->
        VInt l' = M (RefAddr l) ->
        (E, M) |-L AttrAcc x aName ⇓ RefAddr (l' + i - 1)
        
  where "EM '|-L' e ⇓ v" := (evalL EM e v).

  End EvalL.
  Notation "EM '|-L' e ⇓ v" := (evalL EM e v).

  Section Stm.

    Inductive Stm : Type :=
    | Ass    : Exp -> Exp -> Stm
    | Decl   : Ty -> Name -> Stm
    | DeclC  : ClassName -> list Attribute -> list Method -> Stm
    | DeclO  : ClassName -> Name -> Stm
    | Seq    : Stm -> Stm -> Stm.
  
    Reserved Notation "'<' E '|' M '>' alpha '<' E' '|' M' '>'"
             (at level 40, E at level 39, M at level 39, M' at level 40,
              E' at level 39, alpha at level 39).
    Notation "M '[' var ↦ val ']'" := (updateTMap ref_eqb M var val)
                                        (at level 40, right associativity).

    Inductive IsFree : Ref -> Memory -> Prop :=
    | isFree : forall x M,
        M x = Undefined ->
        IsFree x M.

    Definition newVarVal (T : Ty) : Val :=
      match T with
      | Int => VInt 0
      | RefT _ => VRef RefNull
      | ClassTy _ => VRef RefNull
      end.

    Inductive eval : Env * Memory -> Stm -> Env * Memory -> Prop :=
    | EvDecl : forall E M l tau n,
        IsFree l M ->
        < E | M > Decl tau n < E; (n, VarE l tau) | M [l ↦ VInt 0] >

    | EvDeclC : forall E M cName atts ms,
        < E | M > DeclC cName atts ms < E; (cName, ClassE cName atts ms E) | M >

    | EvDeclO : forall E M cName x l,
        IsFree l M ->
        < E | M > DeclO cName x < E; (x, VarE l (ClassTy cName)) | M [l ↦ VRef RefNull] >

    | EvAssO : forall E M e1 x l l' ls cName atts ms E',
        E |-l (x, VarE l (ClassTy cName)) ->
        E |-l (cName, ClassE cName atts ms E') ->
        length ls = length atts - 1 ->
        Forall (fun l => IsFree l M) ls ->
        IsFree l' M ->
        let M' := fold_right (fun '(Attr ty _,l) acc =>
                                updateTMap ref_eqb acc l (newVarVal ty))
                             M
                             (combine atts ls) in
        < E | M > Ass e1 (Clss cName) < E | M' [l ↦ VRef l'] >

    | EvAss : forall E M e1 e2 l v,
        (E,M) |-L e1 ⇓ l ->
        (E,M) |-R e2 ⇓ v ->
        < E | M > Ass e1 e2 < E | M [l ↦ v] >

    | EvSeq : forall E M E' M' E'' M'' S1 S2,
        < E | M > S1 < E' | M' > ->
        < E' | M' > S2 < E'' | M'' > ->
        < E | M > Seq S1 S2 < E'' | M'' >

    where "'<' E '|' M '>' alpha '<' E' '|' M' '>'" := (eval (E,M) alpha (E',M')).
    
  End Stm.

End ObjModell.