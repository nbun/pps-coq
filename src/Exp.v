Section Exp.

  Variable ID : Type.

  Inductive AExp : Type :=
    | ANum  : nat  -> AExp
    | AVar  : ID -> AExp
    | APlus  : AExp -> AExp -> AExp
    | AMinus : AExp -> AExp -> AExp
    | AMult  : AExp -> AExp -> AExp.

  Inductive BExp : Type :=
    | BTrue  : BExp
    | BFalse : BExp
    | BVar   : ID -> BExp
    | BEq  : AExp -> AExp -> BExp
    | BLe  : AExp -> AExp -> BExp
    | BNot : BExp -> BExp
    | BAnd : BExp -> BExp -> BExp.

End Exp.