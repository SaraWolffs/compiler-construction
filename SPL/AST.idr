module SPL.AST

%default total
%access public export

AtomLevel : Nat
AtomLevel = 0
NegLevel : Nat
NegLevel = 2
MultLevel : Nat
MultLevel = 4
PlusLevel : Nat
PlusLevel = 6
OrdLevel : Nat
OrdLevel = 8
EqLevel : Nat
EqLevel = 9
NotLevel : Nat
NotLevel = 10
BoolLevel : Nat
BoolLevel = 12
ConsLevel : Nat
ConsLevel = 14
TupLevel : Nat
TupLevel = 16
TopLevel : Nat
TopLevel = 18

data Id : (nTy:Type) -> Type where
  MkId : (name:String) -> (s:nTy) -> Id nTy

data Selector : (nTy:Type) -> Type where
  MkSel : (sel:String) -> (s:nTy) -> Selector nTy

data Field : (nTy:Type) -> Type where
  MkField : (sels:(List (Selector nTy))) -> Field nTy

data LOp  : Nat -> (nTy:Type) -> Type where
  Mult  : (s:nTy) -> LOp  MultLevel nTy
  Div   : (s:nTy) -> LOp  MultLevel nTy
  Mod   : (s:nTy) -> LOp  MultLevel nTy
  Plus  : (s:nTy) -> LOp  PlusLevel nTy
  Minus : (s:nTy) -> LOp  PlusLevel nTy
  Lt    : (s:nTy) -> LOp  OrdLevel  nTy
  Gt    : (s:nTy) -> LOp  OrdLevel  nTy
  Leq   : (s:nTy) -> LOp  OrdLevel  nTy
  Geq   : (s:nTy) -> LOp  OrdLevel  nTy
  Eq    : (s:nTy) -> LOp  EqLevel   nTy
  Neq   : (s:nTy) -> LOp  EqLevel   nTy
  And   : (s:nTy) -> LOp  BoolLevel nTy
  Or    : (s:nTy) -> LOp  BoolLevel nTy

data ROp  : Nat -> (nTy:Type) -> Type where
  Cons  : (s:nTy) -> ROp  ConsLevel nTy

data UnOp : Nat -> (nTy:Type) -> Type where
  Neg   : (s:nTy) -> UnOp NegLevel nTy
  Not   : (s:nTy) -> UnOp NotLevel nTy


data LitTy = Num | Str | Chr | Bol

ITyFromLitTy : LitTy -> Type
ITyFromLitTy Num = Nat
ITyFromLitTy Str = String
ITyFromLitTy Chr = Char
ITyFromLitTy Bol = Bool

data Expr : Nat -> (nTy:Type) -> Type where
  Lit       : {t:LitTy} -> (val:ITyFromLitTy t) -> (s:nTy) -> Expr (AtomLevel+k) nTy
  Nil       : (s:nTy) -> Expr (AtomLevel+k) nTy
  Var       : (vid:Id nTy) -> (field:Field nTy) -> (s:nTy) -> Expr (AtomLevel+k) nTy
  ParenExpr : (wrapped:Expr TopLevel nTy) -> (s:nTy) -> Expr (AtomLevel+k) nTy
  PairExpr  : (left:Expr TopLevel nTy) -> (right:Expr TopLevel nTy) -> 
              (s:nTy) -> Expr (AtomLevel+k) nTy
  FunCall   : (fid:Id nTy) -> (args:List (Expr TopLevel nTy)) -> 
              (s:nTy) -> Expr (AtomLevel+k) nTy
  UnOpExpr  : (op:UnOp n nTy) -> (e:Expr n nTy) -> (s:nTy) -> Expr (n+k) nTy
  LOpExpr   : (l:Expr (S n) nTy) -> (op:LOp n nTy) -> (r:Expr n nTy) ->
              Expr (S n + k) nTy
  ROpExpr   : (l:Expr n nTy) -> (op:ROp n nTy) -> (r:Expr (S n) nTy) ->
              Expr (S n + k) nTy

data Stmt : (nTy:Type) -> Type where
  IfElse    : (cond:Expr TopLevel nTy) -> Stmt nTy -> Maybe (Stmt nTy) -> 
              (s:nTy) -> Stmt nTy
  While     : (cond:Expr TopLevel nTy) -> Stmt nTy -> (s:nTy) -> Stmt nTy
  Assign    : (vid:Id nTy) -> (field:Field nTy) -> (rval:Expr TopLevel nTy) -> 
              (s:nTy) -> Stmt nTy
  ExprStmt  : (e:Expr TopLevel nTy) -> (s:nTy) -> Stmt nTy
  Return    : (val:Maybe (Expr TopLevel nTy)) -> (s:nTy) -> Stmt nTy
  Compound  : (stmts:List (Stmt nTy)) -> (s:nTy) -> Stmt nTy

data TyLit = SInt | SBool | SChar | SStr

-- Declared Type
data DeclTy : (nTy:Type) -> Type where
  BasicType : (tname:TyLit) -> (s:nTy) -> DeclTy nTy
  ListType  : (el:DeclTy nTy) -> (s:nTy) -> DeclTy nTy
  TypePair  : (l:DeclTy nTy) -> (r:DeclTy nTy) -> (s:nTy) -> DeclTy nTy
  TypeId    : (tid:Id nTy) -> (s:nTy) -> DeclTy nTy

data RetTy : (nTy:Type) -> Type where
  ValType   : (t:DeclTy nTy) -> RetTy nTy
  VoidType  : (s:nTy) -> RetTy nTy


infixr 0 ~>

data FuncTy : (nTy:Type) -> Type where
  (~>) : List (DeclTy nTy) -> RetTy nTy -> (s:nTy) -> FuncTy nTy

data FuncDecl : (nTy:Type) -> Type where
  MkFuncDecl : (fid:Id nTy) -> (params:List (Id nTy)) -> (t:Maybe (FuncTy nTy)) ->
               (s:nTy) -> FuncDecl nTy
  

data VarDef : (nTy:Type) -> Type where
  NewVar : (t:Maybe (DeclTy nTy)) -> (vid:Id nTy) -> (rval:Expr TopLevel nTy) -> 
              (s:nTy) -> VarDef nTy

data FuncBody : (nTy:Type) -> Type where
  MkFuncBody : (locals:List (VarDef nTy)) -> (stmts:List (Stmt nTy)) ->
               (s:nTy) -> FuncBody nTy

data FuncDef : (nTy:Type) -> Type where
  NewFunc : (header:FuncDecl nTy) -> (body:FuncDecl nTy) -> (s:nTy) -> FuncDef nTy

SplDef : (nTy:Type) -> Type
SplDef nTy = Either (VarDef nTy) (FuncDef nTy)

Spl : (nTy:Type) -> Type
Spl nTy = List (SplDef nTy)
