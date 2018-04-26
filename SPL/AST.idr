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
  SNil      : (s:nTy) -> Expr (AtomLevel+k) nTy
  Var       : (vid:Id nTy) -> (field:Field nTy) -> (s:nTy) -> Expr (AtomLevel+k) nTy
  ParenExpr : (wrapped:Expr TopLevel nTy) -> (s:nTy) -> Expr (AtomLevel+k) nTy
  PairExpr  : (left:Expr TopLevel nTy) -> (right:Expr TopLevel nTy) -> 
              (s:nTy) -> Expr (AtomLevel+k) nTy
  FunCall   : (fid:Id nTy) -> (args:List (Expr TopLevel nTy)) -> 
              (s:nTy) -> Expr (AtomLevel+k) nTy
  UnOpExpr  : (op:UnOp n nTy) -> (e:Expr n nTy) -> (s:nTy) -> Expr (n+k) nTy
  LOpExpr   : (l:Expr (S n) nTy) -> (op:LOp n nTy) -> (r:Expr n nTy) ->
              (s:nTy) -> Expr (S n + k) nTy
  ROpExpr   : (l:Expr n nTy) -> (op:ROp n nTy) -> (r:Expr (S n) nTy) ->
              (s:nTy) -> Expr (S n + k) nTy

Atom : (nTy:Type) -> Type
Atom = Expr AtomLevel

Expression : (nTy:Type) -> Type
Expression = Expr TopLevel;

--increase slack

relax : Expr n nTy -> Expr (n+k) nTy
relax (Lit val s) = Lit val s
relax (SNil s) = SNil s
relax (Var vid field s) = (Var vid field s)
relax (ParenExpr wrapped s) = (ParenExpr wrapped s)
relax (PairExpr left right s) = (PairExpr left right s)
relax (FunCall fid args s) = (FunCall fid args s)
relax {k=d} (UnOpExpr {n} {k} op e   s) = rewrite sym (plusAssociative n k d) in (UnOpExpr op e   s) 
relax {k=d} (LOpExpr  {n} {k} l op r s) = rewrite sym (plusAssociative n k d) in (LOpExpr  l op r s)
relax {k=d} (ROpExpr  {n} {k} l op r s) = rewrite sym (plusAssociative n k d) in (ROpExpr  l op r s)

relax' : Expr n nTy -> Expr (k+n) nTy
relax' {n} {k} = rewrite plusCommutative k n in relax

{-
relax (Lit val s) = Lit val s
relax (SNil s) = SNil s
relax (Var vid field s) = (Var vid field s)
relax (ParenExpr wrapped s) = (ParenExpr wrapped s)
relax (PairExpr left right s) = (PairExpr left right s)
relax (FunCall fid args s) = (FunCall fid args s)
relax {k=d} (UnOpExpr {n} {k} op e   s) = rewrite sym (plusCommutative (n+k) d) in 
                                          rewrite sym (plusAssociative n k d) in (UnOpExpr op e   s) 
relax {k=d} (LOpExpr  {n} {k} l op r s) = rewrite sym (plusCommutative (S (n+k)) d) in 
                                          rewrite sym (plusAssociative n k d) in (LOpExpr  l op r s)
relax {k=d} (ROpExpr  {n} {k} l op r s) = rewrite sym (plusCommutative (S (n+k)) d) in 
                                          rewrite sym (plusAssociative n k d) in (ROpExpr  l op r s)
                                          -}

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

interface Functor t => Annotated (t:Type -> Type) where
  note   : t nTy -> nTy
  assign : nTy -> t nTy -> t nTy
  mutate : (nTy -> nTy) -> t nTy -> t nTy

interface Annotated t => VerifiedAnnotated (t:Type -> Type) where
  annotatedIdentity : (x:t nTy) -> x = assign (note x) x
  annotatedNoteIdentity : (x:t nTy) -> (s:nTy) -> s = note (assign s x)
  annotatedMutate : (x:t nTy) -> (f:nTy -> nTy) -> mutate f x = assign (f (note x)) x
  annotatedOverwrite : (x:t nTy) -> (s1:nTy) -> (s2:nTy) -> assign s1 x = assign s1 (assign s2 x)

Functor Id where
  map f (MkId name s) = MkId name (f s)

Functor Selector where
  map f (MkSel sel s) = MkSel sel (f s)
  
Functor Field where
  map f (MkField sels) = MkField (map (map f) sels)

Functor (UnOp n) where
  map f (Neg s) = Neg (f s)
  map f (Not s) = Not (f s)

Functor (LOp n) where
  map f (Mult s) = Mult (f s)
  map f (Div s) = (Div $ f s)
  map f (Mod s) = (Mod $ f s)
  map f (Plus s) = (Plus $ f s)
  map f (Minus s) = (Minus $ f s)
  map f (Lt s) = (Lt $ f s)
  map f (Gt s) = (Gt $ f s)
  map f (Leq s) = (Leq $ f s)
  map f (Geq s) = (Geq $ f s)
  map f (Eq s) = (Eq $ f s)
  map f (Neq s) = (Neq $ f s)
  map f (And s) = (And $ f s)
  map f (Or s) = (Or $ f s)

Functor (ROp n) where
  map f (Cons s) = (Cons $ f s)

Functor (Expr n) where
  map f (Lit val s) = Lit val (f s)
  map f (SNil s) = SNil (f s)
  map f (Var vid field s) = Var (map f vid) (map f field) (f s)
  map f (ParenExpr wrapped s) = ParenExpr (map f wrapped) (f s)
  map f (PairExpr left right s) = PairExpr (map f left) (map f right) (f s)
  map f (FunCall fid args s) = FunCall (map f fid) (assert_total (map (map f) args)) (f s)
  map f (UnOpExpr op e s) = UnOpExpr (map f op) (map f e) (f s)
  map f (LOpExpr l op r s) = LOpExpr (map f l) (map f op) (map f r) (f s)
  map f (ROpExpr l op r s) = ROpExpr (map f l) (map f op) (map f r) (f s)


Annotated Id where
  note (MkId name s) = s
  assign s (MkId name _) = MkId name s
  mutate = map

Annotated Selector where
  note (MkSel sel s) = s
  assign s (MkSel sel _) = MkSel sel s
  mutate = map

Annotated (UnOp n) where
  note (Neg s) = s
  note (Not s) = s
  assign s (Neg x) = Neg s
  assign s (Not x) = Not s
  mutate = map

Annotated (Expr n) where
  note (Lit val s) = s
  note (SNil s) = s
  note (Var vid field s) = s
  note (ParenExpr wrapped s) = s
  note (PairExpr left right s) = s
  note (FunCall fid args s) = s
  note (UnOpExpr op e s) = s
  note (LOpExpr l op r s) = s
  note (ROpExpr l op r s) = s
  assign s (Lit val x) = (Lit val s)
  assign s (SNil x) = (SNil s)
  assign s (Var vid field x) = (Var vid field s)
  assign s (ParenExpr wrapped x) = (ParenExpr wrapped s)
  assign s (PairExpr left right x) = (PairExpr left right s)
  assign s (FunCall fid args x) = (FunCall fid args s)
  assign s (UnOpExpr op e x) = (UnOpExpr op e s)
  assign s (LOpExpr l op r x) = (LOpExpr l op r s)
  assign s (ROpExpr l op r x) = (ROpExpr l op r s)
  mutate = map
