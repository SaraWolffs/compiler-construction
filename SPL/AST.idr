module SPL.AST

import Data.Combinators.Applicative

%default total
%access export

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

data Id = MkId String
data Field = MkField (List String)

data LOp  : Nat -> {nTy:Type} -> Type where
  Mult  : {s:nTy} -> LOp  MultLevel {nTy}
  Div   : {s:nTy} -> LOp  MultLevel {nTy}
  Mod   : {s:nTy} -> LOp  MultLevel {nTy}
  Plus  : {s:nTy} -> LOp  PlusLevel {nTy}
  Minus : {s:nTy} -> LOp  PlusLevel {nTy}
  Lt    : {s:nTy} -> LOp  OrdLevel  {nTy}
  Gt    : {s:nTy} -> LOp  OrdLevel  {nTy}
  Leq   : {s:nTy} -> LOp  OrdLevel  {nTy}
  Geq   : {s:nTy} -> LOp  OrdLevel  {nTy}
  Eq    : {s:nTy} -> LOp  EqLevel   {nTy}
  Neq   : {s:nTy} -> LOp  EqLevel   {nTy}
  And   : {s:nTy} -> LOp  BoolLevel {nTy}
  Or    : {s:nTy} -> LOp  BoolLevel {nTy}

data ROp  : Nat -> {nTy:Type} -> Type where
  Cons  : {s:nTy} -> ROp  ConsLevel {nTy}

data UnOp : Nat -> {nTy:Type} -> Type where
  Neg   : {s:nTy} -> UnOp NegLevel {nTy}
  Not   : {s:nTy} -> UnOp NotLevel {nTy}


data LitTy = Num | Str | Chr | Bol
ITyFromLitTy : LitTy -> Type
ITyFromLitTy Num = Nat
ITyFromLitTy Str = String
ITyFromLitTy Chr = Char
ITyFromLitTy Bol = Bool


data Expr : Nat -> {nTy:Type} -> Type where
  Lit       : {t:LitTy} -> (val:ITyFromLitTy t) -> {s:nTy} -> Expr (AtomLevel+k) {nTy}
  Nil       : {s:nTy} -> Expr (AtomLevel+k) {nTy}
  Var       : (vid:Id) -> (field:Field) -> {s:nTy} -> Expr (AtomLevel+k) {nTy}
  ParenExpr : (wrapped:Expr TopLevel {nTy}) -> {s:nTy} -> Expr (AtomLevel+k) {nTy}
  PairExpr  : (left:Expr TopLevel {nTy}) -> (right:Expr TopLevel {nTy}) -> 
                                                    {s:nTy} -> Expr (AtomLevel+k) {nTy}
  FunCall   : (fid:Id) -> (args:List (Expr TopLevel)) -> {s:nTy} -> Expr (AtomLevel+k)  {nTy}
