module SPL.Parser

import SPL.Lexer
import SPL.AST

import Text.Parser

import Data.Combinators.Applicative
import Control.Pipeline

%default total

RichTok : Type
RichTok = TokenData SplToken

record Loc where
  constructor MkLoc
  line : Nat
  col : Nat

data LocNote : Type where
  Virtual   : (near:Loc) -> LocNote
  At        : (loc:Loc) -> LocNote
  Spanning  : (begin:Loc) -> (end:Loc) -> LocNote

loc : RichTok -> Loc
loc = MkLoc <$> cast . line <*> cast . col

Consume : ((nTy:Type) -> Type) -> Type
Consume = Grammar RichTok True  . (<| LocNote)

Allow   : ((nTy:Type) -> Type) -> Type
Allow   = Grammar RichTok False . (<| LocNote)

ident : Consume Id 
ident = terminal $ \x=>case tok x of 
                            TokId s => Just (MkId s (At (loc x)))
                            _ => Nothing
