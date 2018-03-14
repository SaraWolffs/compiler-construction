module SPL.Parser

import public Text.Parser

-- Derivation libraries
import Derive.Show
import Derive.Eq
import Data.Vect
import Language.Reflection.Elab
import Language.Reflection.Utils
import Pruviloj.Core
import Pruviloj.Internals.TyConInfo
import Pruviloj.Internals
import Data.Combinators.Applicative
%language ElabReflection

%default total
%access export

Atomlevel : Nat
Atomlevel = 0
Neglevel : Nat
Neglevel = 2
Multlevel : Nat
Multlevel = 4
Pluslevel : Nat
Pluslevel = 6
Ordlevel : Nat
Ordlevel = 8
Eqlevel : Nat
Eqlevel = 9
Notlevel : Nat
Notlevel = 10
Boollevel : Nat
Boollevel = 12
Conslevel : Nat
Conslevel = 14
Tuplevel : Nat
Tuplevel = 16
Toplevel : Nat
Toplevel = 18

data LOp : Nat -> {nTy:Type} -> Type where
  Mult  : {s:nTy} -> LOp Multlevel {nTy}
  Div   : {s:nTy} -> LOp Multlevel {nTy}
  Mod   : {s:nTy} -> LOp Multlevel {nTy}
  Plus  : {s:nTy} -> LOp Pluslevel {nTy}
  Minus : {s:nTy} -> LOp Pluslevel {nTy}
  Lt    : {s:nTy} -> LOp Ordlevel  {nTy}
  Gt    : {s:nTy} -> LOp Ordlevel  {nTy}
  Leq   : {s:nTy} -> LOp Ordlevel  {nTy}
  Geq   : {s:nTy} -> LOp Ordlevel  {nTy}
  Eq    : {s:nTy} -> LOp Eqlevel   {nTy}
  Neq   : {s:nTy} -> LOp Eqlevel   {nTy}
  And   : {s:nTy} -> LOp Boollevel {nTy}
  Or    : {s:nTy} -> LOp Boollevel {nTy}


