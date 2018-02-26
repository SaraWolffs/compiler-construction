module SPL.Parser

import public Text.Lexer

public export
data SplToken : Type where 
  TokNat : Nat -> SplToken
  TokEq : SplToken

export
Show SplToken where
  show (TokNat n) = "TokNat" ++ show n
  show TokEq = "TokEq"

export 
Eq SplToken where
  (TokNat n) == (TokNat m) = n == m
  TokEq      == TokEq      = True
  _          == _          = False

splTokMap : TokenMap SplToken
splTokMap = [(digits,TokNat . cast)]

export
lexSpl : String -> (List (TokenData SplToken), (Int,Int,String))
lexSpl = lex splTokMap
