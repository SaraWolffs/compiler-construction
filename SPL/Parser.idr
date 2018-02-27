module SPL.Parser

import public Text.Lexer

public export
data SplToken : Type where 
  TokNat : Nat -> SplToken
  TokEq : SplToken
  TokWhite : SplToken

export
Show SplToken where
  show (TokNat n) = "TokNat" ++ show n
  show TokEq = "TokEq"
  show TokWhite = "TokWhite"

export 
Eq SplToken where
  (TokNat n) == (TokNat m) = n == m
  TokEq      == TokEq      = True
  TokWhite   == TokWhite   = True
  _          == _          = False

splTokMap : TokenMap SplToken
splTokMap = [(digits,TokNat . cast),
             (is '=',const TokEq),
             (spaces,const TokWhite)]

skipWhites : List (TokenData SplToken) -> List (TokenData SplToken)
skipWhites [] = []
skipWhites (h::t) with (tok h)
  skipWhites (h::t) | TokWhite = skipWhites t
  skipWhites (h::t) | _ = h :: skipWhites t

export
lexSpl : String -> (List (TokenData SplToken), (Int,Int,String))
lexSpl = (\(ts,end)=>(skipWhites ts,end)) . (lex splTokMap) 
