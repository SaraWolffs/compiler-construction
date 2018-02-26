module SPL.Parser

import Text.Lexer
{-
import Text.Lexer

public export
record TokenData a where
  constructor MkToken
  line : Int
  col : Int
  tok : a

expTokDat : Text.Lexer.Core.TokenData a -> SPL.Parser.TokenData a 
expTokDat a = MkToken (line a) (col a) (tok a)

export
lexSpl : String -> (List (SPL.Parser.TokenData a), (Int,Int,String))
-}

export 
data SplToken : Type where 
  TokNat : Nat -> SplToken

splTokMap : TokenMap SplToken
splTokMap = [] -- [(opt (is '-') <+> digits, TokInt . cast)]

export
lexSpl : String -> (List (TokenData SplToken), (Int,Int,String))
lexSpl = lex splTokMap
