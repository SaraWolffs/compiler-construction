module SPL.Parser

import Text.Lexer

export 
data SplToken : Type where 
  TokNat : Nat -> SplToken

splTokMap : TokenMap SplToken
splTokMap = []

export
lexSpl : String -> (List (TokenData SplToken), (Int,Int,String))
lexSpl = lex splTokMap
