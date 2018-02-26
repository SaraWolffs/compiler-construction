module SPL.Parser

import public Text.Lexer

public export
data SplToken : Type where 
  TokNat : Nat -> SplToken

splTokMap : TokenMap SplToken
splTokMap = []

export
lexSpl : String -> (List (TokenData SplToken), (Int,Int,String))
lexSpl = lex splTokMap
