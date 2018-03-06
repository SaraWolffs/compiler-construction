module SPL.Parser

import public Text.Lexer

-- Derivation libraries
import Derive.Show
import Derive.Eq
import Data.Vect
import Language.Reflection.Elab
import Language.Reflection.Utils
import Pruviloj.Core
import Pruviloj.Internals.TyConInfo
import Pruviloj.Internals
%language ElabReflection

public export
data SplToken : Type where 
  TokKey : String -> SplToken
  TokId : String -> SplToken
  TokField : String -> SplToken
  TokBrac : Char -> SplToken
  TokSpecial : String -> SplToken
  TokOp : String -> SplToken
  TokNum : Nat -> SplToken
  TokChar : Char -> SplToken
  TokString : String -> SplToken
  TokComment : String -> SplToken
  TokWhite : SplToken

%runElab deriveShow `{{SPL.Parser.SplToken}}
%runElab deriveEq `{{SPL.Parser.SplToken}}

splTokMap : TokenMap SplToken
splTokMap = [(digits,TokNum . cast),
             (is '=',TokSpecial),
             (spaces,const TokWhite)]

skipWhites : List (TokenData SplToken) -> List (TokenData SplToken)
skipWhites [] = []
skipWhites (h::t) with (tok h)
  skipWhites (h::t) | TokWhite = skipWhites t
  skipWhites (h::t) | _ = h :: skipWhites t

isSemantic : SplToken -> Bool
isSemantic (TokComment _) = False
isSemantic TokWhite = False
isSemantic _ = True

export
lexSpl : String -> (List (TokenData SplToken), (Int,Int,String))
lexSpl = (\(ts,end)=>(skipWhites ts,end)) . (lex splTokMap) 
