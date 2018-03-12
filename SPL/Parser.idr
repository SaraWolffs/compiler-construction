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
import Data.Combinators.Applicative
%language ElabReflection
%default total

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
  TokErr : String -> SplToken

%runElab deriveShow `{{SPL.Parser.SplToken}}
%runElab deriveEq `{{SPL.Parser.SplToken}}

reserved : List String
reserved =
  ["var","Void","Int","Bool","Char","if","else","while","return","False","True"]

fields : List String
fields = ["hd","tl","fst","snd"]

isKey : String -> Bool
isKey = flip elem reserved

-- Idris has a combinator-unfriendly implementation of Lazy.
eagerIf : Bool -> a -> a -> a
eagerIf True = const
eagerIf False = flip const

-- For illustrative purposes: 
fork3 : (a -> b -> c -> o) -> (i -> a) -> (i -> b) -> (i -> c) -> i -> o
fork3 f a b c = [| f a b c |]

splitKeysIds : String -> SplToken
splitKeysIds = [| eagerIf isKey TokKey TokId |]

wordOf : String -> Lexer
wordOf = choiceMap exact . words

splTokMap : TokenMap SplToken
splTokMap = [
  (digits, TokNum . cast),
  (spaces, const TokWhite),
  (alpha <+> many (is '_' <|> alphaNum), splitKeysIds),
  (choiceMap (exact . strCons '.') fields, TokField . assert_total strTail),
  (wordOf "-> :: []", TokSpecial),
  (oneOf "(){}[]", TokBrac . assert_total strHead),
  (oneOf ";,=", TokSpecial),
  (any <+> manyUntil space any, TokErr)
  ]

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
