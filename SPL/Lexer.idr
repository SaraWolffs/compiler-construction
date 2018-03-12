module SPL.Lexer

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
%access export

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

%runElab deriveShow `{{SPL.Lexer.SplToken}}
%runElab deriveEq `{{SPL.Lexer.SplToken}}

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

stripOuter : String -> String
stripOuter s = substr 1 (minus (length s) 2) s

escLex : Lexer
escLex = any

escChar' : List Char -> Char
escChar' [] = '?'
escChar' (c::rest) = c

escChar : String -> Char
escChar = escChar' . unpack

escString : String -> String
escString = concat . map tok . fst . 
            lex [(escape '\\' escLex, singleton . escChar . assert_total strTail),
                (some . non . is $ '\\', id)]

splTokMap : TokenMap SplToken
splTokMap = [
  (spaces, const TokWhite),
  (alpha <+> many (is '_' <|> alphaNum), splitKeysIds),
  (digits, TokNum . cast),
  (is '.' <+> choiceMap exact fields, TokField . assert_total strTail),
  (lineComment (exact "//") <|> blockComment (exact "/*") (exact "*/"), TokComment),
  (quote (is '\"') (escape '\\' escLex <|> any), 
            TokString . escString . stripOuter),
  -- order of next two lexers is semantically relevant for "'\\''"
  (exact "'\\" <+> escLex <+> is '\'', 
            TokChar . escChar . assert_total strTail . stripOuter),
  (is '\'' <+> any <+> is '\'', TokChar . assert_total (flip strIndex 1)),
  -- wordOf before oneOf is needed for maximal munch.
  (wordOf "-> :: []", TokSpecial),
  (wordOf "== <= >= != && ||", TokOp),
  (oneOf "(){}[]", TokBrac . assert_total strHead),
  (oneOf ";,=", TokSpecial),
  (oneOf "+*/%<>!-:", TokOp),
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

lexRaw : String -> (List (TokenData SplToken), (Int,Int,String))
lexRaw = lex splTokMap

cleanLex : List (TokenData SplToken) -> List (TokenData SplToken)
cleanLex = filter (isSemantic . tok)

lexSpl : String -> (List (TokenData SplToken), (Int,Int,String))
lexSpl = (\(ts,end)=>(cleanLex ts,end)) . lexRaw
