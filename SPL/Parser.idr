module SPL.Parser

import SPL.Lexer
import SPL.AST

import Text.Parser

%default total

RichTok : Type
RichTok = TokenData SplToken

Consume : Type -> Type
Consume = Grammar RichTok True

Allow : Type -> Type
Allow = Grammar RichTok False

