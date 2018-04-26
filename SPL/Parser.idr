module SPL.Parser

import SPL.Lexer
import SPL.AST

import Text.Parser

import Data.Combinators.Applicative
import Control.Pipeline

%default total

RichTok : Type
RichTok = TokenData SplToken

record Loc where
  constructor MkLoc
  line : Nat
  col : Nat

data LocNote : Type where
  At   : (loc:Loc) -> LocNote
  Span : (begin:Loc) -> (end:Loc) -> LocNote

loc : RichTok -> Loc
loc = MkLoc <$> cast . line <*> cast . col

at : RichTok -> LocNote
at = At . loc

span : (first:LocNote) -> (last:LocNote) -> LocNote
span (At begin) (At end) = Span begin end
span (At begin) (Span _ end) = Span begin end
span (Span begin _) (At end) = Span begin end
span (Span begin _) (Span _ end) = Span begin end

Semigroup LocNote where
  (<+>) = span

Parser : {c:Bool} -> Type -> Type
Parser {c} = Grammar RichTok c 

Consume : ((nTy:Type) -> Type) -> Type
Consume = Grammar RichTok True  . (<| LocNote)

Allow   : ((nTy:Type) -> Type) -> Type
Allow   = Grammar RichTok False . (<| LocNote)

Structure : Type
Structure = Grammar RichTok True LocNote

ident : Consume Id 
ident = terminal $ \x=>case tok x of 
                            TokId s => Just (MkId s (at x))
                            _ => Nothing

selector : Consume Selector
selector = terminal $ \x=>case tok x of 
                            TokField s => Just (MkSel s (at x))
                            _ => Nothing

require : (req:SplToken) -> Structure
require req = terminal $ \x=>if tok x == req then Just (at x) else Nothing

special : String -> Structure
special = require . TokSpecial

key : String -> Structure
key = require . TokKey

brac : Char -> Structure
brac = require . TokBrac

op : String -> Structure
op = require . TokOp

lit : Consume (Expr (AtomLevel+k))
lit = terminal $ \x=>case tok x of 
                          TokNum    n    => Just (Lit {t=Num} n     (at x))
                          TokChar   c    => Just (Lit {t=Chr} c     (at x))
                          TokString s    => Just (Lit {t=Str} s     (at x))
                          TokKey "True"  => Just (Lit {t=Bol} True  (at x))
                          TokKey "False" => Just (Lit {t=Bol} False (at x))
                          _ => Nothing


between : (open:Structure) -> (close:Structure) -> 
          (build:a -> LocNote -> b LocNote) -> (p:Parser a) -> Consume b
between open close build p = [| (\l,m,r=> build m (span l r)) open p close |]

parens : (build:a -> LocNote -> b LocNote) -> (p:Parser a) -> Consume b
parens = between (brac '(') (brac ')')

braced : (build:a -> LocNote -> b LocNote) -> (p:Parser a) -> Consume b
braced = between (brac '{') (brac '}')

pair : (build:a -> a -> LocNote -> b LocNote) -> (p:Parser a) -> Consume b
pair build p = parens (uncurry build) [| (\l,_,r=>(l,r)) p (special ",") p |]


foldr1' : (a -> a -> a) -> (l:List a) -> {auto ok:NonEmpty l} -> a
foldr1' f [] impossible
foldr1' f (x :: xs) = foldr f x xs

dOp : {a:Nat->Type->Type} -> String -> (build:LocNote -> a n LocNote) -> 
      Parser {c=True} (n:Nat ** a n LocNote)
dOp str build = MkDPair _ . build <$> op str

lop : (Parser {c=True} (n:Nat ** LOp n LocNote))
lop = foldr1' (<|>) [ 
              dOp "*"  Mult, dOp "/"  Div  , dOp "%"  Mod, 
              dOp "+"  Plus, dOp "-"  Minus, 
              dOp "<"  Lt  , dOp ">"  Gt   , dOp "<=" Leq, dOp ">=" Geq, 
              dOp "==" Eq  , dOp "!=" Neq  , 
              dOp "&&" And , dOp "||" Or   ]
              
rop : (Parser {c=True} (n:Nat ** ROp n LocNote))
rop = dOp ":" Cons

unop : (Parser {c=True} (n:Nat ** UnOp n LocNote))
unop = foldr1' (<|>) [ dOp "-" Neg, dOp "!"  Not ]



var : Consume (Expr AtomLevel)
var = do vid <- ident
         field <- many selector
         pure (Var vid (MkField field) (foldl span (note vid) (map note field)))

data ShuntFrame : Type where
  SAtom : Atom LocNote -> ShuntFrame
  SLeft : (n:Nat) -> LOp n LocNote -> ShuntFrame
  SRight : (n:Nat) -> ROp n LocNote -> ShuntFrame
  SPre : (n:Nat) -> UnOp n LocNote -> ShuntFrame

inop : Parser {c=True} ShuntFrame
inop = (>>=) {c2=False} lop (\(n ** o)=> pure $ SLeft n o) <|>
       (>>=) {c2=False} rop (\(n ** o)=> pure $ SRight n o)

mutual 
  -- This bit of DRY horror brought to you by finicky totality checkers.
  atom : Consume Atom
  atom = recexpr <|> lit <|> SNil <$> special "[]" <|> var
    where
      sepexpr : Parser {c=False} (List $ Expression LocNote)
      sepexpr = sepBy (special ",") expr
      mkPexpr : (es:List $ Expression LocNote) -> {auto ok:NonEmpty es} -> LocNote -> Atom LocNote
      mkPexpr [x] parenloc = ParenExpr x parenloc
      mkPexpr [r,l] parenloc = PairExpr r l parenloc
      mkPexpr (x::(x'::xs)) parenloc = PairExpr x (relax $ mkPexpr (x'::xs) parenloc) parenloc
      -- pexpr => Pair or Paren Expr
      pexpr : (List $ Expression LocNote) -> (LocNote) -> Allow Atom
      pexpr [] _ = fail "Unexpected \"()\" (Did you mean to call a function?)"
      pexpr (x::xs) loc = pure $ mkPexpr (x::xs) loc
      fcall : Id LocNote -> (List $ Expression LocNote) -> (LocNote) -> Allow Atom
      fcall fid args loc = pure $ FunCall fid args (span (note fid) loc)
      recexpr : Consume Atom
      recexpr =  do build <- option pexpr (map fcall ident)
                    oloc <- special "("
                    commit
                    exprs <- sepexpr -- REPORT: Totality checker issue: beta reduction kills here
                    cloc <- special ")"
                    build exprs $ span oloc cloc

  dijkstra : List ShuntFrame -> Consume Expression
  dijkstra [] = ?dijkstraempty
  dijkstra (h::t) = ?dijkstranonempty
  
  subexpr : (n:Nat) -> Consume $ Expr n
  subexpr Z = atom
  subexpr (S n) = do left <- atom
                     fail {c=False} "Uncomplete definition of subexpr"

  extendexpr : Expr m LocNote -> (n:Nat) -> {auto ok:LTE m n} -> Allow (Expr n)
  expr : Consume Expression
  expr = subexpr TopLevel
