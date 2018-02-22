module TestFrame

import Data.So

%default total 

eqProof : (x:_) -> (y:_) -> {auto ok : x=y} -> Maybe _
eqProof _ _ = Nothing

eqTest : Eq a => (x:a) -> (y:a) -> (msg:b) -> Maybe b
eqTest x y msg = if x == y then Nothing else pure msg

propProof : (x:_) -> (p:a->Bool) -> {auto ok : So (p x)} -> Maybe _
propProof _ _ = Nothing

propTest : (x:a) -> (p:a->Bool) -> (msg:b) -> Maybe b
propTest x p msg = if p x then Nothing else pure msg

syntax trivially [a] is [b] = eqProof a b
syntax provably [a] is [b] by [witness] = eqProof a b {ok=witness}
syntax check [a] equals [b]  = 
  eqTest a b ("Failed test:\nExpected: " ++ show b ++ "\nGot: " ++ show a ++ "\n")
syntax check [a] satisfies [p] meaning [desc] = 
  propTest a p ("Failed test:\n" ++ show a ++ " doesn't satisfy " ++ desc ++ "\n")

testResults : Show a => List (Maybe a) -> String
testResults spec with (catMaybes spec)
  testResults spec | [] = "All tests passed"
  testResults spec | failures = unlines (map show failures)

{- ALL DEPRECATED BELOW
total
take : Nat -> Stream a -> List a
take Z _ = []
take (S n) (h::t) = h :: take n t



spec : List (Maybe String)
spec = [
  trivially (parse "5") is (ASTInt 5),
  provably (parse "5 + 7") is (ASTPlus (ASTInt 5) (ASTInt 7)) by addParseProof,
  ]
-}
