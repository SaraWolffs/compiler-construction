module SPL.ParserSpec
import TestFrame
import SPL.Parser

%default total

testlex : String -> List SplToken
testlex = (map tok) . fst . lexSpl

spec : List TestCase
spec = [check testlex "5" equals [TokNat 5]]
