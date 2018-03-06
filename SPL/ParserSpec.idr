module SPL.ParserSpec
import TestFrame
import SPL.Parser

%default total

testlex : String -> List SplToken
testlex = (map tok) . fst . lexSpl

spec : List TestCase
spec = [check testlex "5" equals [TokNum 5],
        check testlex "=" equals [TokSpecial "="],
        check testlex "5=6" equals [TokNum 5,TokSpecial "=",TokNum 6],
        check testlex "5 = 6" equals [TokNum 5,TokSpecial "=",TokNum 6]
        ]

export
printResults : IO ()
printResults = putStr (testResults spec)
