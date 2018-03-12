module SPL.ParserSpec
import TestFrame
import SPL.Parser

%default total

testlex : String -> List SplToken
testlex = (map tok) . fst . lexSpl

spec : List TestCase
spec = [check testlex "" equals (the (List SplToken) []),
        check testlex "5" equals [TokNum 5],
        check testlex "=" equals [TokSpecial "="],
        check testlex "5=6" equals [TokNum 5,TokSpecial "=",TokNum 6],
        check testlex "5 = 6" equals [TokNum 5,TokSpecial "=",TokNum 6],
        check testlex "var" equals [TokKey "var"],
        check testlex "Void" equals [TokKey "Void"],
        check testlex "Void " equals [TokKey "Void"],
        check testlex "Int" equals [TokKey "Int"],
        check testlex "Bool" equals [TokKey "Bool"],
        check testlex "Char" equals [TokKey "Char"],
        check testlex "if" equals [TokKey "if"],
        check testlex "else" equals [TokKey "else"],
        check testlex "while" equals [TokKey "while"],
        check testlex "return" equals [TokKey "return"],
        check testlex "False" equals [TokKey "False"],
        check testlex "True" equals [TokKey "True"],
        check testlex "x" equals [TokId "x"],
        check testlex "true" equals [TokId "true"],
        check testlex "print" equals [TokId "print"],
        check testlex ".hd" equals [TokField "hd"],
        check testlex ".tl" equals [TokField "tl"],
        check testlex ".fst" equals [TokField "fst"],
        check testlex ".snd" equals [TokField "snd"],
        check testlex "() {} [ ]" equals [TokBrac '(',TokBrac ')',
                                         TokBrac '{',TokBrac '}',
                                         TokBrac '[',TokBrac ']'],
        check testlex "[" equals [TokBrac '['],
        check testlex "]" equals [TokBrac ']'],
        check testlex "= ; -> , :: []" equals [TokSpecial "=", TokSpecial ";",
                                   TokSpecial "->", TokSpecial ",", 
                                   TokSpecial "::", TokSpecial "[]"],
        check testlex operators equals (map TokOp . words) operators, 
        check testlex (quotechars chars) equals map TokChar chars,
        Nothing]
        where 
          operators = "+ * / % == <= < >= > != ! && || - :"
          chars : List Char
          chars = unpack "qwertuiopsdfgjklcvbnmQWERTYUIOPLKJHGFDSAZXCVBNM"
          charquote : Char -> String
          charquote c = pack ['\'',c,'\'']
          quotechars : List Char -> String
          quotechars = concat . map charquote

export
printResults : IO ()
printResults = putStr (testResults spec)
