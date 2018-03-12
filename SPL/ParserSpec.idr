module SPL.ParserSpec
import TestFrame
import SPL.Parser

%default total

testlex : String -> List SplToken
testlex = (map tok) . fst . lexSpl

sampleSnippet : String
sampleSnippet = concat
    [ "/*\n  Three ways to implement\n blabla\n /*nested comment*/",
      "\n more bla\n */ \n facR ( n ) :: Int -> Int {\n",
      "    if ( n < 2 ) {\n",
      "        return 1;\n",
      "    } else { //recursive case\n",
      "        return n * facR ( n - 1 );\n",
      "    }\n}"]

strippedSnippet : String
strippedSnippet = "facR(n)::Int->Int{if(n<2){return 1;}else{return n*facR(n-1);}}"

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
        check testlex "\"This is a string literal\"" equals 
                [TokString "This is a string literal"],
        check testlex "\"This string contains an escaped \\\".\"" equals
                [TokString "This string contains an escaped \"."],
        check testlex "'\\''" equals [TokChar '\''],
        check testlex sampleSnippet equals testlex strippedSnippet,
        Nothing]
        where 
          operators = "+ * / % == <= < >= > != ! && || - :"
          chars : List Char
          chars = unpack "`1234567890~!@#$%^&*()[];qwertuioJHGFDSAZXCVBNM"
          charquote : Char -> String
          charquote c = pack ['\'',c,'\'']
          quotechars : List Char -> String
          quotechars = concat . map charquote

export
printResults : IO ()
printResults = putStr (testResults spec)
