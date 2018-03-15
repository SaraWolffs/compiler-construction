#Parsing in Idris
##A Dependently Typed Functional Language

#Idris
 - Focus: general-purpose programming.
 - Haskell-like.
 - Type system: $\lambda\Pi C$ w/ full polymorphism.
 - Also ad-hoc overloading.
 - Optional totality checking.
 - Evaluation order: default strict.
 - Undecidables: totality, type inference.
 - Standard libraries under active development.

#Technique
 - Two-phase: lex, then use parser combinators.
 - Idris has Text.Lexer and Text.Parser.
 - Both use a deep grammar DSL.
 - Lexer grammar is context-free (Applicative).
 - Parser grammar is context-sensitive (Monad).
 - Lexer sequentally tries *consuming* token grammars.
 - Parser is a parser combinator lib like Parsec.

#Progress
 - Lexer works
 - AST is defined
 - Parsing is WIP

#Grammar changes: front
 - Generally slightly more C-like.
 - Compound statements are just statements.
 - Control structures affect any statement.
 - Any expression can be a statement.
 - The empty function is legal (:: -> Void).
 - String is a type, and literals exist.

#Grammar changes: back
 - Some refactoring of left-recursion.
 - Int literals are positive.
 - Operators and expressions have *levels*.
 - Lower levels bind more strongly. 
 - Associativity is enforced by level bias.

#AST
 - Multi-type AST, typechecked for correct parsing.
 - 
