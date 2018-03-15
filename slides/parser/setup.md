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
 - Every non-terminal is a datatype (as are some terminals).
 - Every production rule is a constructor.
 - The grammar has been inlined slightly in translation.
 - We want annotations! Now, location, later, types.
 - Every constructor has a final "note" argument.
 - Reuse: polymorphic in noteType.

#Expression levels
 - Let's see what dependent types can do.
 Snippet:
    LOpExpr, Id, ParenExpr, UnOpExpr 
 - `k` is "slack".
 - Note levels for each constructor.

#Parsing left-recursion
 - Left recursion as context-free is hard...
 - Parser combinators are context-sensitive. 
 - Parsing weaker grammars using stronger ones is easy.
 - Parse left side first, bind as context parsing rest.
 - `chainl` combinator does this, using `>>=`.
 - Unfortunatly, it's not in Text.Parser.
 - However, `>>=` is, so we'll be able to build it.

#Questions
