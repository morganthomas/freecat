module FreeCat.Lexer where

import FreeCat.Core (LexicalToken(..))
import Text.Parsec
import Text.Parsec.Char

lexer :: Parsec String () [LexicalToken]
lexer = many (whitespace >> freeCatToken)

whitespace :: Parsec String () ()
whitespace = skipMany (space <|> endOfLine)

freeCatToken :: Parsec String () LexicalToken
freeCatToken =
      (many letter >>= \s -> return (SymbolToken s))
  <|> (char ':' >> return ColonToken)
  <|> (char '-' >> char '>' >> return ThinArrowToken)
  <|> (char '=' >> char '>' >> return FatArrowToken)
  <|> (char '(' >> return OpenParenToken)
  <|> (char ')' >> return CloseParenToken)
  <|> (char '\\' >> return BackslashToken)
