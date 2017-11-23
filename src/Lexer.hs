module FreeCat.Lexer where

import Text.Parsec
import Text.Parsec.Char

data LexicalToken =
    SymbolToken String
  | CommaToken
  | ColonToken
  | PeriodToken
  | ThinArrowToken
  | FatArrowToken
  | OpenParenToken
  | CloseParenToken
  | BackslashToken
  deriving (Eq, Show)

lexer :: Parsec String () [LexicalToken]
lexer = many (whitespace >> freeCatToken)

whitespace :: Parsec String () ()
whitespace = skipMany (space <|> endOfLine)

freeCatToken :: Parsec String () LexicalToken
freeCatToken =
      (many letter >>= \s -> return (SymbolToken s))
  <|> (char ',' >> return CommaToken)
  <|> (char '.' >> return PeriodToken)
  <|> (char ':' >> return ColonToken)
  <|> (char '-' >> char '>' >> return ThinArrowToken)
  <|> (char '=' >> char '>' >> return FatArrowToken)
  <|> (char '(' >> return OpenParenToken)
  <|> (char ')' >> return CloseParenToken)
  <|> (char '\\' >> return BackslashToken)
