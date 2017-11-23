module FreeCat.Lexer where

import Text.Parsec
import Text.Parsec.Char

data Token =
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

type PositionedToken = (Token, SourcePos)

type FreeCatLexer = Parsec String ()

lexer :: FreeCatLexer [PositionedToken]
lexer = many (whitespace >> freeCatToken)

whitespace :: FreeCatLexer ()
whitespace = skipMany (space <|> endOfLine)

freeCatToken :: FreeCatLexer PositionedToken
freeCatToken =
      symbolToken
  <|> constToken "," CommaToken
  <|> constToken "." PeriodToken
  <|> constToken ":" ColonToken
  <|> constToken "->" ThinArrowToken
  <|> constToken "=>" FatArrowToken
  <|> constToken "(" OpenParenToken
  <|> constToken ")" CloseParenToken
  <|> constToken "\\" BackslashToken

symbolToken :: FreeCatLexer PositionedToken
symbolToken = do
  s <- many1 letter
  pos <- getPosition
  return (SymbolToken s, pos)

constToken :: String -> Token -> FreeCatLexer PositionedToken
constToken s tok = do
  pos <- getPosition
  mapM char s
  return (tok, pos)
