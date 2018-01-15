module FreeCat.Lexer where

import Text.Parsec
import Text.Parsec.Char
import Data.Maybe (catMaybes)

data Token =
    SymbolToken String
  | CommaToken
  | SemicolonToken
  | ColonToken
  | PeriodToken
  | ThinArrowToken
  | FatArrowToken
  | OpenParenToken
  | CloseParenToken
  | OpenCurlyToken
  | CloseCurlyToken
  | BackslashToken
  deriving (Eq, Show)

type PositionedToken = (Token, SourcePos)

type FreeCatLexer = Parsec String ()

lexer :: FreeCatLexer [PositionedToken]
lexer =
  many (
    (whitespace >> return Nothing)
    <|>
    (freeCatToken >>= return . Just)
  ) >>= (return . catMaybes)

whitespace :: FreeCatLexer ()
whitespace = skipMany1 (space <|> endOfLine)

freeCatToken :: FreeCatLexer PositionedToken
freeCatToken =
      symbolToken
  <|> constToken "," CommaToken
  <|> constToken "." PeriodToken
  <|> constToken ":" ColonToken
  <|> constToken ";" SemicolonToken
  <|> constToken "->" ThinArrowToken
  <|> constToken "=>" FatArrowToken
  <|> constToken "(" OpenParenToken
  <|> constToken ")" CloseParenToken
  <|> constToken "{" OpenCurlyToken
  <|> constToken "}" CloseCurlyToken
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
