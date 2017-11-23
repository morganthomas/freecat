module FreeCat.Parser where

import FreeCat.Core (
    LexicalToken(..),
    RawSymbol,
    RawExpr(..),
    RawPattern(..),
    RawTypeAssertion(..),
    RawEquation(..),
    RawDeclaration(RawTypeDeclaration, RawEquationDeclaration),
    RawContext
  )

import Text.Parsec

type FreeCatParser = Parsec [LexicalToken] ()

parseContext :: FreeCatParser RawContext
parseContext = many parseDeclaration

--
-- Declarations
--

parseDeclaration :: FreeCatParser RawDeclaration
parseDeclaration = do
  varDecl0 <- parseTypeAssertion
  varDecls <- many (exactToken CommaToken >> parseTypeAssertion)
  equation <-
    optionMaybe (
      do exactToken PeriodToken
         pat <- parsePattern
         def <- parseExpr
         return (pat, def)
    )
  case equation of
    Nothing ->
      case varDecls of
        [] -> return (RawTypeDeclaration varDecl0)
        _ -> unexpected "comma after type assertion"
    Just (pat, def) ->
      return (RawEquationDeclaration (RawEquation (varDecl0:varDecls) pat def))

parseTypeAssertion :: FreeCatParser RawTypeAssertion
parseTypeAssertion = do
  s <- parseSymbol
  exactToken ColonToken
  t <- parseExpr
  return (RawTypeAssertion s t)

--
-- Patterns
--

parsePattern :: FreeCatParser RawPattern
parsePattern = parsePattern1

parsePattern1 :: FreeCatParser RawPattern
parsePattern1 = do
  pats <- many1 parsePattern0
  case pats of
    [pat] -> return pat
    (pat:pats) -> return (foldl RawAppPat pat pats)

parsePattern0 :: FreeCatParser RawPattern
parsePattern0 = parseSymbolPattern <|> parseParenthesizedPattern

parseSymbolPattern :: FreeCatParser RawPattern
parseSymbolPattern = do
  s <- parseSymbol
  return (RawSymbolPat s)

parseParenthesizedPattern :: FreeCatParser RawPattern
parseParenthesizedPattern = do
  exactToken OpenParenToken
  pat <- parsePattern
  exactToken CloseParenToken
  return pat

--
-- Expressions
--

parseExpr :: FreeCatParser RawExpr
parseExpr = parseExpr3

parseExpr4 :: FreeCatParser RawExpr
parseExpr4 = parseLambdaExpr <|> parseExpr3

parseLambdaExpr :: FreeCatParser RawExpr
parseLambdaExpr = do
  exactToken BackslashToken
  s <- parseSymbol
  exactToken ColonToken
  t <- parseExpr2
  exactToken FatArrowToken
  e <- parseExpr3
  return (RawLambdaExpr s t e)

parseExpr3 :: FreeCatParser RawExpr
parseExpr3 = try parseDependentFunctionType <|> parseExpr2

parseDependentFunctionType :: FreeCatParser RawExpr
parseDependentFunctionType = do
  exactToken OpenParenToken
  s <- parseSymbol
  exactToken ColonToken
  a <- parseExpr3
  exactToken CloseParenToken
  exactToken ThinArrowToken
  b <- parseExpr3
  return (RawDependentFunctionTypeExpr s a b)

parseExpr2 :: FreeCatParser RawExpr
parseExpr2 = do
  e1 <- parseExpr1
  e2opt <- optionMaybe (exactToken ThinArrowToken >> parseExpr3)
  case e2opt of
    Nothing -> return e1
    Just e2 -> return (RawFunctionTypeExpr e1 e2)

parseExpr1 :: FreeCatParser RawExpr
parseExpr1 = do
  es <- many1 parseExpr0
  case es of
    [e] -> return e
    (e:es) -> return (foldl RawAppExpr e es)

parseExpr0 :: FreeCatParser RawExpr
parseExpr0 = parseSymbolExpr <|> parseParenthesizedExpr

parseSymbolExpr :: FreeCatParser RawExpr
parseSymbolExpr = do
  s <- parseSymbol
  return (RawSymbolExpr s)

parseParenthesizedExpr :: FreeCatParser RawExpr
parseParenthesizedExpr = do
  exactToken OpenParenToken
  e <- parseExpr
  exactToken CloseParenToken
  return e

--
-- Individual tokens
--

emptySourcePos :: SourcePos
emptySourcePos = undefined

exactToken :: LexicalToken -> FreeCatParser ()
exactToken t =
  token show
    (\_ -> emptySourcePos)
    (\u -> if u == t then Just () else Nothing)

parseSymbol :: FreeCatParser RawSymbol
parseSymbol =
  token show
    (\_ -> emptySourcePos)
    (\u ->
      case u of
        SymbolToken s -> Just s
        _ -> Nothing)
