module FreeCat.Parser where

import Text.Parsec
import FreeCat.Lexer (Token(..), PositionedToken, lexer)
import FreeCat.Core (
    RawSymbol,
    RawExpr(..),
    RawPattern(..),
    RawTypeAssertion(..),
    RawEquation(..),
    RawDeclaration(RawTypeDeclaration, RawEquationDeclaration),
    RawContext
  )

type FreeCatParser = Parsec [PositionedToken] ()

context :: FreeCatParser RawContext
context = many declaration

--
-- Declarations
--

declaration :: FreeCatParser RawDeclaration
declaration = do
  varDecl0 <- typeAssertion
  varDecls <- many (exactToken CommaToken >> typeAssertion)
  equation <-
    optionMaybe (
      do exactToken PeriodToken
         pat <- pattern
         def <- expr
         return (pat, def)
    )
  case equation of
    Nothing ->
      case varDecls of
        [] -> return (RawTypeDeclaration varDecl0)
        _ -> unexpected "comma after type assertion"
    Just (pat, def) ->
      return (RawEquationDeclaration (RawEquation (varDecl0:varDecls) pat def))

typeAssertion :: FreeCatParser RawTypeAssertion
typeAssertion = do
  s <- symbol
  exactToken ColonToken
  t <- expr
  return (RawTypeAssertion s t)

--
-- Patterns
--

pattern :: FreeCatParser RawPattern
pattern = pattern1

pattern1 :: FreeCatParser RawPattern
pattern1 = do
  pats <- many1 pattern0
  case pats of
    [pat] -> return pat
    (pat:pats) -> return (foldl RawAppPat pat pats)

pattern0 :: FreeCatParser RawPattern
pattern0 = symbolPattern <|> parenthesizedPattern

symbolPattern :: FreeCatParser RawPattern
symbolPattern = do
  s <- symbol
  return (RawSymbolPat s)

parenthesizedPattern :: FreeCatParser RawPattern
parenthesizedPattern = do
  exactToken OpenParenToken
  pat <- pattern
  exactToken CloseParenToken
  return pat

--
-- Expressions
--

expr :: FreeCatParser RawExpr
expr = expr3

expr4 :: FreeCatParser RawExpr
expr4 = lambdaExpr <|> expr3

lambdaExpr :: FreeCatParser RawExpr
lambdaExpr = do
  exactToken BackslashToken
  s <- symbol
  exactToken ColonToken
  t <- expr2
  exactToken FatArrowToken
  e <- expr3
  return (RawLambdaExpr s t e)

expr3 :: FreeCatParser RawExpr
expr3 = try dependentFunctionType <|> expr2

dependentFunctionType :: FreeCatParser RawExpr
dependentFunctionType = do
  exactToken OpenParenToken
  s <- symbol
  exactToken ColonToken
  a <- expr3
  exactToken CloseParenToken
  exactToken ThinArrowToken
  b <- expr3
  return (RawDependentFunctionTypeExpr s a b)

expr2 :: FreeCatParser RawExpr
expr2 = do
  e1 <- expr1
  e2opt <- optionMaybe (exactToken ThinArrowToken >> expr3)
  case e2opt of
    Nothing -> return e1
    Just e2 -> return (RawFunctionTypeExpr e1 e2)

expr1 :: FreeCatParser RawExpr
expr1 = do
  es <- many1 expr0
  case es of
    [e] -> return e
    (e:es) -> return (foldl RawAppExpr e es)

expr0 :: FreeCatParser RawExpr
expr0 = symbolExpr <|> parenthesizedExpr

symbolExpr :: FreeCatParser RawExpr
symbolExpr = do
  s <- symbol
  return (RawSymbolExpr s)

parenthesizedExpr :: FreeCatParser RawExpr
parenthesizedExpr = do
  exactToken OpenParenToken
  e <- expr
  exactToken CloseParenToken
  return e

--
-- Individual tokens
--

exactToken :: Token -> FreeCatParser ()
exactToken t =
  token show
    (\(u,pos) -> pos)
    (\(u,pos) -> if u == t then Just () else Nothing)

symbol :: FreeCatParser RawSymbol
symbol =
  token show
    (\(tok,pos) -> pos)
    (\(tok,pos) ->
      case tok of
        SymbolToken s -> Just s
        _ -> Nothing)
