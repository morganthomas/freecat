module FreeCat.Parser where

import Text.Parsec
import FreeCat.Lexer (Token(..), PositionedToken, lexer)
import FreeCat.Core (
    Positioned,
    RawSymbol,
    RawExpr(..),
    RawTypeAssertion(..),
    RawEquation(..),
    RawDeclaration(RawTypeDeclaration, RawEquationDeclaration),
    RawContext
  )

type FreeCatParser = Parsec [PositionedToken] ()

runParse :: Either ParseError a -> IO a
runParse (Left e) = error (show e)
runParse (Right x) = return x

lexAndParseContext :: String -> Either ParseError RawContext
lexAndParseContext s = parse lexer "" s >>= parse context ""

lexAndParseExpr :: String -> Either ParseError RawExpr
lexAndParseExpr s =  parse lexer "" s >>= parse expr ""

context :: FreeCatParser RawContext
context = many declaration

--
-- Declarations
--

declaration :: FreeCatParser (Positioned RawDeclaration)
declaration = do {
  s0 <- symbol;
  pos <- getPosition;
  (
    (
      do exactToken ColonToken
         t0 <- expr3
         varDecl0 <- return (RawTypeAssertion s0 t0)
         varDecls <- many (exactToken CommaToken >> typeAssertion)
         equation <- optionMaybe (
             do exactToken PeriodToken
                pat <- pattern
                exactToken FatArrowToken
                def <- expr
                return (pat, def)
           )
         exactToken SemicolonToken
         case equation of
           Nothing ->
             case varDecls of
               [] -> return (RawTypeDeclaration varDecl0, pos)
               _ -> unexpected "comma after type assertion"
           Just (pat, def) ->
             return (RawEquationDeclaration (RawEquation (varDecl0:varDecls) pat def), pos)
    )
    <|>
    (
      do argPats <- many pattern
         exactToken FatArrowToken
         e <- expr
         exactToken SemicolonToken
         let pat = foldl (RawAppExpr pos) (RawSymbolExpr pos s0) argPats in
          return (RawEquationDeclaration (RawEquation [] pat e), pos)
    )
  )
}

typeAssertion :: FreeCatParser RawTypeAssertion
typeAssertion = do
  s <- symbol
  exactToken ColonToken
  t <- expr
  return (RawTypeAssertion s t)

--
-- Patterns
--

pattern :: FreeCatParser RawExpr
pattern = pattern1

pattern1 :: FreeCatParser RawExpr
pattern1 = do
  pos <- getPosition
  pats <- many1 pattern0
  case pats of
    [pat] -> return pat
    (pat:pats) -> return (foldl (RawAppExpr pos) pat pats)

pattern0 :: FreeCatParser RawExpr
pattern0 = symbolPattern <|> parenthesizedPattern

symbolPattern :: FreeCatParser RawExpr
symbolPattern = do
  pos <- getPosition
  s <- symbol
  return (RawSymbolExpr pos s)

parenthesizedPattern :: FreeCatParser RawExpr
parenthesizedPattern = do
  exactToken OpenParenToken
  pat <- pattern
  exactToken CloseParenToken
  return pat

--
-- Expressions
--

expr :: FreeCatParser RawExpr
expr = expr4

expr4 :: FreeCatParser RawExpr
expr4 = lambdaExpr <|> expr3

lambdaExpr :: FreeCatParser RawExpr
lambdaExpr = do
  pos <- getPosition
  exactToken BackslashToken
  s <- symbol
  exactToken ColonToken
  t <- expr2
  exactToken FatArrowToken
  e <- expr3
  return (RawLambdaExpr pos s t e)

expr3 :: FreeCatParser RawExpr
expr3 = try dependentFunctionType <|> expr2

dependentFunctionType :: FreeCatParser RawExpr
dependentFunctionType = do
  pos <- getPosition
  exactToken OpenParenToken
  s <- symbol
  exactToken ColonToken
  a <- expr3
  exactToken CloseParenToken
  exactToken ThinArrowToken
  b <- expr3
  return (RawDependentFunctionTypeExpr pos s a b)

expr2 :: FreeCatParser RawExpr
expr2 = do
  pos <- getPosition
  e1 <- expr1
  e2opt <- optionMaybe (exactToken ThinArrowToken >> expr3)
  case e2opt of
    Nothing -> return e1
    Just e2 -> return (RawFunctionTypeExpr pos e1 e2)

expr1 :: FreeCatParser RawExpr
expr1 = do
  pos <- getPosition
  es <- many1 expr0
  case es of
    [e] -> return e
    (e:es) -> return (foldl (RawAppExpr pos) e es)

expr0 :: FreeCatParser RawExpr
expr0 = symbolExpr <|> parenthesizedExpr

symbolExpr :: FreeCatParser RawExpr
symbolExpr = do
  pos <- getPosition
  s <- symbol
  return (RawSymbolExpr pos s)

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
