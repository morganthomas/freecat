-- Core syntactic and semantic definitions
module Incat.Core where

import Data.Map (Map, singleton)

data LexicalToken =
    SymbolToken String
  | ColonToken
  | ThinArrow
  | FatArrow
  | OpenParen
  | CloseParen
  | Backslash

-- Parse trees

type RawSymbol = String

typeOfType :: RawSymbol
typeOfType = "Type"

data RawExpr =
   RawSymbolExpr RawSymbol
 | RawAppExpr RawExpr RawExpr
 | RawLambdaExpr RawSymbol RawExpr RawExpr
 | RawFunctionTypeExpr RawExpr RawExpr
 | RawDependentFunctionTypeExpr RawSymbol RawExpr RawExpr

data RawPattern =
   RawSymbolPat RawSymbol
 | RawAppPat RawPattern RawPattern

patToExpr :: RawPattern -> RawExpr
patToExpr (RawSymbolPat s) = RawSymbolExpr s
patToExpr (RawAppPat p q) = RawAppExpr (patToExpr p) (patToExpr q)

data RawTypeAssertion = RawTypeAssertion RawSymbol Expr
data RawEquation = RawEquation [RawTypeAssertion] RawPattern RawExpr
data RawImport =
   RawImportAsSymbol String String -- uri, name
 | RawImportSelectively String [String] -- uri, symbols to import

data RawDeclaration =
   RawTypeDeclaration RawTypeAssertion
 | RawEquationDeclaration RawEquation
 | RawImportDeclaration RawImport

type RawContext = [RawDeclaration]

-- Basic semantic structures

data Symbol = Symbol {
  name :: String,
  definedType :: Expr,
  -- all pattern definitions have this symbol as their lead symbol
  definitions :: [Definition],
  nativeContext :: Context
}

data Definition =
   ConstantDef Expr
 | PatternDef [VariableDeclaration] Pattern Expr

data VariableDeclaration = VarDecl Symbol Expr

data Pattern =
   SymbolPat Symbol
 | AppPat Pattern Pattern

data Expr =
   SymbolExpr Symbol
 | AppExpr Expr Expr
 | LambdaExpr Symbol Expr Expr
 | FunctionTypeExpr Expr Expr
 | DependentFunctionTypeExpr Symbol Expr Expr

data Context = Context {
  uri :: Maybe String,
  parentContext :: Maybe Context,
  declarations :: Map String Symbol,
  importedSymbols :: Map String Symbol
}

data Error = Error String

evaluate :: Context -> Expr -> Either Error Expr
evaluate c (SymbolExpr s) =
  case definitions s of
    [] -> Right s
    (ConstantDef e : _) -> evaluate c e
    _ -> s
evaluate c (AppExpr e0 e1) =
  do e0e <- evaluate c e0
     e1e <- evaluate c e1
     case e0e of
      SymbolExpr s ->
        case definitions s of
          [] -> Right (AppExpr e0e e1e)
          (ConstantDef d : _) -> evaluate c (AppExpr d e1e)
          defs -> evaluatePatternMatch c defs (AppExpr e0e e1e)
      AppExpr _ _ ->
        do s <- leadSymbol e0e
           evaluatePatternMatch c (definitions s) (AppExpr e0e e1e)
      LambdaExpr s t d ->
        evaluate (simplyAugmentContext c (name s) (definedType s) e1e) d
      FunctionTypeExpr _ _ -> Left (Error "cannot have a function type on the left hand side of a function application")
      DependentFunctionTypeExpr _ _ _ -> Left (Error "cannot have a function type on the left hand side of a function application")
evaluate c (LambdaExpr s t d) = (LambdaExpr s t d)
evaluate c (FunctionTypeExpr a b) =
  do ae <- evaluate c a
     be <- evaluate c b
     return (FunctionTypeExpr ae be)
evaluate c (DependentFunctionTypeExpr s a b) = (DependentFunctionTypeExpr s a b)

-- Creates a new context which has the given context as parent and has a symbol
-- with the given name, type, and constant definition.
simplyAugmentContext :: Context -> String -> Expr -> Expr -> Context
simplyAugmentContext parentContext vName vType vDef =
  let newContext =
        Context {
          uri = Nothing,
          parentContext = Just parentContext,
          declarations = singleton vName newSymbol
        }
      newSymbol =
        Symbol {
          name = vName,
          definedType = vType,
          definitions = [ConstantDef vDef],
          nativeContext = newContext
        }
    in newContext

-- Gathers the lead symbol in a normalized application expression.
leadSymbol :: Expr -> Either Error Symbol
leadSymbol (SymbolExpr s) = Right s
leadSymbol (AppExpr e0 e1) = leadSymbol e0
leadSymbol (LambdaExpr _ _) = Left (Error "tried to find a lead symbol but found a lambda instead")
leadSymbol (FunctionTypeExpr _ _) = Left (Error "tried to find a lead symbol but found a function type instead")
leadSymbol (DependentFunctionTypeExpr _ _ _) = Left (Error "tried to find a lead symbol but found a function type instead")

-- Checks if the given expr matches any of the given pattern match definitions.
-- Returns the result of evaluating the expr against the first matching definition
-- if one matches, and throws an error if no patterns match.
evaluatePatternMatch :: Context -> [Definition] -> Expr -> Either Error Expr
