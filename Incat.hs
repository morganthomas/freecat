module Incat where

import Data.Map (Map)

-- Parse trees

type RawSymbol = String

typeOfType :: RawSymbol
typeOfType = "Type"

data RawExpr =
   RawSymbolExpr RawSymbol
 | RawAppExpr RawExpr RawExpr
 | RawLambdaExpr RawSymbol RawExpr RawExpr
 | RawFunctionTypeExpr RawSymbol RawExpr RawExpr

data RawPattern =
   RawSymbolPat RawSymbol
 | RawAppPat RawPattern RawPattern

patToExpr :: RawPattern -> RawExpr
patToExpr (RawSymbolPat s) = RawSymbolExpr s
patToExpr (RawAppPat p q) = RawAppExpr (patToExpr p) (patToExpr q)

data RawTypeAssertion = RawTypeAssertion RawSymbol Expr
data RawEquation = RawEquation [RawTypeAssertion] RawPattern RawExpr

data RawDeclaration =
   RawTypeDeclaration RawTypeAssertion
 | RawEquationDeclaration RawEquation

type RawContext = [RawDeclaration]

-- TODO: will use sequent types?
data SequentAssertion =
   SequentTypeAssertion Expr Expr
 | SequentPatternAssertion Pattern
 | SequentReductionAssertion Expr Expr
 | SequentContextAssertion

data Sequent = Sequent RawContext SequentAssertion

-- Annotated stuff

data Symbol = Symbol {
  name :: String,
  definedType :: Expr,
  -- lead symbol of each equation is this symbol
  equations :: [Equation],
  nativeContext :: Context
}

data Equation =
   ConstantEq Symbol Expr
 | PatternEq [VariableDeclaration] Pattern Expr

data VariableDeclaration = VarDecl Symbol Expr

data Pattern =
   SymbolPat Symbol
 | AppPat Pattern Pattern

data Expr =
   SymbolExpr Symbol
 | AppExpr Expr Expr
 | LambdaExpr Symbol Expr Expr
 | FunctionTypeExpr Symbol Expr Expr

data Context = Context {
  uri :: Maybe String,
  parentContext :: Maybe Context,
  declarations :: Map String Symbol,
  importedSymbols :: Map String Symbol
}
