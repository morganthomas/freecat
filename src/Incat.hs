-- Core syntactic and semantic definitions
-- The central processing unit
module Incat.Core where

import Data.Map (Map, singleton, empty)
import Control.Monad.Trans.Class
import Control.Monad.Trans.State
import Control.Monad.Trans.Except as E
import Control.Monad.IO.Class

--
-- Lexical tokens
--

data LexicalToken =
    SymbolToken String
  | ColonToken
  | ThinArrow
  | FatArrow
  | OpenParen
  | CloseParen
  | Backslash

--
-- Errors
--

data Error =
   ErrFunctionTypeOnAppLHS
 | ErrExpectedLeadSymbolFoundLambda
 | ErrExpectedLeadSymbolFoundFunctionType
 | ErrNoPatternMatch
 | ErrExpectedPatternMatchDefGotConstantDef

--
-- Parse trees
--

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

--
-- Basic semantic structures
--

data Symbol = Symbol {
  name :: String,
  definedType :: Expr,
  -- all pattern definitions have this symbol as their lead symbol
  definitions :: [Definition],
  nativeContext :: Context
}

instance Eq Symbol where
  s == t = name s == name t && nativeContext s == nativeContext t

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
 deriving (Eq)

data Context = Context {
  contextId :: Integer,
  uri :: Maybe String,
  parentContext :: Maybe Context,
  declarations :: Map String Symbol,
  importedSymbols :: Map String Symbol
}

rootContext :: Context
rootContext =
  Context {
    contextId = 0,
    uri = Nothing,
    parentContext = Nothing,
    declarations = empty,
    importedSymbols = empty
  }

instance Eq Context where
  c0 == c1 = contextId c0 == contextId c1

--
-- Incat monadic meta-context
--

data IncatState = IncatState {
  nextContextId :: Integer,
  -- keyed by uri
  importedContexts :: Map String Context
}

initialState :: IncatState
initialState =
  IncatState {
    -- rootContext uses id 0
    nextContextId = 1,
    importedContexts = empty
  }

type Incat = StateT IncatState (E.ExceptT Error IO)

barf :: Error -> Incat a
barf e = lift (E.throwE e)

popContextId :: Incat Integer
popContextId =
  do st <- get
     put $ st { nextContextId = 1 + nextContextId st }
     return $ nextContextId st

--
-- Evaluation
--

evaluate :: Context -> Expr -> Incat Expr
evaluate c (SymbolExpr s) =
  case definitions s of
    (ConstantDef e : _) -> evaluate c e
    _ -> return (SymbolExpr s)
evaluate c (AppExpr e0 e1) =
  do e0e <- evaluate c e0
     e1e <- evaluate c e1
     case e0e of
      SymbolExpr s ->
        case definitions s of
          [] -> return (AppExpr e0e e1e)
          (ConstantDef d : _) -> evaluate c (AppExpr d e1e)
          defs -> evaluatePatternMatch c defs (AppExpr e0e e1e)
      AppExpr _ _ ->
        do s <- leadSymbol e0e
           evaluatePatternMatch c (definitions s) (AppExpr e0e e1e)
      LambdaExpr s t d ->
        do c' <- simplyAugmentContext c (name s) (definedType s) [ConstantDef e1e]
           evaluate c' d
      FunctionTypeExpr _ _ -> barf ErrFunctionTypeOnAppLHS
      DependentFunctionTypeExpr _ _ _ -> barf ErrFunctionTypeOnAppLHS
evaluate c (LambdaExpr s t d) = return (LambdaExpr s t d)
evaluate c (FunctionTypeExpr a b) =
  do ae <- evaluate c a
     be <- evaluate c b
     return (FunctionTypeExpr ae be)
evaluate c (DependentFunctionTypeExpr s a b) = return (DependentFunctionTypeExpr s a b)

-- Creates a new context which has the given context as parent and has a symbol
-- with the given name, type, and definitions.
simplyAugmentContext :: Context -> String -> Expr -> [Definition] -> Incat Context
simplyAugmentContext parentContext vName vType vDefs =
  do contextId <- popContextId
     return $ _simplyAugmentContext parentContext vName vType vDefs contextId

_simplyAugmentContext :: Context -> String -> Expr -> [Definition] -> Integer -> Context
_simplyAugmentContext parentContext vName vType vDefs contextId =
  let newContext =
        Context {
          contextId = contextId,
          uri = Nothing,
          parentContext = Just parentContext,
          declarations = singleton vName newSymbol,
          importedSymbols = empty
        }
      newSymbol =
        Symbol {
          name = vName,
          definedType = vType,
          definitions = vDefs,
          nativeContext = newContext
        }
    in newContext

-- Gathers the lead symbol in a normalized application expression.
leadSymbol :: Expr -> Incat Symbol
leadSymbol (SymbolExpr s) = return s
leadSymbol (AppExpr e0 e1) = leadSymbol e0
leadSymbol (LambdaExpr _ _ _) = barf ErrExpectedLeadSymbolFoundLambda
leadSymbol (FunctionTypeExpr _ _) = barf ErrExpectedLeadSymbolFoundFunctionType
leadSymbol (DependentFunctionTypeExpr _ _ _) = barf ErrExpectedLeadSymbolFoundFunctionType

-- Checks if the given expr matches any of the given pattern match definitions.
-- Returns the result of evaluating the expr against the first matching definition
-- if one matches, and throws an error if no patterns match. Assumes the
-- subexpressions of the given expr are normalized.
evaluatePatternMatch :: Context -> [Definition] -> Expr -> Incat Expr
evaluatePatternMatch c [] e =
  barf ErrNoPatternMatch
evaluatePatternMatch c ((ConstantDef _):_) e =
  barf ErrExpectedPatternMatchDefGotConstantDef
evaluatePatternMatch c0 ((PatternDef _ p d):defs) e =
  do unifyResult <- unifyExprWithPattern c0 e p
     case unifyResult of
      Just c1 -> evaluate c1 d
      Nothing -> evaluatePatternMatch c0 defs e

-- Takes an expr and a pattern and returns an augmented context in which the
-- pattern variables are defined according to the unification of expr and pattern.
-- That assumes expr can be unified with pattern. If not returns nothing.
-- Assumes expr is evaluated (i.e. in normal form).
unifyExprWithPattern :: Context -> Expr -> Pattern -> Incat (Maybe Context)
unifyExprWithPattern c (AppExpr (SymbolExpr s) e) (AppPat (SymbolPat t) p) =
  if s == t
    then unifyExprWithPattern c e p
    else return Nothing
unifyExprWithPattern c0 (AppExpr e f) (AppPat p q) =
  do unifyResult1 <- unifyExprWithPattern c0 e p
     case unifyResult1 of
       Nothing -> return Nothing
       Just c1 ->
        do unifyResult2 <- unifyExprWithPattern c1 f q
           case unifyResult2 of
             Nothing -> return Nothing
             Just c2 -> return $ Just c2
unifyExprWithPattern c (SymbolExpr s) (SymbolPat t) =
  if definedType s == definedType t -- TODO: check whether evaluated defined types are alpha convertible
    then simplyAugmentContext c (name t) (definedType t) (definitions s)
         >>= return . Just
    else return Nothing
unifyExprWithPattern _ _ _ = return Nothing

--
-- Constructing semantic objects from raw objects while checking coherence
--

--digestContext :: RawContext -> Either Error Context
