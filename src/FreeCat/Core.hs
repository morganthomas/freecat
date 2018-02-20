{-# LANGUAGE TupleSections #-}

-- Core syntactic and semantic definitions
module FreeCat.Core where

import Data.Map as Map
import Data.Maybe (fromMaybe)
import Control.Monad.Trans.Class
import Control.Monad.Trans.State
import Control.Monad.Trans.Except as E
import Control.Monad.IO.Class
import Text.Parsec (SourcePos)

--
-- Errors
--

data Error =
   ErrFunctionTypeOnAppLHS
 | ErrExpectedLeadSymbolFoundLambda
 | ErrExpectedLeadSymbolFoundFunctionType
 | ErrSymbolNotDefined Context (Maybe SourcePos) String
 | ErrAppHeadIsNotFunctionTyped
 | ErrCannotInferImplicitArgumentValue
 | ErrTypeMismatch Context Expr Expr Context Expr Expr
 | ErrIThoughtThisWasImpossible
 | ErrExtraTypeDeclaration
 | ErrEquationWithoutMatchingTypeDeclaration
 | ErrWrongNumberOfArguments
 | ErrCannotUnify (Expr, Expr) (Expr, Expr) RawExpr
 | ErrNotAllowed -- TODO: replace with more specific errors

instance Show Error where
  show ErrFunctionTypeOnAppLHS = "Nonsense: function type on left hand side of function application expression."
  show ErrExpectedLeadSymbolFoundLambda = "Expected lead symbol, found lambda expression. This condition should never occur. There is a bug in FreeCat.Core."
  show ErrExpectedLeadSymbolFoundFunctionType = "Expected lead symbol, found function type. This condition should never occur. There is a bug in FreeCat.Core."
  show (ErrSymbolNotDefined c pos s) = "Symbol not defined: " ++ s
    ++ "\nSource pos: " ++ show pos
    ++ "\nContext:\n" ++ show c
  show ErrAppHeadIsNotFunctionTyped = "Type error: head of function application doesn't have a function type."
  show (ErrTypeMismatch c0 e0 t0 c1 e1 t1) =
    "Failed to match types: "
    ++ "\n  " ++ show e0 ++ " : " ++ show t0
    ++ "\n  " ++ show e1 ++ " : " ++ show t1
  show ErrIThoughtThisWasImpossible = "Something impossible has occurred. There is a bug in FreeCat.Core."
  show ErrExtraTypeDeclaration = "Illegal: declared a type for a symbol twice in one context."
  show ErrEquationWithoutMatchingTypeDeclaration = "Illegal: declared a pattern matching equation without declaring the lead symbol's type first."
  show ErrWrongNumberOfArguments = "Wrong number of arguments"
  show (ErrCannotUnify (e0, e1) (e0orig, e1orig) appE) = "Cannot unify " ++ show e0 ++ " with " ++ show e1
     ++ " which occurred while trying to unify " ++ show e0orig ++ " with " ++ show e1orig
     ++ " which came about while trying to infer the implicit argument values in " ++ show appE
  show ErrNotAllowed = "Not allowed (TODO: more useful error message)"

--
-- Parse trees
--

type RawSymbol = String

rawTypeSymbol :: RawSymbol
rawTypeSymbol = "Type"

data RawExpr =
   RawSymbolExpr SourcePos RawSymbol
 | RawAppExpr SourcePos RawExpr RawExpr
 | RawLambdaExpr SourcePos RawSymbol RawExpr RawExpr
 | RawFunctionTypeExpr SourcePos RawExpr RawExpr
 | RawDependentFunctionTypeExpr SourcePos RawSymbol RawExpr RawExpr
 | RawImplicitDependencyTypeExpr SourcePos RawSymbol RawExpr RawExpr

type RawPattern = RawExpr

rawExprPos :: RawExpr -> SourcePos
rawExprPos (RawSymbolExpr pos _) = pos
rawExprPos (RawAppExpr pos _ _) = pos
rawExprPos (RawLambdaExpr pos _ _ _) = pos
rawExprPos (RawFunctionTypeExpr pos _ _) = pos
rawExprPos (RawDependentFunctionTypeExpr pos _ _ _) = pos
rawExprPos (RawImplicitDependencyTypeExpr pos _ _ _) = pos

instance Show RawExpr where
  show e = showJustRawExpr e ++ " [" ++ show (rawExprPos e) ++ "]"

showJustRawExpr :: RawExpr -> String
showJustRawExpr (RawSymbolExpr pos s) = s
showJustRawExpr (RawAppExpr pos e0 e1) = "(" ++ showJustRawExpr e0 ++ " " ++ showJustRawExpr e1 ++ ")"
showJustRawExpr (RawLambdaExpr pos s a d) = "(\\" ++ s ++ " : " ++ showJustRawExpr a ++ " => " ++ showJustRawExpr d ++ ")"
showJustRawExpr (RawFunctionTypeExpr pos a b) = "(" ++ showJustRawExpr a ++ " -> " ++ showJustRawExpr b ++ ")"
showJustRawExpr (RawDependentFunctionTypeExpr pos s a b) = "((" ++ s ++ " : " ++ showJustRawExpr a ++ ") -> " ++ showJustRawExpr b ++ ")"
showJustRawExpr (RawImplicitDependencyTypeExpr pos s a b) = "({" ++ s ++ " : " ++ showJustRawExpr a ++ "} -> " ++ showJustRawExpr b ++ ")"

rawApplicationHead :: RawExpr -> FreeCat RawExpr
rawApplicationHead e@(RawSymbolExpr _ _) = return e
rawApplicationHead e@(RawLambdaExpr _ _ _ _) = return e
rawApplicationHead (RawAppExpr pos e0 e1) = rawApplicationHead e0
rawApplicationHead (RawFunctionTypeExpr _ _ _) = barf ErrAppHeadIsNotFunctionTyped
rawApplicationHead (RawDependentFunctionTypeExpr _ _ _ _) = barf ErrAppHeadIsNotFunctionTyped
rawApplicationHead (RawImplicitDependencyTypeExpr _ _ _ _) = barf ErrAppHeadIsNotFunctionTyped

rawApplicationArguments :: RawExpr -> [RawExpr]
rawApplicationArguments (RawAppExpr pos e0 e1) = rawApplicationArguments e0 ++ [e1] -- TODO: less consing
rawApplicationArguments x = []

rawPatternLeadSymbol :: RawPattern -> RawSymbol
rawPatternLeadSymbol (RawSymbolExpr pos s) = s
rawPatternLeadSymbol (RawAppExpr pos p q) = rawPatternLeadSymbol p

data RawTypeAssertion = RawTypeAssertion RawSymbol RawExpr
data RawEquation = RawEquation [RawTypeAssertion] RawPattern RawExpr
data RawImport =
   RawImportAsSymbol String String -- uri, name
 | RawImportSelectively String [String] -- uri, symbols to import

data RawDeclaration =
   RawTypeDeclaration SourcePos RawTypeAssertion
 | RawEquationDeclaration SourcePos RawEquation
 | RawImportDeclaration SourcePos RawImport

type RawContext = [RawDeclaration]

--
-- Basic semantic structures
--

-- Patterns must be built using only SymbolExpr and AppExpr
type Pattern = Expr

data Expr =
   SymbolExpr Symbol (Maybe SourcePos)
 | AppExpr Expr Expr (Maybe SourcePos)
 | ImplicitAppExpr Expr Expr (Maybe SourcePos)
 -- Context is the evaluation context for the lambda body
 | LambdaExpr Context Symbol Expr (Maybe SourcePos)
 | FunctionTypeExpr Expr Expr (Maybe SourcePos)
 | DependentFunctionTypeExpr Symbol Expr (Maybe SourcePos)
 | ImplicitDependencyTypeExpr Symbol Expr (Maybe SourcePos)

data Context = Context {
  contextId :: Integer,
  uri :: Maybe String,
  parentContext :: Maybe Context,
  -- includes declarations from parent context
  declarations :: Map.Map String Symbol,
  importedSymbols :: Map.Map String Symbol
}

data Symbol = Symbol {
  name :: String,
  definedType :: Expr,
  declarationSourcePos :: Maybe SourcePos,
  -- all pattern equations have this symbol as their lead symbol
  equations :: [Equation],
  -- the context in which the symbol was originally defined
  nativeContext :: Context
}

data Equation = -- the Context is the evaluation context
  Equation Context [VariableDeclaration] Pattern Expr (Maybe SourcePos)

type VariableDeclaration = Symbol

constantDefinition :: Symbol -> Expr -> Equation
constantDefinition s e = Equation rootContext [] (SymbolExpr s Nothing) e Nothing

-- Type : Type
rootTypeSymbol :: Symbol
rootTypeSymbol =
 Symbol {
   name = rawTypeSymbol,
   definedType = typeOfTypes,
   declarationSourcePos = Nothing,
   equations = [],
   nativeContext = rootContext
 }

typeOfTypes :: Expr
typeOfTypes = SymbolExpr rootTypeSymbol Nothing

rawUndefinedSymbol :: String
rawUndefinedSymbol = "undefined"

-- undefined : {a : Type} -> a
undefinedSymbol :: Symbol
undefinedSymbol =
  let a = Symbol {
            name = "a",
            definedType = typeOfTypes,
            declarationSourcePos = Nothing,
            equations = [],
            nativeContext = rootContext
          }
  in
    Symbol {
      name = rawUndefinedSymbol,
      definedType = ImplicitDependencyTypeExpr a (SymbolExpr a Nothing) Nothing,
      declarationSourcePos = Nothing,
      equations = [],
      nativeContext = rootContext
    }

makeUndefined :: Expr -> Expr
makeUndefined t = (AppExpr (SymbolExpr undefinedSymbol Nothing) t Nothing)

rootContext :: Context
rootContext =
 Context {
   contextId = 0,
   uri = Nothing,
   parentContext = Nothing,
   declarations = Map.fromList [
    (rawTypeSymbol, rootTypeSymbol),
    (rawUndefinedSymbol, undefinedSymbol)
   ],
   importedSymbols = Map.empty
 }

--
-- Eq and Show
--

instance Eq Expr where
  (SymbolExpr s _) == (SymbolExpr t _) = s == t
  (AppExpr a0 b0 _) == (AppExpr a1 b1 _) = a0 == a1 && b0 == b1
  (LambdaExpr c0 s0 b0 _) == (LambdaExpr c1 s1 b1 _) =
    -- alpha convertible lambdas are equal
    (definedType s0) == (definedType s1) && b0 == (substitute s1 (SymbolExpr s0 Nothing) b1)
  (FunctionTypeExpr a0 b0 _) == (FunctionTypeExpr a1 b1 _) = a0 == a1 && b0 == b1
  (DependentFunctionTypeExpr s0 b0 _) == (DependentFunctionTypeExpr s1 b1 _) =
    -- alpha convertible ones are equal
    (definedType s0) == (definedType s1) && b0 == (substitute s1 (SymbolExpr s0 Nothing) b1)
  (FunctionTypeExpr a0 b0 _) == (DependentFunctionTypeExpr s1 b1 _) =
    not (s1 `occursFreeIn` b1) && a0 == (definedType s1) && b0 == b1
  (DependentFunctionTypeExpr s0 b0 _) == (FunctionTypeExpr a1 b1 _) =
    not (s0 `occursFreeIn` b0) && (definedType s0) == a1 && b0 == b1
  (ImplicitDependencyTypeExpr s0 b0 _) == (ImplicitDependencyTypeExpr s1 b1 _) =
    (definedType s0) == (definedType s1) && b0 == (substitute s1 (SymbolExpr s0 Nothing) b1)
  _ == _ = False

instance Eq Symbol where
  s == t = name s == name t && nativeContext s == nativeContext t

instance Eq Context where
  c0 == c1 = contextId c0 == contextId c1

instance Show Context where
  -- TODO: less consing
  show c = Prelude.foldl (++) "" (Map.map showSymbolEquations (declarations c))

showSymbolEquations :: Symbol -> String
showSymbolEquations s = name s ++ " : " ++ show (definedType s) ++ "\n"
  ++ (Prelude.foldl (++) "" $ Prelude.map (\d -> show d ++ "\n") (equations s))

instance Show Symbol where
  show = name

instance Show Equation where
  show (Equation c decls pat e pos) =
    "    " ++ showVariableDeclarationList decls
    ++ show pat ++ " = " ++ show e

showVariableDeclaration :: VariableDeclaration -> String
showVariableDeclaration s = show s ++ " : " ++ show (definedType s)

showVariableDeclarationList :: [VariableDeclaration] -> String
showVariableDeclarationList [] = ""
showVariableDeclarationList (decl:decls) =
  (Prelude.foldl joinByComma (show decl) (Prelude.map showVariableDeclaration decls)) ++ ". "
  where joinByComma a b = a ++ ", " ++ b

instance Show Expr where
  show (SymbolExpr s pos) = name s
  show (AppExpr f g pos) = "(" ++ show f ++ " " ++ show g ++ ")"
  show (ImplicitAppExpr f g pos) = "{" ++ show f ++ " " ++ show g ++ "}"
  show (LambdaExpr c s e pos) = "(\\" ++ name s ++ " : " ++ show (definedType s) ++ " => " ++ show e ++ ")"
  show (FunctionTypeExpr a b pos) = "(" ++ show a ++ " -> " ++ show b ++ ")"
  show (DependentFunctionTypeExpr s b pos) = "((" ++ name s ++ " : " ++ show (definedType s) ++ ") -> " ++ show b ++ ")"
  show (ImplicitDependencyTypeExpr s b pos) = "({" ++ name s ++ " : " ++ show (definedType s) ++ "} -> " ++ show b ++ ")"

--
-- FreeCat monadic meta-context
--

data FreeCatState = FreeCatState {
  nextContextId :: Integer,
  -- keyed by uri
  importedContexts :: Map.Map String Context
}

initialState :: FreeCatState
initialState =
  FreeCatState {
    -- rootContext uses id 0
    nextContextId = 1,
    importedContexts = empty
  }

type FreeCat = StateT FreeCatState (E.ExceptT Error IO)

runFreeCat :: FreeCat a -> IO (Either Error (a, FreeCatState))
runFreeCat f = runExceptT $ runStateT f initialState

ioToFreeCat :: IO (Either Error a) -> FreeCat a
ioToFreeCat m = lift (ExceptT m)

debug :: String -> FreeCat ()
debug s = ioToFreeCat (
    do putStrLn s
       return (Right ())
  )

barf :: Error -> FreeCat a
barf e = lift (E.throwE e)

popContextId :: FreeCat Integer
popContextId =
  do st <- get
     put $ st { nextContextId = 1 + nextContextId st }
     return $ nextContextId st

-- Use to extract a from Maybe a when you know that it will be there
certainly :: Maybe a -> FreeCat a
certainly (Just x) = return x
certainly Nothing = barf ErrIThoughtThisWasImpossible

--
-- Dealing with symbols and contexts
--

lookupSymbol :: Context -> String -> Maybe Symbol
lookupSymbol c s =
  case Map.lookup s (declarations c) of
    Just sym -> Just sym
    Nothing -> Map.lookup s (importedSymbols c)

lookupExactSymbol :: Context -> Symbol -> Maybe Symbol
lookupExactSymbol c s =
  case lookupSymbol c (name s) of
    Just t ->
      if s == t
      then Just t
      else Nothing
    Nothing -> Nothing

-- Creates a new context which has the given context as parent and has a symbol
-- with the given name, type, and equations.
augmentContext :: Context -> String -> Maybe Context -> Expr ->
  Maybe SourcePos -> [Equation] -> FreeCat Context
augmentContext parentContext vName vNativeContext vType pos vDefs =
  do contextId <- popContextId
     return $ _augmentContext parentContext vName vNativeContext vType pos vDefs contextId

_augmentContext :: Context -> String -> Maybe Context -> Expr ->
  Maybe SourcePos -> [Equation] -> Integer -> Context
_augmentContext parentContext vName vNativeContext vType pos equations contextId =
  let newContext =
        Context {
          contextId = contextId,
          uri = Nothing,
          parentContext = Just parentContext,
          declarations = Map.insert vName newSymbol (declarations parentContext),
          importedSymbols = (importedSymbols parentContext)
        }
      newSymbol =
        Symbol {
          name = vName,
          definedType = vType,
          declarationSourcePos = pos,
          equations = equations,
          nativeContext = fromMaybe newContext vNativeContext
        }
    in newContext

-- Replaces all free instances of a symbol with an expr in an expr
substitute :: Symbol -> Expr -> Expr -> Expr
substitute s v e@(SymbolExpr s' pos) =
  if s' == s
    then v
    else e
substitute s v (AppExpr a b pos) =
  AppExpr (substitute s v a) (substitute s v b) Nothing
substitute s v e@(LambdaExpr c s' d pos) =
  if s == s'
    then LambdaExpr c (s' { definedType = substitute s v (definedType s') }) d Nothing
    else LambdaExpr c (s' { definedType = substitute s v (definedType s') }) (substitute s v d) Nothing
substitute s v (FunctionTypeExpr a b pos) =
  FunctionTypeExpr (substitute s v a) (substitute s v b) pos
substitute s v e@(DependentFunctionTypeExpr s' b pos) =
  if s == s'
    then DependentFunctionTypeExpr (s' { definedType = substitute s v (definedType s') }) b Nothing
    else DependentFunctionTypeExpr (s' { definedType = substitute s v (definedType s') }) (substitute s v b) Nothing
substitute s v e@(ImplicitDependencyTypeExpr s' b pos) =
  if s == s'
    then ImplicitDependencyTypeExpr (s' { definedType = substitute s v (definedType s') }) b Nothing
    else ImplicitDependencyTypeExpr (s' { definedType = substitute s v (definedType s') }) (substitute s v b) Nothing

-- returns true if the given symbol occurs free in the given expr
occursFreeIn :: Symbol -> Expr -> Bool
s `occursFreeIn` (SymbolExpr s' _) = s == s'
s `occursFreeIn` (AppExpr a b _) = s `occursFreeIn` a || s `occursFreeIn` b
s `occursFreeIn` (LambdaExpr c s' e _) =
  s `occursFreeIn` (definedType s')
  || (s /= s' && occursFreeIn s e)
s `occursFreeIn` (FunctionTypeExpr a b _) = s `occursFreeIn` a || s `occursFreeIn` b
s `occursFreeIn` (DependentFunctionTypeExpr s' b _) =
  s `occursFreeIn` (definedType s')
  || (s /= s' && s `occursFreeIn` b)

--
-- Dealing with expressions
--

-- Gathers the head of a function application expression.
applicationHead :: Expr -> FreeCat Expr
applicationHead e@(SymbolExpr _ _) = return e
applicationHead e@(LambdaExpr _ _ _ _) = return e
applicationHead (AppExpr e0 e1 pos) = applicationHead e0
applicationHead (FunctionTypeExpr _ _ _) = barf ErrAppHeadIsNotFunctionTyped
applicationHead (DependentFunctionTypeExpr _ _ _) = barf ErrAppHeadIsNotFunctionTyped
applicationHead (ImplicitDependencyTypeExpr _ _ _) = barf ErrAppHeadIsNotFunctionTyped

-- Gathers the lead symbol in a normalized application expression.
leadSymbol :: Expr -> FreeCat Symbol
leadSymbol (SymbolExpr s pos) = return s
leadSymbol (AppExpr e0 e1 pos) = leadSymbol e0
leadSymbol (LambdaExpr _ _ _ _) = barf ErrExpectedLeadSymbolFoundLambda
leadSymbol (FunctionTypeExpr _ _ _) = barf ErrExpectedLeadSymbolFoundFunctionType
leadSymbol (DependentFunctionTypeExpr _ _ _) = barf ErrExpectedLeadSymbolFoundFunctionType
leadSymbol (ImplicitDependencyTypeExpr _ _ _) = barf ErrExpectedLeadSymbolFoundFunctionType

domainType :: Error -> Expr -> FreeCat Expr
domainType err (FunctionTypeExpr a b pos) = return a
domainType err (DependentFunctionTypeExpr s b pos) = return (definedType s)
domainType err (ImplicitDependencyTypeExpr s b pos) = return (definedType s)
domainType err _ = barf err

codomainType :: Expr -> Expr -> FreeCat Expr
codomainType (FunctionTypeExpr a b _) x = return a
codomainType (DependentFunctionTypeExpr s b _) x = return (substitute s x b)
codomainType _ _ = barf ErrIThoughtThisWasImpossible -- not really, todo describe this error

-- Gathers the types of the explicit arguments given a function type
explicitArgumentTypes :: Expr -> [Expr]
explicitArgumentTypes (FunctionTypeExpr a b _) = (a : explicitArgumentTypes b)
explicitArgumentTypes (DependentFunctionTypeExpr s@(Symbol { definedType = a }) b _) = (a  : explicitArgumentTypes b)
explicitArgumentTypes (ImplicitDependencyTypeExpr s b _) = explicitArgumentTypes b
explicitArgumentTypes _ = []
