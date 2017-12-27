{-# LANGUAGE TupleSections #-}

-- Core syntactic and semantic definitions
-- The central processing unit
module FreeCat.Core where

import Data.Map as Map
import Data.Maybe (fromMaybe)
import Control.Monad.Trans.Class
import Control.Monad.Trans.State
import Control.Monad.Trans.Except as E
import Control.Monad.IO.Class
import Text.Parsec (SourcePos)

type Positioned a = (a, SourcePos)

--
-- Errors
--

data Error =
   ErrFunctionTypeOnAppLHS
 | ErrExpectedLeadSymbolFoundLambda
 | ErrExpectedLeadSymbolFoundFunctionType
 | ErrSymbolNotDefined Context (Maybe SourcePos) String
 | ErrAppHeadIsNotFunctionTyped
 | ErrTypeMismatch Context Expr Expr Context Expr Expr
 | ErrIThoughtThisWasImpossible
 | ErrExtraTypeDeclaration
 | ErrEquationWithoutMatchingTypeDeclaration

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

type RawPattern = RawExpr

rawPatternLeadSymbol :: RawPattern -> RawSymbol
rawPatternLeadSymbol (RawSymbolExpr pos s) = s
rawPatternLeadSymbol (RawAppExpr pos p q) = rawPatternLeadSymbol p

data RawTypeAssertion = RawTypeAssertion RawSymbol RawExpr
data RawEquation = RawEquation [RawTypeAssertion] RawPattern RawExpr
data RawImport =
   RawImportAsSymbol String String -- uri, name
 | RawImportSelectively String [String] -- uri, symbols to import

data RawDeclaration =
   RawTypeDeclaration RawTypeAssertion
 | RawEquationDeclaration RawEquation
 | RawImportDeclaration RawImport

type RawContext = [Positioned RawDeclaration]

--
-- Basic semantic structures
--

-- Patterns must be built using only SymbolExpr and AppExpr
type Pattern = Expr

data Expr =
 -- last argument of type Expr is the expression's type
   SymbolExpr Symbol Expr (Maybe SourcePos)
 | AppExpr Expr Expr Expr (Maybe SourcePos)
 -- Context is the evaluation context for the lambda body
 -- Expr arguments are (in order) the variable type, the definition, and the
 -- type of the whole lambda expr
 | LambdaExpr Context Symbol Expr Expr Expr (Maybe SourcePos)
 -- type is necessarily Type, so expression's type isn't included
 | FunctionTypeExpr Expr Expr (Maybe SourcePos)
 | DependentFunctionTypeExpr Symbol Expr Expr (Maybe SourcePos)

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

data VariableDeclaration = VarDecl Symbol Expr

constantDefinition :: Symbol -> Expr -> Expr -> Equation
constantDefinition s t e = Equation rootContext [] (SymbolExpr s t Nothing) e Nothing

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
typeOfTypes = SymbolExpr rootTypeSymbol typeOfTypes Nothing

rootContext :: Context
rootContext =
 Context {
   contextId = 0,
   uri = Nothing,
   parentContext = Nothing,
   declarations = Map.singleton rawTypeSymbol rootTypeSymbol,
   importedSymbols = Map.empty
 }

-- Gathers the lead symbol in a normalized application expression.
leadSymbol :: Expr -> FreeCat Symbol
leadSymbol (SymbolExpr s t pos) = return s
leadSymbol (AppExpr e0 e1 t pos) = leadSymbol e0
leadSymbol (LambdaExpr _ _ _ _ _ _) = barf ErrExpectedLeadSymbolFoundLambda
leadSymbol (FunctionTypeExpr _ _ _) = barf ErrExpectedLeadSymbolFoundFunctionType
leadSymbol (DependentFunctionTypeExpr _ _ _ _) = barf ErrExpectedLeadSymbolFoundFunctionType

lookupSymbol :: Context -> String -> Maybe Symbol
lookupSymbol c s =
  case Map.lookup s (declarations c) of
    Just sym -> Just sym
    Nothing -> Map.lookup s (importedSymbols c)

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

instance Eq Expr where
  (SymbolExpr s _ _) == (SymbolExpr t _ _) = s == t
  (AppExpr a0 b0 _ _) == (AppExpr a1 b1 _ _) = a0 == a1 && b0 == b1
  (LambdaExpr c0 s0 a0 b0 t0 _) == (LambdaExpr c1 s1 a1 b1 t1 _) =
    a0 == a1 && b0 == (substitute s1 (SymbolExpr s0 a0 Nothing) b1)
  (FunctionTypeExpr a0 b0 _) == (FunctionTypeExpr a1 b1 _) = a0 == a1 && b0 == b1
  (DependentFunctionTypeExpr s0 a0 b0 _) == (DependentFunctionTypeExpr s1 a1 b1 _) =
    a0 == a1 && b0 == (substitute s1 (SymbolExpr s0 a0 Nothing) b1)
  (FunctionTypeExpr a0 b0 _) == (DependentFunctionTypeExpr s1 a1 b1 _) =
    not (s1 `occursFreeIn` b1) && a0 == a1 && b0 == b1
  (DependentFunctionTypeExpr s0 a0 b0 _) == (FunctionTypeExpr a1 b1 _) =
    not (s0 `occursFreeIn` b0) && a0 == a1 && b0 == b1
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

instance Show VariableDeclaration where
  show (VarDecl s e) = show s ++ " : " ++ show e

showVariableDeclarationList :: [VariableDeclaration] -> String
showVariableDeclarationList [] = ""
showVariableDeclarationList (decl:decls) =
  (Prelude.foldl joinByComma (show decl) (Prelude.map show decls)) ++ ". "
  where joinByComma a b = a ++ ", " ++ b

instance Show Expr where
  show (SymbolExpr s t pos) = name s
  show (AppExpr f g t pos) = "(" ++ show f ++ " " ++ show g ++ ")"
  show (LambdaExpr c s t e lt pos) = "(\\" ++ name s ++ " : " ++ show t ++ " => " ++ show e ++ ")"
  show (FunctionTypeExpr a b pos) = "(" ++ show a ++ " -> " ++ show b ++ ")"
  show (DependentFunctionTypeExpr s a b pos) = "((" ++ name s ++ " : " ++ show a ++ ") -> " ++ show b ++ ")"

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
-- Dealing with variables
--

-- Replaces all free instances of a symbol with an expr in an expr
substitute :: Symbol -> Expr -> Expr -> Expr
substitute s v e@(SymbolExpr s' t pos) =
  if s' == s
    then v
    else e
substitute s v (AppExpr a b t pos) =
  -- TODO: is this correct for t?
  AppExpr (substitute s v a) (substitute s v b) (substitute s v t) Nothing
substitute s v e@(LambdaExpr c s' t d lt pos) =
  -- TODO: is this correct for lt?
  if s == s'
    then LambdaExpr c s' (substitute s v t) d (substitute s v lt) Nothing
    else LambdaExpr c s' (substitute s v t) (substitute s v d) (substitute s v lt) Nothing
substitute s v (FunctionTypeExpr a b pos) =
  FunctionTypeExpr (substitute s v a) (substitute s v b) pos
substitute s v e@(DependentFunctionTypeExpr s' a b pos) =
  if s == s'
    then DependentFunctionTypeExpr s' (substitute s v a) b Nothing
    else DependentFunctionTypeExpr s' (substitute s v a) (substitute s v b) Nothing

-- returns true if the given symbol occurs free in the given expr
occursFreeIn :: Symbol -> Expr -> Bool
s `occursFreeIn` (SymbolExpr s' _ _) = s == s'
s `occursFreeIn` (AppExpr a b _ _) = s `occursFreeIn` a || s `occursFreeIn` b
s `occursFreeIn` (LambdaExpr c s' t e _ _) =
  s `occursFreeIn` t
  || (s /= s' && occursFreeIn s e)
s `occursFreeIn` (FunctionTypeExpr a b _) = s `occursFreeIn` a || s `occursFreeIn` b
s `occursFreeIn` (DependentFunctionTypeExpr s' a b _) =
  s `occursFreeIn` a
  || (s /= s' && s `occursFreeIn` b)
