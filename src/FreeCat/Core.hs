{-# LANGUAGE TupleSections #-}

-- Core syntactic and semantic definitions
-- The central processing unit
module FreeCat.Core where

import Data.Map as Map
import Control.Monad (mapM, foldM)
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
 | ErrExpectedPatternMatchDefGotConstantDef
 | ErrSymbolNotDefined String
 | ErrAppHeadIsNotFunctionTyped
 | ErrTypeMismatch
 | ErrIThoughtThisWasImpossible
 | ErrExtraTypeDeclaration
 | ErrEquationWithoutMatchingTypeDeclaration
 deriving (Show)

--
-- Parse trees
--

type RawSymbol = String

rawTypeSymbol :: RawSymbol
rawTypeSymbol = "Type"

data RawExpr =
   RawSymbolExpr RawSymbol
 | RawAppExpr RawExpr RawExpr
 | RawLambdaExpr RawSymbol RawExpr RawExpr
 | RawFunctionTypeExpr RawExpr RawExpr
 | RawDependentFunctionTypeExpr RawSymbol RawExpr RawExpr

data RawPattern =
   RawSymbolPat RawSymbol
 | RawAppPat RawPattern RawPattern

rawPatternLeadSymbol :: RawPattern -> RawSymbol
rawPatternLeadSymbol (RawSymbolPat s) = s
rawPatternLeadSymbol (RawAppPat p q) = rawPatternLeadSymbol p

patToExpr :: RawPattern -> RawExpr
patToExpr (RawSymbolPat s) = RawSymbolExpr s
patToExpr (RawAppPat p q) = RawAppExpr (patToExpr p) (patToExpr q)

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
  -- all pattern definitions have this symbol as their lead symbol
  definitions :: [Definition],
  -- the context in which the symbol was originally defined
  nativeContext :: Context,
  -- the context to use for evaluating the symbol's definition
  evaluationContext :: Maybe Context
}

instance Eq Symbol where
  -- temporarily loosen symbol equality relation
  --s == t = name s == name t && nativeContext s == nativeContext t
  s == t = name s == name t

data Definition =
   ConstantDef Expr (Maybe SourcePos)
 | PatternDef [VariableDeclaration] Pattern Expr (Maybe SourcePos)

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

instance Show Expr where
  show (SymbolExpr s) = name s
  show (AppExpr f g) = "(" ++ show f ++ " " ++ show g ++ ")"
  show (LambdaExpr s t e) = "(\\" ++ name s ++ " : " ++ show t ++ " => " ++ show e ++ ")"
  show (FunctionTypeExpr a b) = "(" ++ show a ++ " -> " ++ show b ++ ")"
  show (DependentFunctionTypeExpr s a b) = "((" ++ name s ++ " : " ++ show a ++ ") -> " ++ show b ++ ")"

lookupSymbol :: Context -> String -> Maybe Symbol
lookupSymbol c s =
  case Map.lookup s (declarations c) of
    Just sym -> Just sym
    Nothing -> Map.lookup s (importedSymbols c)

rootContext :: Context
rootContext =
  Context {
    contextId = 0,
    uri = Nothing,
    parentContext = Nothing,
    declarations = Map.singleton rawTypeSymbol rootTypeSymbol,
    importedSymbols = empty
  }

rootTypeSymbol :: Symbol
rootTypeSymbol =
  Symbol {
    name = rawTypeSymbol,
    definedType = typeOfTypes,
    declarationSourcePos = Nothing,
    definitions = [],
    nativeContext = rootContext,
    evaluationContext = Nothing
  }

evaluationOrNativeContext :: Symbol -> Context
evaluationOrNativeContext s =
  case evaluationContext s of
    Just c -> c
    Nothing -> nativeContext s

typeOfTypes :: Expr
typeOfTypes = SymbolExpr rootTypeSymbol

instance Eq Context where
  c0 == c1 = contextId c0 == contextId c1

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
-- Evaluation
--

evaluate :: Context -> Expr -> FreeCat Expr
evaluate c (SymbolExpr s) =
  case definitions s of
    (ConstantDef e pos : _) ->
      evaluate (evaluationOrNativeContext s) e
    (PatternDef [] (SymbolPat _) e pos : _) ->
      evaluate (evaluationOrNativeContext s) e
    _ -> return (SymbolExpr s)
evaluate c (AppExpr e0 e1) =
  do e0e <- evaluate c e0
     e1e <- evaluate c e1
     case e0e of
      SymbolExpr s ->
        case definitions s of
          [] -> return (AppExpr e0e e1e)
          (ConstantDef d pos : _) ->
            evaluate (evaluationOrNativeContext s) (AppExpr d e1e)
          defs ->
            -- TODO: if pattern defs for a symbol can originate from
            -- different contexts, then those defs can have different
            -- evaluation contexts
            evaluatePatternMatch (evaluationOrNativeContext s) defs (AppExpr e0e e1e)
      AppExpr _ _ ->
        do s <- leadSymbol e0e
           evaluatePatternMatch (evaluationOrNativeContext s) (definitions s) (AppExpr e0e e1e)
      LambdaExpr s t d ->
        do ec' <- simplyAugmentContext (evaluationOrNativeContext s)
                     (name s) (definedType s) Nothing [ConstantDef e1e Nothing]
           evaluate ec' d
      FunctionTypeExpr _ _ -> barf ErrFunctionTypeOnAppLHS
      DependentFunctionTypeExpr _ _ _ -> barf ErrFunctionTypeOnAppLHS
evaluate c (LambdaExpr s t d) =
  do c' <- simplyAugmentContext c (name s) t (declarationSourcePos s) []
     s' <- certainly (lookupSymbol c' (name s))
     return (LambdaExpr s' t d)
evaluate c (FunctionTypeExpr a b) =
  do ae <- evaluate c a
     be <- evaluate c b
     return (FunctionTypeExpr ae be)
evaluate c (DependentFunctionTypeExpr s a b) = return (DependentFunctionTypeExpr s a b)

-- Creates a new context which has the given context as parent and has a symbol
-- with the given name, type, and definitions.
simplyAugmentContext :: Context -> String -> Expr -> Maybe SourcePos ->
  [Definition] -> FreeCat Context
simplyAugmentContext parentContext vName vType pos vDefs =
  do contextId <- popContextId
     return $ _simplyAugmentContext parentContext vName vType pos vDefs contextId

_simplyAugmentContext :: Context -> String -> Expr -> Maybe SourcePos ->
  [Definition] -> Integer -> Context
_simplyAugmentContext parentContext vName vType pos vDefs contextId =
  let newContext =
        Context {
          contextId = contextId,
          uri = Nothing,
          parentContext = Just parentContext,
          declarations = Map.insert vName newSymbol (declarations parentContext),
          importedSymbols = Map.empty
        }
      newSymbol =
        Symbol {
          name = vName,
          definedType = vType,
          declarationSourcePos = pos,
          definitions = vDefs,
          nativeContext = newContext,
          evaluationContext = Nothing
        }
    in newContext

-- Gathers the lead symbol in a normalized application expression.
leadSymbol :: Expr -> FreeCat Symbol
leadSymbol (SymbolExpr s) = return s
leadSymbol (AppExpr e0 e1) = leadSymbol e0
leadSymbol (LambdaExpr _ _ _) = barf ErrExpectedLeadSymbolFoundLambda
leadSymbol (FunctionTypeExpr _ _) = barf ErrExpectedLeadSymbolFoundFunctionType
leadSymbol (DependentFunctionTypeExpr _ _ _) = barf ErrExpectedLeadSymbolFoundFunctionType

-- Checks if the given expr matches any of the given pattern match definitions.
-- Returns the result of evaluating the expr against the first matching definition
-- if one matches, and throws an error if no patterns match. Assumes the
-- subexpressions of the given expr are normalized.
evaluatePatternMatch :: Context -> [Definition] -> Expr -> FreeCat Expr
evaluatePatternMatch c [] e = return e
evaluatePatternMatch c ((ConstantDef _ _):_) e =
  barf ErrExpectedPatternMatchDefGotConstantDef
evaluatePatternMatch c0 ((PatternDef _ p d pos):defs) e =
  do unifyResult <- unifyExprWithPattern c0 e p
     case unifyResult of
      Just c1 -> evaluate c1 d
      Nothing -> evaluatePatternMatch c0 defs e

-- Takes an expr and a pattern and returns an augmented context in which the
-- pattern variables are defined according to the unification of expr and pattern.
-- That assumes expr can be unified with pattern. If not returns nothing.
-- Assumes expr is evaluated (i.e. in normal form).
unifyExprWithPattern :: Context -> Expr -> Pattern -> FreeCat (Maybe Context)
unifyExprWithPattern c e pat =
  do unifyResult <- _unifyExprWithPattern (c, Map.empty) e pat
     case unifyResult of
       Just (c, matches) -> return (Just c)
       Nothing -> return Nothing

_unifyExprWithPattern :: (Context, Map String Expr) -> Expr -> Pattern -> FreeCat (Maybe (Context, Map String Expr))
_unifyExprWithPattern (c, matches) e (SymbolPat t) =
  case Map.lookup (name t) matches of
    Just v ->
      -- temporarily made pattern matching easier
      return (Just (c, matches))
      --if e == v -- TODO: weaken equivalence notion?
        --then return (Just (c, matches))
        --else return Nothing
    Nothing ->
      case lookupSymbol c (name t) of
       Just s ->
        case e of
          SymbolExpr u ->
            if u == t
              then return (Just (c, matches))
              else return Nothing
          _ -> return Nothing
       Nothing -> do
         c' <- simplyAugmentContext c (name t) (definedType t) Nothing [ConstantDef e Nothing]
         return (Just (c', Map.insert (name t) e matches))
_unifyExprWithPattern (c0, matches0) (AppExpr e f) (AppPat p q) =
  do unifyResult1 <- _unifyExprWithPattern (c0, matches0) e p
     case unifyResult1 of
       Nothing -> return Nothing
       Just (c1, matches1) ->
        do unifyResult2 <- _unifyExprWithPattern (c1, matches1) f q
           case unifyResult2 of
             Nothing -> return Nothing
             something@(Just (c2, matches2)) -> return something
_unifyExprWithPattern _ _ _ = return Nothing

--
-- Constructing semantic objects from raw objects while checking coherence
--

digestContext :: RawContext -> FreeCat Context
digestContext decls =
  do c <- foldM addToContext rootContext decls
     completeContext c

addToContext :: Context -> Positioned RawDeclaration -> FreeCat Context
addToContext c (RawTypeDeclaration assertion, pos) =
  digestTypeAssertion c (assertion, Just pos)
addToContext c (RawImportDeclaration _, pos) = error "import not implemented"
addToContext c (RawEquationDeclaration (RawEquation rawdecls rawpat rawdef), pos) =
 case lookupSymbol c (rawPatternLeadSymbol rawpat) of
   Nothing -> barf ErrEquationWithoutMatchingTypeDeclaration
   Just sym ->
     do cPat <- foldM digestTypeAssertion c (Prelude.map (,Nothing) rawdecls)
        pat <- digestPattern cPat rawpat
        (def, defType) <- digestExpr cPat rawdef
        --assertTypesMatch cPat defType (nativeContext sym) (definedType sym)
        decls <- mapM (digestVarDecl cPat) rawdecls
        simplyAugmentContext c (name sym) (definedType sym) (declarationSourcePos sym)
          (definitions sym ++ [ (PatternDef decls pat def (Just pos)) ]) -- TODO: less consing

digestTypeAssertion :: Context -> (RawTypeAssertion, Maybe SourcePos) -> FreeCat Context
digestTypeAssertion c (RawTypeAssertion s rawt, pos) =
  case lookupSymbol c s of
    Just _ -> barf ErrExtraTypeDeclaration
    Nothing ->
      do (t, tt) <- digestExpr c rawt
         --assertTypesMatch c tt rootContext typeOfTypes
         c' <- simplyAugmentContext c s t pos []
         return c'

digestPattern :: Context -> RawPattern -> FreeCat Pattern
digestPattern c (RawSymbolPat s) =
  case lookupSymbol c s of
    Just sym -> return (SymbolPat sym)
    Nothing -> barf (ErrSymbolNotDefined s)
digestPattern c (RawAppPat p q) =
  do pd <- digestPattern c p
     pq <- digestPattern c q
     return (AppPat pd pq)

-- cPat is assumed to contain a declaration generated from this type
-- assertion via digestTypeAssertion
digestVarDecl :: Context -> RawTypeAssertion -> FreeCat VariableDeclaration
digestVarDecl cPat (RawTypeAssertion s _) =
  do sym <- certainly (lookupSymbol cPat s)
     return (VarDecl sym (definedType sym))


-- Assumes all symbols used in RawExpr are defined in Context.
-- Returns a pair of the digested expr and its inferred type.
digestExpr :: Context -> RawExpr -> FreeCat (Expr, Expr)
digestExpr c (RawSymbolExpr s) =
  case lookupSymbol c s of
    Just sym -> return (SymbolExpr sym, definedType sym)
    Nothing -> barf (ErrSymbolNotDefined s)
digestExpr c (RawAppExpr e0 e1) =
  do (e0d, e0dType) <- digestExpr c e0
     (e1d, e1dType) <- digestExpr c e1
     e0dTypeNorm <- evaluate c e0dType
     appType <- case e0dType of
       FunctionTypeExpr a b ->
         do --assertTypesMatch c a c e1dType
            return b
       DependentFunctionTypeExpr s a b ->
         do --assertTypesMatch c a c e1dType
            c' <- simplyAugmentContext c (name s) a Nothing [ConstantDef e1d Nothing]
            bEv <- evaluate c' b
            return bEv
       _ -> barf ErrAppHeadIsNotFunctionTyped
     return ((AppExpr e0d e1d), appType)
digestExpr c (RawLambdaExpr s t d) =
  do (td, tdType) <- digestExpr c t
     --assertTypesMatch c tdType rootContext typeOfTypes
     c' <- simplyAugmentContext c s td Nothing []
     (dd, ddType) <- digestExpr c' d
     sym <- certainly (lookupSymbol c' s)
     return (
       (LambdaExpr sym td dd),
       (DependentFunctionTypeExpr sym tdType ddType)
      )
digestExpr c (RawFunctionTypeExpr a b) =
  do (ad, adType) <- digestExpr c a
     --assertTypesMatch c adType rootContext typeOfTypes
     (bd, bdType) <- digestExpr c b
     --assertTypesMatch c bdType rootContext typeOfTypes
     return (FunctionTypeExpr ad bd, typeOfTypes)
digestExpr c (RawDependentFunctionTypeExpr s a b) =
  do (ad, adType) <- digestExpr c a
     --assertTypesMatch c adType rootContext typeOfTypes
     c' <- simplyAugmentContext c s ad Nothing []
     sym <- certainly (lookupSymbol c' s)
     (bd, bdType) <- digestExpr c' b
     --assertTypesMatch c' bdType rootContext typeOfTypes
     return (DependentFunctionTypeExpr sym ad bd, typeOfTypes)

-- Throws an error unless the two exprs match as types. For now this
-- simply means their normal forms are syntactically equal.
assertTypesMatch :: Context -> Expr -> Context -> Expr -> FreeCat ()
assertTypesMatch ac a bc b =
  do aEv <- evaluate ac a
     bEv <- evaluate bc b
     -- TODO: use a looser equivalence notion than == (alpha-convertibility?)
     if aEv == bEv then return () else barf ErrTypeMismatch

completeContext :: Context -> FreeCat Context
completeContext c =
  do contextId <- popContextId
     let completedContext = Context {
             contextId = contextId,
             uri = (uri c),
             parentContext = Just rootContext,
             declarations = Map.map (addEvaluationContextToSymbol completedContext) (declarations c),
             importedSymbols = Map.empty
           }
       in return completedContext

addEvaluationContextToSymbol :: Context -> Symbol -> Symbol
addEvaluationContextToSymbol ec s =
  Symbol {
    name = name s,
    definedType = addEvaluationContextToExpr ec (definedType s),
    declarationSourcePos = declarationSourcePos s,
    definitions = Prelude.map (addEvaluationContextToDefinition ec) (definitions s),
    nativeContext = nativeContext s,
    evaluationContext = Just ec
  }

addEvaluationContextToExpr :: Context -> Expr -> Expr
addEvaluationContextToExpr ec (SymbolExpr s) =
  case Map.lookup (name s) (declarations ec) of
    Just s' ->
      if nativeContext s == nativeContext s'
        then SymbolExpr s'
        else SymbolExpr s
    Nothing -> SymbolExpr s
addEvaluationContextToExpr ec (AppExpr f x) =
  let f' = addEvaluationContextToExpr ec f
      x' = addEvaluationContextToExpr ec x
    in AppExpr f' x'
addEvaluationContextToExpr ec (LambdaExpr s t d) =
  let t' = addEvaluationContextToExpr ec t
      d' = addEvaluationContextToExpr ec d
    in LambdaExpr s t' d'

addEvaluationContextToPattern :: Context -> Pattern -> Pattern
addEvaluationContextToPattern ec (SymbolPat s) =
  case Map.lookup (name s) (declarations ec) of
    Just s' ->
      if s == s' -- iff nativeContext s == nativeContext s', since we know name s == name s'
        then -- even though s == s', s' has the evaluation context added whereas s does not
          SymbolPat s'
        else -- s' is some other symbol not declared in ec.
          -- this is right because we're not adding an evaluation context
          -- to symbols outside the evaluation context
          SymbolPat s
    Nothing -> SymbolPat s
addEvaluationContextToPattern ec (AppPat f x) =
  let f' = addEvaluationContextToPattern ec f
      x' = addEvaluationContextToPattern ec x
    in AppPat f' x'

addEvaluationContextToVariableDeclaration :: Context -> VariableDeclaration -> VariableDeclaration
addEvaluationContextToVariableDeclaration ec (VarDecl s t) =
  let t' = addEvaluationContextToExpr ec t
    in VarDecl s t'

addEvaluationContextToDefinition :: Context -> Definition -> Definition
addEvaluationContextToDefinition ec (ConstantDef e pos) =
  let e' = addEvaluationContextToExpr ec e'
    in (ConstantDef e' pos)
addEvaluationContextToDefinition ec (PatternDef decls pat e pos) =
  let decls' = Prelude.map (addEvaluationContextToVariableDeclaration ec) decls
      pat' = addEvaluationContextToPattern ec pat
      e' = addEvaluationContextToExpr ec e
    in (PatternDef decls' pat' e' pos)
