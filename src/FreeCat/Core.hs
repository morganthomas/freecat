{-# LANGUAGE TupleSections #-}

-- Core syntactic and semantic definitions
-- The central processing unit
module FreeCat.Core where

import Data.Map as Map
import Data.Maybe (fromMaybe)
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
  show ErrExpectedPatternMatchDefGotConstantDef = "Illegal: found a constant definition for a symbol with pattern match definitions. A symbol can have exactly one constant definition, or any number of pattern match definitions, but not both."
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

data RawPattern =
   RawSymbolPat RawSymbol
 | RawAppPat RawPattern RawPattern

rawPatternLeadSymbol :: RawPattern -> RawSymbol
rawPatternLeadSymbol (RawSymbolPat s) = s
rawPatternLeadSymbol (RawAppPat p q) = rawPatternLeadSymbol p

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

instance Show Context where
  -- TODO: less consing
  show c = Prelude.foldl (++) "" (Map.map showSymbolDefinition (declarations c))

showSymbolDefinition :: Symbol -> String
showSymbolDefinition s = name s ++ " : " ++ show (definedType s) ++ "\n"
  ++ (Prelude.foldl (++) "" $ Prelude.map (\d -> show d ++ "\n") (definitions s))

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
  s == t =
    -- for now, freak out if there are symbols with the same name and diff. contexts.
    -- this case is actually legal but for now it won't occur on purpose.
    if name s == name t && nativeContext s /= nativeContext t
      then error ("same symbol different context: " ++ name s ++ "\n" ++ show (nativeContext s) ++ "\n--\n" ++ show (nativeContext t))
      else name s == name t && nativeContext s == nativeContext t

instance Show Symbol where
  show = name

data Definition =
   ConstantDef Expr (Maybe SourcePos)
 | PatternDef [VariableDeclaration] Pattern Expr (Maybe SourcePos)

instance Show Definition where
  show (ConstantDef e pos) = "    " ++ show e
  show (PatternDef decls pat e pos) =
    "    " ++ showVariableDeclarationList decls
    ++ show pat ++ " = " ++ show e

data VariableDeclaration = VarDecl Symbol Expr

instance Show VariableDeclaration where
  show (VarDecl s e) = show s ++ " : " ++ show e

showVariableDeclarationList :: [VariableDeclaration] -> String
showVariableDeclarationList [] = ""
showVariableDeclarationList (decl:decls) =
  (Prelude.foldl joinByComma (show decl) (Prelude.map show decls)) ++ ". "
  where joinByComma a b = a ++ ", " ++ b

data Pattern =
  -- the Expr argument is the type
   SymbolPat Symbol Expr
 | AppPat Pattern Pattern Expr

instance Show Pattern where
  show (SymbolPat s t) = name s
  show (AppPat f g t) = "("  ++ show f ++ " " ++ show g ++ ")"

data Expr =
 -- last argument of type Expr is the expression's type
   SymbolExpr Symbol Expr (Maybe SourcePos)
 | AppExpr Expr Expr Expr (Maybe SourcePos)
 | LambdaExpr Symbol Expr Expr Expr (Maybe SourcePos)
 -- type is necessarily Type, so expression's type isn't included
 | FunctionTypeExpr Expr Expr (Maybe SourcePos)
 | DependentFunctionTypeExpr Symbol Expr Expr (Maybe SourcePos)

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

instance Eq Expr where
  (SymbolExpr s _ _) == (SymbolExpr t _ _) = s == t
  (AppExpr a0 b0 _ _) == (AppExpr a1 b1 _ _) = a0 == a1 && b0 == b1
  (LambdaExpr s0 a0 b0 t0 _) == (LambdaExpr s1 a1 b1 t1 _) =
    a0 == a1 && b0 == (substitute s1 (SymbolExpr s0 a0 Nothing) b1)
  (FunctionTypeExpr a0 b0 _) == (FunctionTypeExpr a1 b1 _) = a0 == a1 && b0 == b1
  (DependentFunctionTypeExpr s0 a0 b0 _) == (DependentFunctionTypeExpr s1 a1 b1 _) =
    a0 == a1 && b0 == (substitute s1 (SymbolExpr s0 a0 Nothing) b1)
  (FunctionTypeExpr a0 b0 _) == (DependentFunctionTypeExpr s1 a1 b1 _) =
    not (s1 `occursFreeIn` b1) && a0 == a1 && b0 == b1
  (DependentFunctionTypeExpr s0 a0 b0 _) == (FunctionTypeExpr a1 b1 _) =
    not (s0 `occursFreeIn` b0) && a0 == a1 && b0 == b1
  _ == _ = False

patternToExpr :: Pattern -> Expr
patternToExpr (SymbolPat s t) = SymbolExpr s t Nothing
patternToExpr (AppPat a b t) = AppExpr (patternToExpr a) (patternToExpr b) t Nothing

typeOf :: Expr -> Expr
typeOf (SymbolExpr s t pos) = t
typeOf (AppExpr a b t pos) = t
typeOf (LambdaExpr s a e t pos) = t
typeOf (FunctionTypeExpr _ _ _) = typeOfTypes
typeOf (DependentFunctionTypeExpr _ _ _ _) = typeOfTypes

instance Show Expr where
  show (SymbolExpr s t pos) = name s
  show (AppExpr f g t pos) = "(" ++ show f ++ " " ++ show g ++ ")"
  show (LambdaExpr s t e lt pos) = "(\\" ++ name s ++ " : " ++ show t ++ " => " ++ show e ++ ")"
  show (FunctionTypeExpr a b pos) = "(" ++ show a ++ " -> " ++ show b ++ ")"
  show (DependentFunctionTypeExpr s a b pos) = "((" ++ name s ++ " : " ++ show a ++ ") -> " ++ show b ++ ")"

lookupSymbol :: Context -> String -> Maybe Symbol
lookupSymbol c s =
  case Map.lookup s (declarations c) of
    Just sym -> Just sym
    Nothing -> Map.lookup s (importedSymbols c)

evaluationOrNativeContext :: Symbol -> Context
evaluationOrNativeContext s =
  case evaluationContext s of
    Just c -> c
    Nothing -> nativeContext s

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

getEvaluationContext :: Symbol -> FreeCat Context
getEvaluationContext = certainly . evaluationContext

--
-- Evaluation
--

evaluate :: Context -> Expr -> FreeCat Expr
evaluate c (SymbolExpr s t pos) = do
  debug ("evaluate c " ++ (name s) ++ " where c = " ++ show c ++ "\n~~\n")
  case lookupSymbol c (name s) of
    Nothing ->
      barf (ErrSymbolNotDefined c pos (name s))
    Just s' ->
      case definitions s' of
        (ConstantDef e pos : _) -> return e
        (PatternDef [] (SymbolPat _ _) e pos : _) -> do
          c' <- getEvaluationContext s
          evaluate c' e
        _ -> debug ("symbol is irreducible 2 " ++ name s) >> return (SymbolExpr s (definedType s) pos)
evaluate c e@(AppExpr e0 e1 t pos) =
  do e0e <- evaluate c e0
     e1e <- evaluate c e1
     te <- evaluate c t
     debug ("evaluate c " ++ show e ++ " where c = " ++ show c ++ "\n~~\n")
     case e0e of
      SymbolExpr s t pos ->
        case lookupSymbol c (name s) of
          Nothing -> debug ("symbol is irreducible 3 " ++ name s) >> return (AppExpr e0e e1e te pos)
          Just s ->
            case definitions s of
              [] -> return (AppExpr e0e e1e te pos)
              (ConstantDef d pos : _) -> do
                c' <- getEvaluationContext s
                evaluate c' (AppExpr d e1e te pos)
              defs -> do
                -- TODO: if pattern defs for a symbol can originate from
                -- different contexts, then those defs can have different
                -- evaluation contexts
                c' <- getEvaluationContext s
                evaluatePatternMatch c' defs (AppExpr e0e e1e te pos)
      AppExpr _ _ _ pos ->
        do s <- leadSymbol e0e
           case lookupSymbol c (name s) of
             Nothing -> debug ("symbol is irreducible 4 " ++ name s) >> return (AppExpr e0e e1e te pos)
             Just s -> do
               c' <- getEvaluationContext s
               evaluatePatternMatch c' (definitions s) (AppExpr e0e e1e te pos)
      LambdaExpr s t d lt pos ->
        do c' <- getEvaluationContext s
           ec' <- augmentContext c' (name s) Nothing
              (definedType s) Nothing [ConstantDef e1e Nothing]
           evaluate ec' d
      FunctionTypeExpr _ _ _ -> barf ErrFunctionTypeOnAppLHS
      DependentFunctionTypeExpr _ _ _ _ -> barf ErrFunctionTypeOnAppLHS
evaluate c e@(LambdaExpr s t d lt pos) =
  do debug ("evaluate c " ++ show e ++ " where c = " ++ show c ++ "\n~~\n")
     te <- evaluate c t
     lte <- evaluate c lt
     c' <- augmentContext c (name s) Nothing t (declarationSourcePos s) []
     s' <- certainly (lookupSymbol c' (name s))
     de <- evaluate c' d
     return (LambdaExpr s' te de lte pos)
evaluate c e@(FunctionTypeExpr a b pos) =
  do debug ("evaluate c " ++ show e ++ " where c = " ++ show c)
     ae <- evaluate c a
     be <- evaluate c b
     return (FunctionTypeExpr ae be pos)
evaluate c e@(DependentFunctionTypeExpr s a b pos) = do
  debug ("evaluate c " ++ show e ++ " where c = " ++ show c ++ "\n~~\n")
  ae <- evaluate c a
  c' <- augmentContext c (name s) Nothing ae (declarationSourcePos s) []
  s' <- certainly (lookupSymbol c' (name s))
  be <- evaluate c' b
  return (DependentFunctionTypeExpr s' ae be pos)

-- Creates a new context which has the given context as parent and has a symbol
-- with the given name, type, and definitions.
augmentContext :: Context -> String -> Maybe Context -> Expr ->
  Maybe SourcePos -> [Definition] -> FreeCat Context
augmentContext parentContext vName vNativeContext vType pos vDefs =
  do contextId <- popContextId
     return $ _augmentContext parentContext vName vNativeContext vType pos vDefs contextId

_augmentContext :: Context -> String -> Maybe Context -> Expr ->
  Maybe SourcePos -> [Definition] -> Integer -> Context
_augmentContext parentContext vName vNativeContext vType pos vDefs contextId =
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
          definitions = vDefs,
          nativeContext = fromMaybe newContext vNativeContext,
          evaluationContext = Just newContext
        }
    in newContext

-- Gathers the lead symbol in a normalized application expression.
leadSymbol :: Expr -> FreeCat Symbol
leadSymbol (SymbolExpr s t pos) = return s
leadSymbol (AppExpr e0 e1 t pos) = leadSymbol e0
leadSymbol (LambdaExpr _ _ _ _ _) = barf ErrExpectedLeadSymbolFoundLambda
leadSymbol (FunctionTypeExpr _ _ _) = barf ErrExpectedLeadSymbolFoundFunctionType
leadSymbol (DependentFunctionTypeExpr _ _ _ _) = barf ErrExpectedLeadSymbolFoundFunctionType

-- Checks if the given expr matches any of the given pattern match definitions.
-- Returns the result of evaluating the expr against the first matching definition
-- if one matches, and throws an error if no patterns match. Assumes the
-- subexpressions of the given expr are normalized.
evaluatePatternMatch :: Context -> [Definition] -> Expr -> FreeCat Expr
evaluatePatternMatch c [] e = debug ("no patterns matching " ++ show e) >> return e
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
unifyExprWithPattern c0 e pat =
  do unifyResult <- _unifyExprWithPattern (c0, Map.empty) e pat
     case unifyResult of
       Just (c1, matches) ->
        debug (show matches) >>
        debug (show (Map.keys (declarations c1))) >>
        --(certainly (Map.lookup "f" (declarations c)) >>= debug . definitions) >>
        return (Just c1)
       Nothing -> debug ("cannot unify " ++ show e ++ " with " ++ show pat) >> return Nothing

_unifyExprWithPattern :: (Context, Map String Expr) -> Expr -> Pattern -> FreeCat (Maybe (Context, Map String Expr))
_unifyExprWithPattern (c, matches) e (SymbolPat t _) =
  case Map.lookup (name t) matches of
    Just v ->
      -- temporarily allow anything for a duplicate pattern variable
      return (Just (c, matches))
      --if e == v -- TODO: weaken equivalence notion?
        --then return (Just (c, matches))
        --else debug "thing one" >> return Nothing
    Nothing ->
      case lookupSymbol c (name t) of
       Just s ->
        case e of
          SymbolExpr u _ _ ->
            if u == t
              then return (Just (c, matches))
              else do
                debug ("symbol mismatch " ++ show u ++ " " ++ show t)
                if name u == name t
                  then debug ("due to mismatched contexts:\n" ++ show (nativeContext u) ++ "---\n" ++ show (nativeContext t))
                  else return ()
                return Nothing
          _ -> debug "thing three" >> return Nothing
       Nothing -> do
         c' <- augmentContext c (name t) Nothing (definedType t) Nothing [ConstantDef e Nothing]
         return (Just (c', Map.insert (name t) e matches))
_unifyExprWithPattern (c0, matches0) (AppExpr e f _ _) (AppPat p q _) =
  do unifyResult1 <- _unifyExprWithPattern (c0, matches0) e p
     case unifyResult1 of
       Nothing -> return Nothing
       Just (c1, matches1) ->
        do unifyResult2 <- _unifyExprWithPattern (c1, matches1) f q
           case unifyResult2 of
             Nothing -> return Nothing
             Just (c2, matches2) -> return unifyResult2
_unifyExprWithPattern (c, matches) e p = do
  debug ("odd mismatch " ++ show (e, p, matches, c))
  return Nothing

--
-- Constructing semantic objects from raw objects while checking coherence
--

digestContext :: RawContext -> FreeCat Context
digestContext decls =
  do c <- foldM addToContext rootContext decls
     debug "complete digestion"
     completeContext c

addToContext :: Context -> Positioned RawDeclaration -> FreeCat Context
addToContext c (RawTypeDeclaration assertion, pos) = do
  debug ("digest type assertion " ++ show pos)
  digestTypeAssertion c (assertion, Just pos)
addToContext c (RawImportDeclaration _, pos) = error "import not implemented"
addToContext c (RawEquationDeclaration (RawEquation rawdecls rawpat rawdef), pos) =
 case lookupSymbol c (rawPatternLeadSymbol rawpat) of
   Nothing -> barf ErrEquationWithoutMatchingTypeDeclaration
   Just sym ->
     do cPat <- foldM digestTypeAssertion c (Prelude.map (,Nothing) rawdecls)
        debug ("digest equation " ++ show pos)
        debug ("pattern context " ++ show cPat)
        (pat, patType) <- digestPattern cPat rawpat
        (def, defType) <- digestExpr cPat rawdef
        assertTypesMatch cPat def defType cPat (patternToExpr pat) patType
        decls <- mapM (digestVarDecl cPat) rawdecls
        augmentContext c (name sym) (Just $ nativeContext sym) (definedType sym) (declarationSourcePos sym)
          (definitions sym ++ [ (PatternDef decls pat def (Just pos)) ]) -- TODO: less consing

digestTypeAssertion :: Context -> (RawTypeAssertion, Maybe SourcePos) -> FreeCat Context
digestTypeAssertion c (RawTypeAssertion s rawt, pos) =
  case lookupSymbol c s of
    Just _ -> barf ErrExtraTypeDeclaration
    Nothing ->
      do (t, tt) <- digestExpr c rawt
         assertTypesMatch c t tt rootContext t typeOfTypes
         c' <- augmentContext c s Nothing t pos []
         return c'

digestPattern :: Context -> RawPattern -> FreeCat (Pattern, Expr)
digestPattern c (RawSymbolPat s) =
  case lookupSymbol c s of
    Just sym -> return (SymbolPat sym (definedType sym), definedType sym)
    Nothing -> barf (ErrSymbolNotDefined c Nothing s)
digestPattern c (RawAppPat p q) =
  do (pd, pdType) <- digestPattern c p
     (pq, pqType) <- digestPattern c q
     appType <- case pdType of
       FunctionTypeExpr a b pos ->
        do assertTypesMatch c (patternToExpr pq) pqType c (patternToExpr pq) a
           return b
       DependentFunctionTypeExpr s a b pos ->
        do assertTypesMatch c (patternToExpr pq) pqType c (SymbolExpr s a pos) a
           c' <- augmentContext c (name s) Nothing a Nothing [ConstantDef (patternToExpr pq) Nothing]
           bEv <- evaluate c' b
           return bEv
       _ -> barf ErrAppHeadIsNotFunctionTyped
     return (AppPat pd pq appType, appType)

-- cPat is assumed to contain a declaration generated from this type
-- assertion via digestTypeAssertion
digestVarDecl :: Context -> RawTypeAssertion -> FreeCat VariableDeclaration
digestVarDecl cPat (RawTypeAssertion s _) =
  do sym <- certainly (lookupSymbol cPat s)
     return (VarDecl sym (definedType sym))

-- Assumes all symbols used in RawExpr are defined in Context.
-- Returns a pair of the digested expr and its inferred type.
digestExpr :: Context -> RawExpr -> FreeCat (Expr, Expr)
digestExpr c (RawSymbolExpr pos s) =
  case lookupSymbol c s of
    Just sym -> return (SymbolExpr sym (definedType sym) (Just pos), definedType sym)
    Nothing -> barf (ErrSymbolNotDefined c (Just pos) s)
digestExpr c (RawAppExpr pos e0 e1) =
  do (e0d, e0dType) <- digestExpr c e0
     (e1d, e1dType) <- digestExpr c e1
     appType <- case e0dType of
       FunctionTypeExpr a b pos ->
         do assertTypesMatch c e1d e1dType c e1d a
            return b
       DependentFunctionTypeExpr s a b pos ->
         do assertTypesMatch c e1d e1dType c (SymbolExpr s a pos) a
            c' <- augmentContext c (name s) Nothing a Nothing [ConstantDef e1d Nothing]
            bEv <- evaluate c' b
            return bEv
       _ -> barf ErrAppHeadIsNotFunctionTyped
     return ((AppExpr e0d e1d appType (Just pos)), appType)
digestExpr c (RawLambdaExpr pos s t d) =
  do (td, tdType) <- digestExpr c t
     assertTypesMatch c td tdType rootContext td typeOfTypes
     c' <- augmentContext c s Nothing td Nothing []
     (dd, ddType) <- digestExpr c' d
     sym <- certainly (lookupSymbol c' s)
     let lt = (DependentFunctionTypeExpr sym td ddType (Just pos)) in
       return (LambdaExpr sym td dd lt (Just pos), lt)
digestExpr c (RawFunctionTypeExpr pos a b) =
  do (ad, adType) <- digestExpr c a
     assertTypesMatch c ad adType rootContext ad typeOfTypes
     (bd, bdType) <- digestExpr c b
     assertTypesMatch c bd bdType rootContext bd typeOfTypes
     return (FunctionTypeExpr ad bd (Just pos), typeOfTypes)
digestExpr c (RawDependentFunctionTypeExpr pos s a b) =
  do (ad, adType) <- digestExpr c a
     assertTypesMatch c ad adType rootContext ad typeOfTypes
     c' <- augmentContext c s Nothing ad (Just pos) []
     sym <- certainly (lookupSymbol c' s)
     (bd, bdType) <- digestExpr c' b
     assertTypesMatch c' bd bdType rootContext bd typeOfTypes
     return (DependentFunctionTypeExpr sym ad bd (Just pos), typeOfTypes)

-- Throws an error unless the two exprs match as types. For now this
-- simply means their normal forms are syntactically equal.
assertTypesMatch :: Context -> Expr -> Expr -> Context -> Expr -> Expr -> FreeCat ()
assertTypesMatch c0 e0 t0 c1 e1 t1 =
  do t0ev <- evaluate c0 t0
     t1ev <- evaluate c1 t1
     -- TODO: use a looser equivalence notion than == (alpha-convertibility?)
     if t0ev == t1ev
       then return ()
       else barf (ErrTypeMismatch c0 e0 t0ev c1 e1 t1ev)

completeContext :: Context -> FreeCat Context
completeContext c =
  do contextId <- popContextId
     let completedContext = Context {
             contextId = contextId,
             uri = (uri c),
             parentContext = Just rootContext,
             declarations = Map.union
              (declarations rootContext)
              (Map.map (addEvaluationContextToSymbol completedContext) (declarations c)),
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
addEvaluationContextToExpr ec (SymbolExpr s t pos) =
  let t' = addEvaluationContextToExpr ec t' in
    case Map.lookup (name s) (declarations ec) of
      Just s' ->
        if nativeContext s == nativeContext s'
          then SymbolExpr s' t' pos
          else SymbolExpr s t' pos
      Nothing -> SymbolExpr s t' Nothing
addEvaluationContextToExpr ec (AppExpr f x t pos) =
  let f' = addEvaluationContextToExpr ec f
      x' = addEvaluationContextToExpr ec x
      t' = addEvaluationContextToExpr ec t
    in AppExpr f' x' t' pos
addEvaluationContextToExpr ec (LambdaExpr s t d lt pos) =
  let t' = addEvaluationContextToExpr ec t
      d' = addEvaluationContextToExpr ec d
      lt' = addEvaluationContextToExpr ec lt
    in LambdaExpr s t' d' lt' pos
addEvaluationContextToExpr ec (FunctionTypeExpr a b pos) =
  let a' = addEvaluationContextToExpr ec a
      b' = addEvaluationContextToExpr ec b
    in FunctionTypeExpr a' b' pos
addEvaluationContextToExpr ec (DependentFunctionTypeExpr s a b pos) =
  let a' = addEvaluationContextToExpr ec a
      b' = addEvaluationContextToExpr ec b
    in DependentFunctionTypeExpr s a' b' pos

addEvaluationContextToPattern :: Context -> Pattern -> Pattern
addEvaluationContextToPattern ec (SymbolPat s t) =
  case Map.lookup (name s) (declarations ec) of
    Just s' ->
      if s == s' -- iff nativeContext s == nativeContext s', since we know name s == name s'
        then -- even though s == s', s' has the evaluation context added whereas s does not
          SymbolPat s' t
        else -- s' is some other symbol not declared in ec.
          -- this is right because we're not adding an evaluation context
          -- to symbols outside the evaluation context
          SymbolPat s t
    Nothing -> SymbolPat s t
addEvaluationContextToPattern ec (AppPat f x t) =
  let f' = addEvaluationContextToPattern ec f
      x' = addEvaluationContextToPattern ec x
    in AppPat f' x' t

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
substitute s v e@(LambdaExpr s' t d lt pos) =
  if s == s'
    then e
    -- TODO: is this correct for lt?
    else LambdaExpr s' (substitute s v t) (substitute s v d) (substitute s v lt) Nothing
substitute s v (FunctionTypeExpr a b pos) =
  FunctionTypeExpr (substitute s v a) (substitute s v b) pos
substitute s v e@(DependentFunctionTypeExpr s' a b pos) =
  if s == s'
    then e
    else DependentFunctionTypeExpr s' (substitute s v a) (substitute s v b) Nothing

-- returns true if the given symbol occurs free in the given expr
occursFreeIn :: Symbol -> Expr -> Bool
s `occursFreeIn` (SymbolExpr s' _ _) = s == s'
s `occursFreeIn` (AppExpr a b _ _) = s `occursFreeIn` a || s `occursFreeIn` b
s `occursFreeIn` (LambdaExpr s' t e _ _) =
  s `occursFreeIn` t
  || (s /= s' && occursFreeIn s e)
s `occursFreeIn` (FunctionTypeExpr a b _) = s `occursFreeIn` a || s `occursFreeIn` b
s `occursFreeIn` (DependentFunctionTypeExpr s' a b _) =
  s `occursFreeIn` a
  || (s /= s' && s `occursFreeIn` b)
