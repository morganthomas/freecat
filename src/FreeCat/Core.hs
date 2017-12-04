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
  show c = Prelude.foldl (++) "" (Map.map showSymbolEquations (declarations c))

showSymbolEquations :: Symbol -> String
showSymbolEquations s = name s ++ " : " ++ show (definedType s) ++ "\n"
  ++ (Prelude.foldl (++) "" $ Prelude.map (\d -> show d ++ "\n") (equations s))

data Symbol = Symbol {
  name :: String,
  definedType :: Expr,
  declarationSourcePos :: Maybe SourcePos,
  -- all pattern equations have this symbol as their lead symbol
  equations :: [Equation],
  -- the context in which the symbol was originally defined
  nativeContext :: Context
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

data Equation = -- the Context is the evaluation context
  Equation Context [VariableDeclaration] Pattern Expr (Maybe SourcePos)

constantDefinition :: Symbol -> Expr -> Equation
constantDefinition s e = Equation rootContext [] (SymbolExpr s (typeOf e) Nothing) e Nothing

instance Show Equation where
  show (Equation c decls pat e pos) =
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

type Pattern = Expr

data Expr =
 -- last argument of type Expr is the expression's type
   SymbolExpr Symbol Expr (Maybe SourcePos)
 | AppExpr Expr Expr Expr (Maybe SourcePos)
 -- Context is the context inside the lambda before the variable has a value
 | LambdaExpr Context Symbol Expr Expr Expr (Maybe SourcePos)
 -- type is necessarily Type, so expression's type isn't included
 | FunctionTypeExpr Expr Expr (Maybe SourcePos)
 | DependentFunctionTypeExpr Symbol Expr Expr (Maybe SourcePos)

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

typeOf :: Expr -> Expr
typeOf (SymbolExpr s t pos) = t
typeOf (AppExpr a b t pos) = t
typeOf (LambdaExpr c s a e t pos) = t
typeOf (FunctionTypeExpr _ _ _) = typeOfTypes
typeOf (DependentFunctionTypeExpr _ _ _ _) = typeOfTypes

instance Show Expr where
  show (SymbolExpr s t pos) = name s
  show (AppExpr f g t pos) = "(" ++ show f ++ " " ++ show g ++ ")"
  show (LambdaExpr c s t e lt pos) = "(\\" ++ name s ++ " : " ++ show t ++ " => " ++ show e ++ ")"
  show (FunctionTypeExpr a b pos) = "(" ++ show a ++ " -> " ++ show b ++ ")"
  show (DependentFunctionTypeExpr s a b pos) = "((" ++ name s ++ " : " ++ show a ++ ") -> " ++ show b ++ ")"

lookupSymbol :: Context -> String -> Maybe Symbol
lookupSymbol c s =
  case Map.lookup s (declarations c) of
    Just sym -> Just sym
    Nothing -> Map.lookup s (importedSymbols c)

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

--
-- Evaluation
--

evaluate :: Context -> Expr -> FreeCat Expr
evaluate c e@(SymbolExpr s t pos) = do
  debug ("evaluate c " ++ (name s) ++ " where c = " ++ show c ++ "\n~~\n")
  case lookupSymbol c (name s) of
    Nothing -> debug ("symbol is irreducible 1 " ++ name s) >> return e
    Just s' ->
      case equations s' of
        (Equation c' [] (SymbolExpr _ _ _) e _ : _) -> evaluate c' e
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
          Just s -> evaluatePatternMatch (equations s) (AppExpr e0e e1e te pos)
      AppExpr _ _ _ pos ->
        do s <- leadSymbol e0e
           case lookupSymbol c (name s) of
             Nothing -> debug ("symbol is irreducible 4 " ++ name s) >> return (AppExpr e0e e1e te pos)
             Just s -> evaluatePatternMatch (equations s) (AppExpr e0e e1e te pos)
      LambdaExpr c' s t d lt pos ->
        do ec' <- augmentContext c' (name s) Nothing
              (definedType s) Nothing [constantDefinition s e1e]
           evaluate ec' d
      FunctionTypeExpr _ _ _ -> barf ErrFunctionTypeOnAppLHS
      DependentFunctionTypeExpr _ _ _ _ -> barf ErrFunctionTypeOnAppLHS
evaluate c0 e@(LambdaExpr c1 s t d lt pos) =
  do debug ("evaluate c " ++ show e ++ " where c = " ++ show c0 ++ "\n~~\n")
     te <- evaluate c0 t
     lte <- evaluate c0 lt
     c2 <- augmentContext c0 (name s) Nothing t (declarationSourcePos s) []
     s' <- certainly (lookupSymbol c2 (name s))
     de <- evaluate c2 d
     return (LambdaExpr c2 s' te de lte pos)
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

-- Gathers the lead symbol in a normalized application expression.
leadSymbol :: Expr -> FreeCat Symbol
leadSymbol (SymbolExpr s t pos) = return s
leadSymbol (AppExpr e0 e1 t pos) = leadSymbol e0
leadSymbol (LambdaExpr _ _ _ _ _ _) = barf ErrExpectedLeadSymbolFoundLambda
leadSymbol (FunctionTypeExpr _ _ _) = barf ErrExpectedLeadSymbolFoundFunctionType
leadSymbol (DependentFunctionTypeExpr _ _ _ _) = barf ErrExpectedLeadSymbolFoundFunctionType

-- Checks if the given expr matches any of the given pattern match equations.
-- Returns the result of evaluating the expr against the first matching definition
-- if one matches, and throws an error if no patterns match. Assumes the
-- subexpressions of the given expr are normalized.
evaluatePatternMatch :: [Equation] -> Expr -> FreeCat Expr
evaluatePatternMatch [] e = debug ("no patterns matching " ++ show e) >> return e
evaluatePatternMatch ((Equation c0 _ p d pos):defs) e =
  do unifyResult <- unifyExprWithPattern c0 e p
     case unifyResult of
      Just c1 -> evaluate c1 d
      Nothing -> evaluatePatternMatch defs e

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
        --(certainly (Map.lookup "f" (declarations c)) >>= debug . equations) >>
        return (Just c1)
       Nothing -> debug ("cannot unify " ++ show e ++ " with " ++ show pat) >> return Nothing

_unifyExprWithPattern :: (Context, Map String Expr) -> Expr -> Pattern -> FreeCat (Maybe (Context, Map String Expr))
_unifyExprWithPattern (c, matches) e (SymbolExpr t _ _) =
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
         c' <- augmentContext c (name t) Nothing (definedType t) Nothing
                [constantDefinition t e]
         return (Just (c', Map.insert (name t) e matches))
_unifyExprWithPattern (c0, matches0) (AppExpr e f _ _) (AppExpr p q _ _) =
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
        (pat, patType) <- digestExpr cPat rawpat
        (def, defType) <- digestExpr cPat rawdef
        assertTypesMatch cPat def defType cPat pat patType
        decls <- mapM (digestVarDecl cPat) rawdecls
        augmentContext c (name sym) (Just $ nativeContext sym) (definedType sym) (declarationSourcePos sym)
          (equations sym ++ [ (Equation cPat decls pat def (Just pos)) ]) -- TODO: less consing

digestTypeAssertion :: Context -> (RawTypeAssertion, Maybe SourcePos) -> FreeCat Context
digestTypeAssertion c (RawTypeAssertion s rawt, pos) =
  case lookupSymbol c s of
    Just _ -> barf ErrExtraTypeDeclaration
    Nothing ->
      do (t, tt) <- digestExpr c rawt
         assertTypesMatch c t tt rootContext t typeOfTypes
         c' <- augmentContext c s Nothing t pos []
         return c'

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
            c' <- augmentContext c (name s) Nothing a Nothing
                    [constantDefinition s e1d]
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
       return (LambdaExpr c' sym td dd lt (Just pos), lt)
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
    equations = Prelude.map (addEvaluationContextToEquation ec) (equations s),
    nativeContext = nativeContext s
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
addEvaluationContextToExpr ec (LambdaExpr c s t d lt pos) =
  let t' = addEvaluationContextToExpr ec t
      d' = addEvaluationContextToExpr ec d
      lt' = addEvaluationContextToExpr ec lt
    in LambdaExpr ec s t' d' lt' pos
addEvaluationContextToExpr ec (FunctionTypeExpr a b pos) =
  let a' = addEvaluationContextToExpr ec a
      b' = addEvaluationContextToExpr ec b
    in FunctionTypeExpr a' b' pos
addEvaluationContextToExpr ec (DependentFunctionTypeExpr s a b pos) =
  let a' = addEvaluationContextToExpr ec a
      b' = addEvaluationContextToExpr ec b
    in DependentFunctionTypeExpr s a' b' pos

addEvaluationContextToPattern :: Context -> Pattern -> Pattern
addEvaluationContextToPattern ec (SymbolExpr s t pos) =
  case Map.lookup (name s) (declarations ec) of
    Just s' ->
      if s == s' -- iff nativeContext s == nativeContext s', since we know name s == name s'
        then -- even though s == s', s' has the evaluation context added whereas s does not
          SymbolExpr s' t pos
        else -- s' is some other symbol not declared in ec.
          -- this is right because we're not adding an evaluation context
          -- to symbols outside the evaluation context
          SymbolExpr s t pos
    Nothing -> SymbolExpr s t pos
addEvaluationContextToPattern ec (AppExpr f x t pos) =
  let f' = addEvaluationContextToPattern ec f
      x' = addEvaluationContextToPattern ec x
    in AppExpr f' x' t pos

addEvaluationContextToVariableDeclaration :: Context -> VariableDeclaration -> VariableDeclaration
addEvaluationContextToVariableDeclaration ec (VarDecl s t) =
  let t' = addEvaluationContextToExpr ec t
    in VarDecl s t'

addEvaluationContextToEquation :: Context -> Equation -> Equation
addEvaluationContextToEquation ec (Equation c decls pat e pos) =
  let decls' = Prelude.map (addEvaluationContextToVariableDeclaration ec) decls
      pat' = addEvaluationContextToPattern ec pat
      e' = addEvaluationContextToExpr ec e
    in (Equation ec decls' pat' e' pos)

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
  if s == s'
    then e
    -- TODO: is this correct for lt?
    else LambdaExpr c s' (substitute s v t) (substitute s v d) (substitute s v lt) Nothing
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
s `occursFreeIn` (LambdaExpr c s' t e _ _) =
  s `occursFreeIn` t
  || (s /= s' && occursFreeIn s e)
s `occursFreeIn` (FunctionTypeExpr a b _) = s `occursFreeIn` a || s `occursFreeIn` b
s `occursFreeIn` (DependentFunctionTypeExpr s' a b _) =
  s `occursFreeIn` a
  || (s /= s' && s `occursFreeIn` b)
