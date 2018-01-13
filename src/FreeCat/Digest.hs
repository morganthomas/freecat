{-# LANGUAGE TupleSections #-}

--
-- Constructing semantic objects from raw objects while checking coherence
--

module FreeCat.Digest where

import Data.Map as Map
import Control.Monad (mapM, foldM)
import Text.Parsec (SourcePos)
import FreeCat.Core
import FreeCat.Evaluate (evaluate)

digestContext :: RawContext -> FreeCat Context
digestContext decls =
  do c <- foldM addToContext rootContext decls
     completeContext c

addToContext :: Context -> RawDeclaration -> FreeCat Context
addToContext c (RawTypeDeclaration pos assertion) =
  digestTypeAssertion False c (assertion, pos)
addToContext c (RawImportDeclaration pos _) = error "import not implemented"
addToContext c (RawEquationDeclaration pos (RawEquation rawdecls rawpat rawdef)) =
 case lookupSymbol c (rawPatternLeadSymbol rawpat) of
   Nothing -> barf ErrEquationWithoutMatchingTypeDeclaration
   Just sym ->
     do (pat, patType, cPat') <- digestPattern c rawpat
        (def, defType) <- digestExpr cPat' rawdef
        assertTypesMatch cPat' def defType cPat' pat patType
        decls <- mapM (digestVarDecl pos cPat') rawdecls
        augmentContext c (name sym) (Just $ nativeContext sym) (definedType sym) (declarationSourcePos sym)
          (equations sym ++ [ (Equation cPat' decls pat def (Just pos)) ]) -- TODO: less consing

digestTypeAssertion :: Bool -> Context -> (RawTypeAssertion, SourcePos) -> FreeCat Context
digestTypeAssertion allowDuplicates c (RawTypeAssertion s rawt, pos) =
  case lookupSymbol c s of
    Just _ ->
      if allowDuplicates
        then return c
        else barf ErrExtraTypeDeclaration
    Nothing ->
      do (t, tt) <- digestExpr c rawt
         assertTypesMatch c t tt rootContext t typeOfTypes
         c' <- augmentContext c s Nothing t (Just pos) []
         return c'

-- cPat is assumed to contain a declaration generated from this type
-- assertion via digestTypeAssertion
digestVarDecl :: SourcePos -> Context -> RawTypeAssertion -> FreeCat VariableDeclaration
digestVarDecl pos cPat assertion@(RawTypeAssertion s rawt) = do
  sym <- certainly (lookupSymbol cPat s)
  c' <- digestTypeAssertion True cPat (assertion, pos)
  sym' <- certainly (lookupSymbol c' s)
  assertTypesMatch cPat (SymbolExpr sym (Just pos)) (definedType sym) c' (SymbolExpr sym' (Just pos)) (definedType sym')
  return sym

-- Returns a triple of the digested pattern, its inferred type, and the Context
-- resulting from inferring the types of any free variables in the pattern.
digestPattern :: Context -> RawExpr -> FreeCat (Expr, Expr, Context)
digestPattern c (RawSymbolExpr pos s) =
  case lookupSymbol c s of
    Just sym -> return (SymbolExpr sym (Just pos), definedType sym, c)
    Nothing -> barf (ErrSymbolNotDefined c (Just pos) s)
digestPattern c0 (RawAppExpr pos e0 e1) = do
     (e0d, e0dType, c1) <- digestPattern c0 e0
     e1_expectedType <- domainType e0dType
     (e1d, e1dType, c2) <- digestPattern' c1 e1 e1_expectedType
     appType <- case e0dType of
       FunctionTypeExpr a b pos ->
         do assertTypesMatch c2 e1d e1dType c2 e1d a
            return b
       DependentFunctionTypeExpr s b pos ->
         do assertTypesMatch c2 e1d e1dType c2 (SymbolExpr s pos) (definedType s)
            c3 <- augmentContext c2 (name s) Nothing (definedType s) Nothing
                    [constantDefinition s e1dType e1d]
            bEv <- evaluate c3 b
            return bEv
       _ -> barf ErrAppHeadIsNotFunctionTyped
     return ((AppExpr e0d e1d (Just pos)), appType, c2)

-- Also expects to receive an expected type (et) for this pattern
digestPattern' :: Context -> RawExpr -> Expr -> FreeCat (Expr, Expr, Context)
digestPattern' c (RawSymbolExpr pos s) et =
   case lookupSymbol c s of
     Just sym -> return (SymbolExpr sym (Just pos), definedType sym, c)
     Nothing -> do
      c' <- augmentContext c s Nothing et Nothing []
      sym <- certainly (lookupSymbol c' s)
      return (SymbolExpr sym (Just pos), et, c')
digestPattern' c0 (RawAppExpr pos e0 e1) et =
   do (e0d, e0dType, c1) <- digestPattern c0 e0
      e1_expectedType <- domainType e0dType
      (e1d, e1dType, c2) <- digestPattern' c1 e1 e1_expectedType
      appType <- case e0dType of
        FunctionTypeExpr a b pos ->
          do assertTypesMatch c2 e1d e1dType c2 e1d a
             return b
        DependentFunctionTypeExpr s b pos ->
          do assertTypesMatch c2 e1d e1dType c2 (SymbolExpr s pos) (definedType s)
             c3 <- augmentContext c2 (name s) Nothing (definedType s) Nothing
                     [constantDefinition s e1dType e1d]
             bEv <- evaluate c3 b
             return bEv
        _ -> barf ErrAppHeadIsNotFunctionTyped
      return ((AppExpr e0d e1d (Just pos)), appType, c2)

-- Assumes all symbols used in RawExpr are defined in Context.
-- Returns a pair of the digested expr and its inferred type.
digestExpr :: Context -> RawExpr -> FreeCat (Expr, Expr)
digestExpr c (RawSymbolExpr pos s) =
  case lookupSymbol c s of
    Just sym -> return (SymbolExpr sym (Just pos), definedType sym)
    Nothing -> barf (ErrSymbolNotDefined c (Just pos) s)
digestExpr c (RawAppExpr pos e0 e1) =
  do (e0d, e0dType) <- digestExpr c e0
     (e1d, e1dType) <- digestExpr c e1
     appType <- case e0dType of
       FunctionTypeExpr a b pos ->
         do assertTypesMatch c e1d e1dType c e1d a
            return b
       DependentFunctionTypeExpr s b pos ->
         do assertTypesMatch c e1d e1dType c (SymbolExpr s pos) (definedType s)
            c' <- augmentContext c (name s) Nothing (definedType s) Nothing
                    [constantDefinition s e1dType e1d]
            bEv <- evaluate c' b
            return bEv
       _ -> barf ErrAppHeadIsNotFunctionTyped
     return ((AppExpr e0d e1d (Just pos)), appType)
digestExpr c (RawLambdaExpr pos s t d) =
  do (td, tdType) <- digestExpr c t
     assertTypesMatch c td tdType rootContext td typeOfTypes
     c' <- augmentContext c s Nothing td Nothing []
     (dd, ddType) <- digestExpr c' d
     sym <- certainly (lookupSymbol c' s)
     let lt = (DependentFunctionTypeExpr sym ddType (Just pos)) in
       return (LambdaExpr c' sym dd (Just pos), lt)
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
     return (DependentFunctionTypeExpr sym bd (Just pos), typeOfTypes)

-- Throws an error unless the two exprs match as types.
assertTypesMatch :: Context -> Expr -> Expr -> Context -> Expr -> Expr -> FreeCat ()
assertTypesMatch c0 e0 t0 c1 e1 t1 =
  do t0ev <- evaluate c0 t0
     t1ev <- evaluate c1 t1
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
addEvaluationContextToExpr ec (SymbolExpr s pos) =
  case Map.lookup (name s) (declarations ec) of
    Just s' ->
      if nativeContext s == nativeContext s'
        then SymbolExpr s' pos
        else SymbolExpr s pos
    Nothing -> SymbolExpr s pos
addEvaluationContextToExpr ec (AppExpr f x pos) =
  let f' = addEvaluationContextToExpr ec f
      x' = addEvaluationContextToExpr ec x
    in AppExpr f' x' pos
addEvaluationContextToExpr ec (LambdaExpr c s d pos) =
  let s' = s { definedType = addEvaluationContextToExpr ec (definedType s) }
      d' = addEvaluationContextToExpr ec d
    in LambdaExpr ec s' d' pos
addEvaluationContextToExpr ec (FunctionTypeExpr a b pos) =
  let a' = addEvaluationContextToExpr ec a
      b' = addEvaluationContextToExpr ec b
    in FunctionTypeExpr a' b' pos
addEvaluationContextToExpr ec (DependentFunctionTypeExpr s b pos) =
  let a' = addEvaluationContextToExpr ec (definedType s)
      s' = s { definedType = a' }
      b' = addEvaluationContextToExpr ec b
    in DependentFunctionTypeExpr s' b' pos

addEvaluationContextToPattern :: Context -> Pattern -> Pattern
addEvaluationContextToPattern ec (SymbolExpr s pos) =
  case Map.lookup (name s) (declarations ec) of
    Just s' ->
      if s == s' -- iff nativeContext s == nativeContext s', since we know name s == name s'
        then -- even though s == s', s' has the evaluation context added whereas s does not
          SymbolExpr s' pos
        else -- s' is some other symbol not declared in ec.
          -- this is right because we're not adding an evaluation context
          -- to symbols outside the evaluation context
          SymbolExpr s pos
    Nothing -> SymbolExpr s pos
addEvaluationContextToPattern ec (AppExpr f x pos) =
  let f' = addEvaluationContextToPattern ec f
      x' = addEvaluationContextToPattern ec x
    in AppExpr f' x' pos

addEvaluationContextToVariableDeclaration :: Context -> VariableDeclaration -> VariableDeclaration
addEvaluationContextToVariableDeclaration ec s =
  let t' = addEvaluationContextToExpr ec (definedType s)
    in s { definedType = t' }

addEvaluationContextToEquation :: Context -> Equation -> Equation
addEvaluationContextToEquation ec (Equation c decls pat e pos) =
  let decls' = Prelude.map (addEvaluationContextToVariableDeclaration ec) decls
      pat' = addEvaluationContextToPattern ec pat
      e' = addEvaluationContextToExpr ec e
    in (Equation ec decls' pat' e' pos)
