{-# LANGUAGE TupleSections #-}

--
-- Constructing semantic objects from raw objects while checking coherence
--

module FreeCat.Digest where

import Data.Map as Map
import Data.Maybe (fromMaybe)
import Control.Monad (mapM, foldM)
import Control.Monad.Trans.Class
import Control.Monad.Trans.State
import Control.Monad.Trans.Except as E
import Control.Monad.IO.Class
import Text.Parsec (SourcePos)

import FreeCat.Core
import FreeCat.Evaluate (evaluate)

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
       else debug ("Type mismatch! " ++ show (ErrTypeMismatch c0 e0 t0ev c1 e1 t1ev))

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
      Nothing -> SymbolExpr s t' pos
addEvaluationContextToExpr ec (AppExpr f x t pos) =
  let f' = addEvaluationContextToExpr ec f
      x' = addEvaluationContextToExpr ec x
      t' = addEvaluationContextToExpr ec t
    in AppExpr f' x' t' pos
addEvaluationContextToExpr ec (LambdaExpr c s t d lt pos) =
  let t' = addEvaluationContextToExpr ec t
      d' = addEvaluationContextToExpr ec d
      lt' = addEvaluationContextToExpr ec lt
      -- TODO: pretty sure this context never gets used in eval. What do?
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
