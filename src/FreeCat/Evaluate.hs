{-# LANGUAGE TupleSections #-}

--
-- Evaluation
--

module FreeCat.Evaluate where

import Data.Map as Map
import FreeCat.Core

evaluate :: Context -> Expr -> FreeCat Expr
evaluate c e@(SymbolExpr s pos) = do
  case lookupSymbol c (name s) of
    Nothing -> return e
    Just s' ->
      case equations s' of
        (Equation c' [] (SymbolExpr _ _) e _ : _) -> evaluate c' e
        _ -> return (SymbolExpr s pos)
evaluate c e@(AppExpr e0 e1 pos) =
  do e0e <- evaluate c e0
     e1e <- evaluate c e1
     case e0e of
      SymbolExpr s pos ->
        case lookupSymbol c (name s) of
          Nothing -> return (AppExpr e0e e1e pos)
          Just s -> evaluatePatternMatch (equations s) (AppExpr e0e e1e pos)
      AppExpr _ _ pos ->
        do s <- leadSymbol e0e
           case lookupSymbol c (name s) of
             Nothing -> return (AppExpr e0e e1e pos)
             Just s -> evaluatePatternMatch (equations s) (AppExpr e0e e1e pos)
      LambdaExpr c' s t d pos ->
        do ec' <- augmentContext c' (name s) Nothing
              (definedType s) Nothing [constantDefinition s (definedType s) e1e]
           evaluate ec' d
      FunctionTypeExpr _ _ _ -> barf ErrFunctionTypeOnAppLHS
      DependentFunctionTypeExpr _ _ _ _ -> barf ErrFunctionTypeOnAppLHS
evaluate c0 e@(LambdaExpr c1 s t d pos) = return e
evaluate c e@(FunctionTypeExpr a b pos) =
  do ae <- evaluate c a
     be <- evaluate c b
     return (FunctionTypeExpr ae be pos)
evaluate c e@(DependentFunctionTypeExpr s a b pos) = do
  c' <- augmentContext c (name s) Nothing a Nothing []
  ae <- evaluate c' a
  be <- evaluate c' b
  return (DependentFunctionTypeExpr s ae be pos)

-- Checks if the given expr matches any of the given pattern match equations.
-- Returns the result of evaluating the expr against the first matching definition
-- if one matches, and throws an error if no patterns match. Assumes the
-- subexpressions of the given expr are normalized.
evaluatePatternMatch :: [Equation] -> Expr -> FreeCat Expr
evaluatePatternMatch [] e = return e
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
       Just (c1, matches) -> return (Just c1)
       Nothing -> return Nothing

_unifyExprWithPattern :: (Context, Map String Expr) -> Expr -> Pattern -> FreeCat (Maybe (Context, Map String Expr))
_unifyExprWithPattern (c, matches) e (SymbolExpr t _) =
  case Map.lookup (name t) matches of
    Just v ->
      -- temporarily allow anything for a duplicate pattern variable
      return (Just (c, matches))
      --if e == v -- TODO: weaken equivalence notion?
        --then return (Just (c, matches))
        --else return Nothing
    Nothing ->
      case lookupSymbol c (name t) of
       Just s ->
        case e of
          SymbolExpr u _ ->
            if u == t
              then return (Just (c, matches))
              else return Nothing
          _ -> return Nothing
       Nothing -> do
         c' <- augmentContext c (name t) Nothing (definedType t) Nothing
                [constantDefinition t (definedType t) e]
         return (Just (c', Map.insert (name t) e matches))
_unifyExprWithPattern (c0, matches0) (AppExpr e f _) (AppExpr p q _) =
  do unifyResult1 <- _unifyExprWithPattern (c0, matches0) e p
     case unifyResult1 of
       Nothing -> return Nothing
       Just (c1, matches1) ->
        do unifyResult2 <- _unifyExprWithPattern (c1, matches1) f q
           case unifyResult2 of
             Nothing -> return Nothing
             Just (c2, matches2) -> return unifyResult2
_unifyExprWithPattern (c, matches) e p = return Nothing
