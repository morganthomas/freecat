{-# LANGUAGE TupleSections #-}

--
-- Evaluation
--

module FreeCat.Evaluate where

import Data.Map as Map
import Data.Maybe (fromMaybe)
import Control.Monad (mapM, foldM)
import Control.Monad.Trans.Class
import Control.Monad.Trans.State
import Control.Monad.Trans.Except as E
import Control.Monad.IO.Class
import Text.Parsec (SourcePos)

import FreeCat.Core

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
     return e
evaluate c e@(FunctionTypeExpr a b pos) =
  do debug ("evaluate c " ++ show e ++ " where c = " ++ show c)
     ae <- evaluate c a
     be <- evaluate c b
     return (FunctionTypeExpr ae be pos)
evaluate c e@(DependentFunctionTypeExpr s a b pos) = do
  debug ("evaluate c " ++ show e ++ " where c = " ++ show c ++ "\n~~\n")
  return e

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
