{-
Copyright 2015 Tristan Aubrey-Jones 
Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License. 
-}

{-|
Copyright   : (c) Tristan Aubrey-Jones, 2015
License     : Apache-2
Maintainer  : developer@flocc.net
Stability   : experimental

For more information please see <http://www.flocc.net/>
-}
{-# LANGUAGE TypeFamilies #-}

module Compiler.Types.DepTypeAssignment (assignDepTypes, assignFunDepTypes, showExprWithDepTypes) where

{-import Common (delimList, maybeError)
import Indices (Idx, IdxSet)
import ModelSolver (Model(..))
import RuleSets (RuleSet)
import ExprTree (Expr(Let, Lit, Tup, Rel, If, App, Fun), renewIdAndExprIds, StructEq(..))
import qualified ExprTree (Expr(Var))
import Variables (VarSubsts, VarsIn(..), emptyVarSubsts, composeVarSubsts)
import qualified Variables (fromList)
import TypeAssignment (TyToken, TyTerm, TyConstr, TyScheme, TySchemeEx, TyEnv, 
  typeOfVal, rel, relNonOrd, showExprWithTypes)
import TermLanguage (Term(..), Constr(..), Subst(..), MonadicUnifierExtension, 
  Scheme(..), SchemeEx(..), getIdsInIdTree,
  FunctionToken, Subst, monadicUnifyTrans, emptyTermEnv, applyVarSubstsToConstr,
  bindTermInState, instantiateScheme, generalizeTerm, bindNewTermVarInState,
  instantiateSchemeEx, instantiateSchemeEx2, schemeEnvToSchemeExEnv)
import TermBuilder (buildForIdxTree, fun, tup)
import TidyCode (tidyCode)

import Data.Map (Map, toList, (!), (\\), keysSet, keys, elems)
import qualified Data.Map (map, union, insert, empty, fromList, lookup, member, delete)
import Data.Set (Set, unions, intersection)
import qualified Data.Set (map, null)

import Control.Monad.Identity
import Control.Monad.State ( runStateT, evalStateT, StateT, modify, get, lift )

-}


import Compiler.Front.Common (delimList, maybeError, eids, dtvids)
import Compiler.Front.Indices (Idx, IdxSet, IdxMonad, newidST)
import Compiler.Front.ExprTree (Expr(Let, Lit, Tup, Rel, If, App, Fun), renewIdAndExprIds, StructEq(..), showExprTree)
import qualified Compiler.Front.ExprTree as ExprTree (Expr(Var))

import Compiler.Types.TermLanguage (Term(..), Constr(..), Subst(..), MonadicUnifierExtension, 
  Scheme(..), SchemeEx(..), getIdsInIdTree, IdTree(..), forAllSubs, subInTerm,
  FunctionToken(..), Subst, monadicUnifyTrans, emptyTermEnv, applyVarSubstsToConstr,
  bindTermInState, instantiateScheme, generalizeTerm, bindNewTermVarInState,
  instantiateSchemeEx, instantiateSchemeEx2, schemeEnvToSchemeExEnv, lookupTermMaybe,
  unifyConstraints)
import Compiler.Types.TermBuilder (buildForIdxTree, fun, tup)
import Compiler.Types.TypeAssignment (TyToken(..), TyTerm, TyConstr, TyScheme, TySchemeEx, TyEnv, 
  typeOfVal, rel, relNonOrd, showExprWithTypes)
import Compiler.Types.Variables (VarSubsts, VarsIn(..), emptyVarSubsts, composeVarSubsts)
import qualified Compiler.Types.Variables as Variables (fromList)
import Compiler.Types.EmbeddedFunctions

import Control.Monad.Identity (Identity, runIdentity)
import Control.Monad.State.Strict (StateT, runStateT, evalStateT, lift, get, modify)
import qualified Data.IntMap.Strict as IM
import qualified Data.Map.Strict as M
import Data.Set (Set, unions, intersection, null)
import Data.IntMap.Strict ((\\))
import Debug.Trace (trace)

-- |trace is used to display or hide debugging
-- |info depending on its implementation
trace' :: String -> a -> a
--trace' s = trace s
trace' s a = a 

type ExpMap a = IM.IntMap a
type VarMap v = IM.IntMap v

-- |expMapFromList takes an associative array and returns
-- |the ExpMap equivalent.
expMapFromList :: [(Idx,v)] -> VarMap v
expMapFromList l = IM.fromList l

-- |varMapLookup returns the value stored under the key given
-- |in the VarMap provided.
varMapLookup :: VarMap a -> Idx -> Maybe a
varMapLookup mp idx = IM.lookup idx mp

-- |varMapFromList takes an associative array and returns
-- |the VarMap equivalent.
varMapFromList :: [(Idx,v)] -> VarMap v
varMapFromList l = IM.fromList l

-- |composeVarMaps creates the left biased union of 
-- |VarMaps a and b.
composeVarMaps :: VarMap a -> VarMap a -> VarMap a
composeVarMaps a b = a `IM.union` b

-- |applyVarSubstsToVarMap subs varMap applies all the substitutions in
-- |subs to the map varMap.
applyVarSubstsToVarMap :: VarsIn a => VarSubsts a -> VarMap a -> VarMap a
applyVarSubstsToVarMap subs m = IM.map (applyVarSubsts subs) m

-- |applyVarSubstsToScheme takes a map of substitutions and a type scheme
-- |and returns the scheme with the substitutions applied to free variables.
applyVarSubstsToScheme :: VarSubsts TyTerm -> TyScheme -> TyScheme
applyVarSubstsToScheme subs (Scheme l t) = Scheme l $ applyVarSubsts (subs \\ (IM.fromList $ zip l [0..])) t

-- |applyVarSubstsToScheme map applies all substitutions to free variables in the 
-- |scheme map.
applyVarSubstsToSchemeMap :: VarSubsts TyTerm -> VarMap TyScheme -> VarMap TyScheme
applyVarSubstsToSchemeMap subs env = IM.map (applyVarSubstsToScheme subs) env

-- |applyVarSubstsToSchemeExMap map applies all substitutions to free variables in the 
-- |scheme map.
applyVarSubstsToSchemeExMap :: VarSubsts TyTerm -> VarMap TySchemeEx -> VarMap TySchemeEx
applyVarSubstsToSchemeExMap subs env = IM.map (\(SchemeEx it scheme) -> 
    SchemeEx it (applyVarSubstsToScheme (subs \\ (IM.fromList $ zip (getIdsInIdTree it) [0..])) scheme)) 
  env

-- |applySubstsToScheme takes a list of substitutions and a type scheme
-- |and returns the scheme with the substitutions applied to free variables.
applyTermSubsts :: [(TyTerm, TyTerm)] -> TyTerm -> TyTerm
applyTermSubsts ((a,b):r) term = applyTermSubsts r (applyTermSubst a b term)
applyTermSubsts [] term = term

applyTermSubst :: TyTerm -> TyTerm -> TyTerm -> TyTerm
applyTermSubst a b c = case c of
  _ | a == c -> b 
  Term t l -> Term t $ map (applyTermSubst a b) l
  other -> other

-- |Pretty print type scheme
showDepTyScheme :: TyScheme -> String
showDepTyScheme (Scheme [] term) = showEmbeddedFuns term
showDepTyScheme (Scheme vars term) = "forall " ++ 
  (delimList "," $ map (\i -> ("v" ++ show i)) vars) ++
  " => " ++ (showEmbeddedFuns  term)

showDepExprTy :: TyEnv -> Idx -> String
showDepExprTy env idx = case lookupTermMaybe env idx of
  Just v  -> " :: " ++ (showDepTyScheme v)
  Nothing -> " :: ERROR: no type term exists in env with idx " ++ (show idx) 

showExprWithDepTypes :: TyEnv -> Expr -> String
showExprWithDepTypes env exp = showExprTree env showDepExprTy 2 exp

-- |lookupVar takes two var maps and an id and tries to 
-- |lookup the value in the first map, or failing that in
-- |the second map.
lookupVar :: VarMap a -> VarMap a -> Idx -> Maybe a
lookupVar globals locals id = case varMapLookup locals id of
  Just v  -> Just v
  Nothing -> case varMapLookup globals id of
    Just v  -> Just v
    Nothing -> Nothing

-- |getIdExprPairs zips together an IdTree and a tuple expression tree
-- |returning a lift of pairs of id tree ids to expressions.
getIdExprPairs :: (IdTree, Expr) -> [(Idx, Expr)]
getIdExprPairs ab = case ab of
  ((IdTup al),(Tup _ bl)) | length al == length bl -> concat $ map getIdExprPairs $ zip al bl
  ((IdLeaf ai),expr) -> [(ai, expr)]
  ((IdBlank),_) -> []
  other -> error $ "DepTyAss:getIdExprPairs: IdTree and Expr tuple tree are not isomorphic: " ++ (show ab)

-- |Instantiates a term SchemeEx by replacing every qualified term variable
-- |with a new variable, and every function application qualified variable 
-- |with a ref to that var id (or expression id).
instantiateSchemeEx3 :: Monad m => TySchemeEx -> Expr -> IdxMonad m TyTerm
instantiateSchemeEx3 (SchemeEx it inner) expr = do
  term <- instantiateScheme inner
  let varPairs = getIdExprPairs (it, expr)
  varSubs <- mapM (\(from,to) -> embedFun [] to >>= (\t -> return $ trace ("Embed: " ++ (show to) ++ " => \n" ++ (show t) ++ "\n") $ (Var from) :|-> t)) varPairs 
  let term' = forAllSubs subInTerm varSubs term
  return term'

-- |For a given expression sets up the type environment, constraints,
-- |and expandable expression map.
buildConstrs :: Monad m => 
  VarMap TySchemeEx -> -- global var types
  VarMap TySchemeEx -> -- local var types
  Expr -> 
  StateT TyEnv (IdxMonad m) ([TyConstr], TyTerm)
buildConstrs globalEnv localEnv exp = case exp of
  -- standard constraint building
  (Lit i vl) -> do
    let ty = typeOfVal vl
    bindTermInState (Scheme [] ty) i
    return ([], ty)
  -- look for var binding in local var env
  (ExprTree.Var i vi s) -> case lookupVar globalEnv localEnv vi of
    (Just scheme) -> do
      term <- lift $ instantiateSchemeEx2 scheme
      bindTermInState (Scheme [] term) i
      return ([], term)
    (Nothing) -> error $ "Unbound var " ++ (show vi) ++ " " ++ s
                      ++ " when building dep type constraints."
  (Tup i l) -> do -- new tup term
    l' <- mapM (buildConstrs globalEnv localEnv) l
    let (cl,tl) = unzip l'
    let term = tup tl
    bindTermInState (Scheme [] term) i
    return (concat cl, term)
  (Rel i l) -> case l of
    -- empty list: just a term var
    [] -> do
      v <- bindNewTermVarInState i
      return ([], v)
    -- non empty list: all children same type
    _  -> do
      l' <- mapM (\e -> buildConstrs globalEnv localEnv e) l
      let (cl,tl) = unzip l'
      let (headTy:tail) = tl
      let cl' = map (\ty -> headTy :=: ty) tail
      let ty = rel headTy (relNonOrd)
      bindTermInState (Scheme [] ty) i -- TODO: change so not just non ord
      return (cl' ++ (concat cl), ty)
  (If i pe te ee) -> do
    v <- bindNewTermVarInState i
    (c1,t1) <- buildConstrs globalEnv localEnv pe
    (c2,t2) <- buildConstrs globalEnv localEnv te
    (c3,t3) <- buildConstrs globalEnv localEnv ee
    return ((v :=: t2):(v :=: t3):(c1 ++ c2 ++ c3), v)
  (Let i it be ie) -> do
    (c1,t1)          <- buildConstrs globalEnv localEnv be
    (newVarEnv, t1') <- buildForIdxTree it
    let newVarEnv' = varMapFromList $ schemeEnvToSchemeExEnv newVarEnv
    (c2, t2)  <- buildConstrs globalEnv (newVarEnv' `composeVarMaps` localEnv) ie
    bindTermInState (Scheme [] t2) i
    return ((t1 :=: t1'):(c1 ++ c2), t2)
  -- check if application of function with pi type
  (App i fe ae) -> do
    v <- bindNewTermVarInState i
    (c2,t2) <- buildConstrs globalEnv localEnv ae
    case fe of
      -- if application of function var (check if has a dep type)
      (ExprTree.Var fi vi s) -> do
        -- instantiate dependent type scheme using
        -- func app argument expression
        case lookupVar globalEnv localEnv vi of
          (Just schemeEx) -> do 
            t1 <- lift $ instantiateSchemeEx3 schemeEx ae
            bindTermInState (Scheme [] t1) fi
            let constr = (t1 :=: fun t2 v)
            return $ trace ("AppConstr: " ++ s ++ ": " ++ (show constr) ++ "\n") $ (constr:c2, v)
          (Nothing) -> error $ "Unbound function var " ++ (show vi) ++ " " ++ s
                    ++ " when building dep type constraints." 
      -- otherwise treat like any other function typed valueassignDepTypes
      _                      -> do 
        (c1,t1) <- buildConstrs globalEnv localEnv fe
        return ((t1 :=: fun t2 v):(c1 ++ c2), v)
  -- dive another level down
  (Fun i it e) -> do
    (newVarEnv, t1) <- buildForIdxTree it
    let newVarEnv' = varMapFromList $ schemeEnvToSchemeExEnv newVarEnv
    (cl, t2) <- buildConstrs globalEnv (newVarEnv' `composeVarMaps` localEnv) e
    let term = (fun t1 t2)
    bindTermInState (Scheme [] term) i
    return (cl, term)

-- |Extends the unification function to postpone constraints that contain
-- |Ref's (unexpanded functions) until later.
{-postponeRefsUniferEx ::
  MonadicUnifierExtension (FunctionToken TyToken) (StateT [TyConstr] Identity)
postponeRefsUniferEx env con = case con of
  --(Ref i :=: t) -> modify (\l -> con:l)           >> return (Left  [])
  --(t :=: Ref i) -> modify (\l -> (Ref i :=: t):l) >> return (Left  [])
  _             -> return $ Right con-}

-- if the constraint still contains one of these, it cannot be expanded yet
-- because it lacks a concrete function/or dim tuple to deal with. so we
-- should delay this until it is chosen. this may be later in unification, or
-- when filling gaps.
{-termsToDelay = ["FPair", "FSeq", "GFst", "GSnd", "GRem", "DFst", "DSnd"]

isTermToDelay :: TyTerm -> Bool
isTermToDelay (Term (Tok (Ty n)) _) = elem n termsToDelay
isTermToDelay _ = False-}

-- TODO Problem: now that some constraints can't be expanded until
--   others have been, we must keep retrying delayed constraints, until
--   none of them can be expanded, at which point we must fill gaps, and
--   then try and unify again.
-- NEED:
-- a new unify that jumps over bad constraints, trying others until
-- it is left with a set where none of them can be unified.

-- |Extends the unification function to simplify any embedded functions 
-- |before trying to unify.
simplifyFunsUniferEx :: Monad m => MonadicUnifierExtension (FunctionToken TyToken) (StateT [(TyTerm, TyTerm)] (IdxMonad m))
simplifyFunsUniferEx env con@(a :=: b) = {-return $ Right con-} do
  -- try and simplify terms
  (a', cl1, subs1) <- lift $ applyDimGens a -- (simplifies funs and applies dim generators)s
  (b', cl2, subs2) <- lift $ applyDimGens b
  -- if made changes then add to changes 
  modify (++subs1++subs2)
  -- if changed constr, return it, otherwise fail
  if (a /= a') || (b /= b') 
    then return $ Left $ [a' :=: b'] ++ cl1 ++ cl2
    else return $ Right con

-- |Unify all constraints ignoring those with a Ref on one side
-- |and returning them at the end if the unification succeeds
{-unifyAllButRefs :: Monad m => [TyConstr] -> 
  IdxMonad m (Either (VarSubsts TyTerm, [TyConstr]) TyConstr)
unifyAllButRefs cl = do
  either <- evalStateT (evalStateT (monadicUnifyTrans cl) simplifyFunsUniferEx) emptyTermEnv
  case either of
    (Left sl)   -> do
      let subs = Variables.fromList $ map (\(Var i :|-> e) -> (i,e)) sl
      return $ Left (subs, map (applyVarSubstsToConstr subs) refCl)
    (Right con) -> return $ Right con-}

-- |Unify all constraints ignoring those with a Ref on one side
-- |and returning them at the end if the unification succeeds
unify :: Monad m => [TyConstr] -> 
  (IdxMonad m) (Either ([(TyTerm, TyTerm)], VarSubsts TyTerm) TyConstr)
unify cl = do
  (either, subs1) <- runStateT (evalStateT (evalStateT (monadicUnifyTrans cl) simplifyFunsUniferEx) emptyTermEnv) []
  case either of
    (Left sl)   -> do
      let subs2 = Variables.fromList $ map (\(Var i :|-> e) -> (i,e)) sl
      return $ Left (subs1, subs2)
    (Right con) -> return $ Right con

-- |Check that the constraints are all disjoint (no circular variables)
checkConstraints :: [TyConstr] -> [TyConstr]
checkConstraints l = l'
  where l' = map (\(a :=: b) -> if (not $ Data.Set.null $ (getVars a) `intersection` (getVars b))
                   then error $ "Types:DepTypeAssignment:circlular constraint: " ++ (show (a :=: b)) ++ "\n of \n" ++ (show l)
                   else (a :=: b) ) l

-- |DANGER! If applyDimGensInEnv can keep on producing new constraints
-- |then this will never terminate!
solveDepConstrs :: Monad m => TyEnv -> [TyConstr] -> IdxMonad m TyEnv
solveDepConstrs tyEnv cl = do
  -- check constaints are disjoint (no circular vars)
  let cl1 = checkConstraints cl
  -- try and unify them (ignoring refs)
  res <- unify cl1
  case res of
    Left (subs1, subs2) -> do
      -- apply extra subs made due to simplification to type env
      let tyEnv1 = map (\(i, Scheme l t) -> (i, Scheme l $ applyTermSubsts subs1 t)) tyEnv
      -- apply substituions to type env
      let tyEnv2 = map (\(i,s) -> (i, applyVarSubstsToScheme subs2 s)) tyEnv1
      -- simplify any remaining unsimplified embedded func and dim generators in tyEnv
      (tyEnv3, cl2, simpSubs) <- applyDimGensInEnv tyEnv2 
      let tyEnv4 = map (\(i, Scheme l t) -> (i, Scheme l $ applyTermSubsts simpSubs t)) tyEnv3
      iw <- newidST dtvids
      case cl2 of 
        -- if no more constraints produced, return env
        [] -> return $ trace ("\nno extra constrs\n" ++ (show iw)) $ tyEnv4
        -- if more constraints, solve them too
        cl3 -> trace ("\nrecur solveDepConstrs:\n" ++ (show cl3) ++ "\n" ++ (show iw)) $ solveDepConstrs tyEnv4 cl3
    Right c@(a :=: b) -> error $ "Dependent type assignment failed on constraint:\n" ++ (show c) ++ "\n of \n" ++ (show cl) ++ "\n with \n" ++ (show tyEnv) 

assignDepTypes :: Monad m => VarMap TySchemeEx -> Expr -> IdxMonad m TyEnv
assignDepTypes varEnv expr = do
  -- create constraints
  ((cl,_),tyEnv) <- runStateT (buildConstrs varEnv IM.empty expr) emptyTermEnv
  -- solve constrs
  tyEnv' <- solveDepConstrs tyEnv cl
  return tyEnv'

-- |assignFunDepTypes varEnv domTy expr. Returns the types of the expressions in expr
-- |where expr is a function type, and domTy is the type of the function's domain.
assignFunDepTypes :: Monad m => VarMap TySchemeEx -> TyTerm -> Expr -> IdxMonad m TyEnv
assignFunDepTypes varEnv domTy expr = case expr of
  (Fun eid idxTree bodyExp) -> do
    -- create constraints
    ((cl,funTy1),tyEnv) <- runStateT (buildConstrs varEnv IM.empty expr) emptyTermEnv
    -- create constraint between funType and domainType
    ranTyVid <- newidST dtvids
    let cl' = (funTy1 :=: fun domTy (Var ranTyVid)):cl
    -- solve consts
    tyEnv' <- solveDepConstrs tyEnv $ trace ("assignFunDepTypes: " ++ (show $ head cl') ++ "\n") $cl'
    return tyEnv'
  other -> error $ "DepTypeAssignment:assignFunDepTypes: Requires a fun expr: " ++ (show expr) 

