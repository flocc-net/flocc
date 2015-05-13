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

module Compiler.Types2.DepTypeAssignment (assignDepTypes, assignDepTypes2, assignDepTypes3, assignFunDepTypes, showExprWithDepTypes, applyVarSubstsToVarMap, unify,
  solveDepConstrs2, solveDepConstrs3) where

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


import Compiler.Front.Common (delimList, maybeError, eids, dtvids, ShowP(..), hasCycle, isLeft)
import Compiler.Front.Indices (Idx, IdxSet, IdxMonad, newidST)
import Compiler.Front.ExprTree (Expr(Let, Lit, Tup, Rel, If, App, Fun), renewIdAndExprIds, StructEq(..), showExprTree)
import qualified Compiler.Front.ExprTree as E
import qualified Compiler.Front.ExprTree as ExprTree (Expr(Var))

import Compiler.Types2.TermLanguage (Term(..), Constr(..), Subst(..), MonadicUnifierExtension, 
  Scheme(..), SchemeEx(..), getIdsInIdTree, IdTree(..), forAllSubs, subInTerm,
  FunctionToken(..), Subst, monadicUnifyTrans, defaultMonadicUnifierExtension, emptyTermEnv, applyVarSubstsToConstr,
  bindTermInState, instantiateScheme, generalizeTerm, bindNewTermVarInState,
  instantiateSchemeEx, instantiateSchemeEx2, schemeEnvToSchemeExEnv, lookupTermMaybe,
  unifyConstraints, newTermVarFromState,
  labelTerm, labelTermRec, labelArgTermRec, labelRanTermRec, 
  addLabelsToTermRec, addLabelsToArgTermRec, addLabelsToRanTermRec, getLabels,
  stripTermLabels, stripTermLabelsRec,
  getVarIdsInTerm)
import Compiler.Types2.TermBuilder (ExpLbl(..), buildForIdxTree, fun, tup)
import Compiler.Types2.TypeAssignment (TyToken(..), TyTerm, TyConstr, TyScheme, TySchemeEx, TyEnv, 
  typeOfVal, rel, relNonOrd, showExprWithTypes)
import Compiler.Types2.Variables (VarSubsts, VarsIn(..), emptyVarSubsts, composeVarSubsts)
import qualified Compiler.Types2.Variables as Variables
import Compiler.Types2.EmbeddedFunctions

import Control.Monad.Identity (Identity, runIdentity)
import Control.Monad.State.Strict (StateT, runStateT, evalStateT, lift, get, modify)
import Control.Monad.Catch (MonadCatch(..))
import qualified Data.IntMap.Strict as IM
import qualified Data.Map.Strict as M
import qualified Data.Set as DS
import Data.Set (Set, unions, intersection, null)
import Data.IntMap.Strict ((\\))
import Debug.Trace (trace)
import Data.Maybe (fromMaybe, isJust)
import Data.List (intercalate, find)

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
  LTerm lbls t l -> LTerm lbls t $ map (applyTermSubst a b) l
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
  other -> error $ "DepTyAss:getIdExprPairs: IdTree and Expr tuple tree are not isomorphic: " ++ (showP ab)

-- TODO may need to update to work with term labels?
-- |Instantiates a term SchemeEx by replacing every qualified term variable
-- |with a new variable, and every function application qualified variable 
-- |with a ref to that var id (or expression id).
instantiateSchemeEx3 :: Monad m => VarMap TySchemeEx -> TySchemeEx -> Expr -> IdxMonad m TyTerm
instantiateSchemeEx3 varTys ts@(SchemeEx it inner) expr = do
  term <- instantiateScheme inner
  let varPairs = getIdExprPairs (it, expr)
  --if (sum $ map ((E.countExprs (\e -> E.isVarExpr e && E.getVarExprName e == "loop")) . snd) varPairs) > 0 then error $ "instSchemeEx3: found x0: " ++ (showP expr) ++ " binding to " ++ (showP ts) else return ()
  varSubs <- mapM (\(from,to) -> evalEmFunM (embedFun [] to) (error "DepTyAss:instSchemeEx3: call to embedFun should not use efsExpEnv!") varTys
                     >>= (\t -> return $ trace' ("Embed: " ++ (show to) ++ " => \n" ++ (show t) ++ "\n") $ (Var from) :|-> t)) varPairs 
  let subMap = IM.fromList $ map (\(Var vid :|-> e) -> (vid, e)) varSubs
  let term' = applyVarSubsts subMap term
  --let term' = forAllSubs subInTerm varSubs {-$ (if length varPairs > 0 then trace $ "VARPAIRS: " ++ (intercalate "\n" $ map (\(k,e) -> "(" ++ (show k) ++ ", " ++ (show $ E.getExprId e) ++ " " ++ (showP e) ++ ")") varPairs) ++ "\n\nVARSUBS: " ++ (showP varSubs) ++ "\n\n" ++ (showP $ E.getExprById 933 expr) ++ "\n\n" else id) $-} term
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
    let ty = labelTermRec (ProdLbl i) $ typeOfVal vl
    bindTermInState (Scheme [] ty) i
    return ([], ty)
  -- look for var binding in local var env
  (ExprTree.Var i vi s) -> case lookupVar globalEnv localEnv vi of
    (Just scheme) -> do
      term <- lift $ instantiateSchemeEx2 scheme
      let term' = labelTermRec (ProdLbl i) {-stripTermLabelsRec-} term
      bindTermInState (Scheme [] term') i
      return ([], term')
    (Nothing) -> error $ "Unbound var " ++ (show vi) ++ " " ++ s
                      ++ " when building dep type constraints."
  (Tup i l) -> do -- new tup term
    l' <- mapM (buildConstrs globalEnv localEnv) l
    if length l == 1 || length l' == 1 then error $ "tup with one child! " ++ (show exp) else return ()
    let (cl,tl) = unzip l'
    let term = tup tl
    bindTermInState (Scheme [] term) i
    return (concat cl, term)
  (Rel i l) -> case l of
    -- empty list: just a term var
    [] -> do
      v <- lift $ newTermVarFromState
      let v' = labelTerm (ProdLbl i) v
      bindTermInState (Scheme [] v') i
      return ([], v)
    -- non empty list: all children same type
    _  -> do
      l' <- mapM (\e -> buildConstrs globalEnv localEnv e) l
      let (cl,tl) = unzip l'
      let (headTy:tail) = tl
      let cl' = map (\ty -> headTy :=: ty) tail
      let ty = labelTermRec (ProdLbl i) $ rel headTy (relNonOrd)
      bindTermInState (Scheme [] ty) i -- TODO: change so not just non ord
      return ((concat cl) ++ cl', ty)
  (If i pe te ee) -> do -- PREPROCESSING NOW ELIMINATES IF EXPRESSIONS!
    v <- lift $ newTermVarFromState
    let v' = labelTerm (ProdLbl i) v
    bindTermInState (Scheme [] v') i
    (c1,t1) <- buildConstrs globalEnv localEnv pe
    (c2,t2) <- buildConstrs globalEnv localEnv te
    (c3,t3) <- buildConstrs globalEnv localEnv ee
    {-let t2' = labelTermRec (IfLbl i) t2
    let t3' = labelTermRec (IfLbl i) t3-}
    return ((c1 ++ c2 ++ c3) ++ [t2 :=: t3, v' :=: t2], v')
  (Let i it be ie) -> do 
    (c1,t1)          <- buildConstrs globalEnv localEnv be
    (newVarEnv, t1') <- buildForIdxTree it
    let newVarEnv' = varMapFromList $ schemeEnvToSchemeExEnv newVarEnv
    (c2, t2)  <- buildConstrs globalEnv (newVarEnv' `composeVarMaps` localEnv) ie
    let t2' = labelTermRec (ProdLbl i) t2
    bindTermInState (Scheme [] t2') i
    -- don't need to carry labels through from be, since only want to know about var exp ids
    -- so we strip them off
    return (c1 ++ [t1 :=: t1'] ++ c2, t2')
    --return ((stripTermLabelsRec t1 :=: stripTermLabelsRec t1'):(c1 ++ c2), t2')
  -- check if application of function with pi type
  (App i fe ae) -> do
    v <- lift $ newTermVarFromState
    let v' = labelTermRec (ProdLbl i) v
    bindTermInState (Scheme [] v') i
    (c2,t2) <- buildConstrs globalEnv localEnv ae
    case fe of
      -- if application of function var (check if has a dep type)
      (ExprTree.Var fi vi s) -> do
        -- instantiate dependent type scheme using
        -- func app argument expression
        case lookupVar globalEnv localEnv vi of
          (Just schemeEx) -> do 
            t1 <- lift $ instantiateSchemeEx3 globalEnv schemeEx ae
            let t1' = {-addLabelsToArgTermRec (getLabels t2) $ labelRanTermRec (ProdLbl i)-} t1
            bindTermInState (Scheme [] t1') fi
            let constr = (t1' :=: fun t2 v')
            return {- trace' ("AppConstr: " ++ s ++ ": " ++ (show constr) ++ "\n") $-} (constr:c2, v')
          (Nothing) -> error $ "Unbound function var " ++ (show vi) ++ " " ++ s
                    ++ " when building dep type constraints." 
      -- otherwise treat like any other function typed valueassignDepTypes
      _                      -> do 
        (c1,t1) <- buildConstrs globalEnv localEnv fe
        let t1' = {-addLabelsToArgTermRec (getLabels t2) $ labelRanTermRec (ProdLbl i)-} t1
        return (c1 ++ c2 ++ [t1' :=: fun t2 v'], v')
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

simplifyFunsUniferEx :: Monad m => MonadicUnifierExtension ExpLbl (FunctionToken TyToken) (StateT [(TyTerm, TyTerm)] (IdxMonad m))
simplifyFunsUniferEx env con@(a :=: b) = return $ Right con

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
  (IdxMonad m) (Either ([(TyTerm, TyTerm)], VarSubsts TyTerm) (TyConstr, VarSubsts TyTerm))
unify cl = do
  (either, subs1) <- runStateT (evalStateT (evalStateT (monadicUnifyTrans [Tok $ Ty "FBoth"] cl) simplifyFunsUniferEx) emptyTermEnv) []
  if subs1 /= [] then error $ "DepTyAss:unify: no subs should be stored in the state here.\n" else return ()
  case either of
    (Left sl)   -> do
      let subs2 = Variables.fromList $ map (\(v :|-> e) -> (fromMaybe (error $ "Types2/DepTyAss:unify:lambda only takes vars! " ++ (show v)) $ isVar v, e)) sl
      return $ Left (subs1, subs2)
    (Right (con,sl)) -> do
      let subs2 = Variables.fromList $ map (\(v :|-> e) -> (fromMaybe (error $ "Types2/DepTyAss:unify:lambda only takes vars! " ++ (show v)) $ isVar v, e)) sl
      return $ Right (con, subs2)

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
      let tyEnv2 = map (\(i,s) -> (i, applyVarSubstsToScheme subs2 s)) tyEnv
      --return tyEnv2
      -- simplify any remaining unsimplified embedded func and dim generators in tyEnv
      --(tyEnv3, cl2, simpSubs) <- applyDimGensInEnv tyEnv2 
      --let tyEnv4 = map (\(i, Scheme l t) -> (i, Scheme l $ applyTermSubsts simpSubs t)) tyEnv3
      let tyEnv4 = tyEnv2
      iw <- newidST dtvids
      case {-cl2-} [] of 
        -- if no more constraints produced, return env
        [] -> return $ trace' ("\nno extra constrs\n" ++ (show iw)) $ tyEnv4
        -- if more constraints, solve them too
        cl3 -> trace' ("\nrecur solveDepConstrs:\n" ++ (show cl3) ++ "\n" ++ (show iw)) $ solveDepConstrs tyEnv4 cl3
    Right (c@(a :=: b), subs) -> do
      -- apply substituions to type env
      let tyEnv2 = map (\(i,s) -> (i, applyVarSubstsToScheme subs s)) tyEnv
      error $ "Dependent type assignment failed on constraint:\n" ++ (show c) ++ "\n of \n" ++ (show cl) ++ "\n with \n" ++ (show tyEnv) 

assignDepTypes :: Monad m => VarMap TySchemeEx -> Expr -> IdxMonad m TyEnv
assignDepTypes varEnv expr = do
  -- create constraints
  ((cl,_),tyEnv) <- runStateT (buildConstrs varEnv IM.empty expr) emptyTermEnv
  -- solve constrs
  tyEnv' <- solveDepConstrs tyEnv $ trace' ("Constraints:\n" ++ (intercalate "\n" $ map show cl)) $ cl
  --error $ intercalate "\n" $ map show cl
  return tyEnv'

-- |DANGER! If applyDimGensInEnv can keep on producing new constraints
-- |then this will never terminate!
solveDepConstrs2 :: Monad m => TyEnv -> [TyConstr] -> IdxMonad m (Either TyEnv (TyConstr,TyEnv))
solveDepConstrs2 tyEnv cl = do
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
      --return tyEnv2
      -- simplify any remaining unsimplified embedded func and dim generators in tyEnv
      {-(tyEnv3, cl2, simpSubs) <- applyDimGensInEnv tyEnv2 
      let tyEnv4 = map (\(i, Scheme l t) -> (i, Scheme l $ applyTermSubsts simpSubs t)) tyEnv3
      iw <- newidST dtvids
      case cl2 of 
        -- if no more constraints produced, return env
        [] -> return $ trace' ("\nno extra constrs\n" ++ (show iw)) $ Left tyEnv4
        -- if more constraints, solve them too
        cl3 -> trace' ("\nrecur solveDepConstrs:\n" ++ (show cl3) ++ "\n" ++ (show iw)) $ solveDepConstrs2 tyEnv4 cl3-}
      return $ Left tyEnv2
    Right (c@(a :=: b), subs) -> do
      -- apply substituions to type env
      let tyEnv2 = map (\(i,s) -> (i, applyVarSubstsToScheme subs s)) tyEnv
      return $ Right (c, tyEnv2)

assignDepTypes2 :: Monad m => VarMap TySchemeEx -> Expr -> IdxMonad m (Either TyEnv (TyConstr, TyEnv))
assignDepTypes2 varEnv expr = do
  -- create constraints
  ((cl,_),tyEnv) <- runStateT (buildConstrs varEnv IM.empty expr) emptyTermEnv
  -- solve constrs
  res <- solveDepConstrs2 tyEnv $ trace' (
    "Constraints:\n" ++ (intercalate "\n" $ map show cl) ++ "\n" ++ 
    "TyEnv:\n" ++ (intercalate "\n" $ map show tyEnv) ++ "\n") $ cl
  --error $ intercalate "\n" $ map show cl
  return res

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
    tyEnv' <- solveDepConstrs tyEnv $ trace' ("assignFunDepTypes: " ++ (show $ head cl') ++ "\n") $cl'
    return tyEnv'
  other -> error $ "DepTypeAssignment:assignFunDepTypes: Requires a fun expr: " ++ (show expr) 

-- -------- New 26/06/2014 -------------------

trySimplifiedPair :: (Monad m, MonadCatch m) => 
  MonadicUnifierExtension ExpLbl (FunctionToken TyToken) (StateT ([TyConstr], Int) (IdxMonad m))
trySimplifiedPair env con@(a :=: b) = do
   -- call unify without this extension (so it can't get into an infinite loop of simplification)
  (res, subs1) <- runStateT (evalStateT (evalStateT (monadicUnifyTrans [Tok $ Ty "FBoth"] {-trace ("trySimpPair: " ++ (show con) ++ "\n") $-} [a :=: b]) defaultMonadicUnifierExtension) emptyTermEnv) []
  if (subs1 :: [Subst TyTerm]) /= [] then error $ "DepTypeAssignment:simplifyFunsUnifierEx:monadicUnifyTrans returned non empty subs: " ++ (show subs1) else return ()
  case res of
    -- if pass, then return the subs as constraints
    -- and mark that one simplifyable constraint has been solved
    Left subs2 -> do
      -- check if subs has a cycle
      if hasCycle DS.empty $ map (\(v :|-> e) -> (fromMaybe (error $ "Types2:DepTyAss:trySimpPair:lambad only takes vars! " ++ (show v)) $ isVar v, getVarIdsInTerm e)) subs2
      -- then fail
      then return $ Right (a :=: b)
      -- otherwise
      else do
        -- transform subs
        let subs3 = Variables.fromList $ map (\(v :|-> e) -> (fromMaybe (error $ "Types2/DepTyAss:simplifyFunsUnifierEx3:lambda only takes vars! " ++ (show v)) $ isVar v, e)) subs2
        -- check that subs2 leads to valid functions (i.e. doesn't expand params to be non tuples of vars)
        let a' = applyVarSubsts subs3 a
        let b' = applyVarSubsts subs3 b
        if areValidFuns [] a' && areValidFuns [] b'
        then do 
          -- if valid funs
          -- increment pass count
          return $ trace ("simplifyFunsUnifierEx3: passed: " ++ (show $ fmap showEmbeddedFuns $ fmap stripTermLabelsRec $ a :=: b) ++ "\n  with: " ++ (show subs2) ++ "\n" ++ "  giving: " ++ (show $ fmap showEmbeddedFuns $ fmap stripTermLabelsRec $ a' :=: b') ++ "\n\n") $ Left $ map (\(v :|-> t) -> v :=: t) subs2
        else do
          -- if not valid funs, then no simplification will make them valid, so fail here
          return $ Right (a :=: b)
    -- if fail, then add to constraints in state
    -- to be unified later
    Right (con,subs3) -> do
      return $ trace ("simplifyFunsUnifierEx3: delayed: " ++ (show $ fmap showEmbeddedFuns $ fmap stripTermLabelsRec $ a :=: b) ++ "\n") $ Right (a :=: b)

-- |Extends the unification function to simplify any embedded functions 
-- |before trying to unify.
simplifyFunsUniferEx3 :: (Monad m, MonadCatch m) => 
  IM.IntMap Expr -> IM.IntMap TySchemeEx ->
  MonadicUnifierExtension ExpLbl (FunctionToken TyToken) (StateT ([TyConstr], Int) (IdxMonad m))
simplifyFunsUniferEx3 expEnv varTys env con@(a :=: b) = do
  -- if fun terms/simplifyable
  if isFunTerm a && isFunTerm b
  then do
    -- simplify both terms
    (a', cl1) <- lift $ evalEmFunM (fullySimplifyFun a) expEnv varTys 
    (b', cl2) <- lift $ evalEmFunM (fullySimplifyFun b) expEnv varTys
    -- TODO CURRENTLY IGNORES cl1 and cl2
    --if cl1 /= [] then error $ "DepTypeAssignment:simplifyFunUnifierEx:fullySimplifyFun a: returned non empty constraints: " ++ (show cl1) else return ()
    --if cl2 /= [] then error $ "DepTypeAssignment:simplifyFunUnifierEx:fullySimplifyFun b: returned non empty constraints: " ++ (show cl2) else return ()
    -- get FBoth lists
    let al = fromFBoth a'
    let bl = fromFBoth b'
    let allpairs = [ (at :=: bt) | at <- al, bt <- bl ]
    -- try all combinations of terms from each fboth until one unifies
    resl <- mapM (trySimplifiedPair env) {- trace ("allpairs: " ++ (show allpairs) ++ "\nal:" ++ (show al) ++ "\nbl: " ++ (show bl) ++ "\n" ++ (show a) ++ "\n" ++ (show b) ++ "\n\n")-} allpairs
    let res = find isLeft resl
    case res of
      -- if at least one pair of constraints unified, then inc pass count
      Just (Left conl) -> do
         modify (\(cl,passCount) -> (cl,passCount+1))
         return $ Left conl
      -- if no pair of constraints unified, then add con to state to be unified later
      Nothing -> do
        modify (\(cl,passCount) -> ((a :=: b):cl, passCount))
        return $ Left []
  -- if not simplifyable, then fail 
  else return $ Right con

-- TODO debug!!!

-- |Unify all constraints. If a constraint doesn't pass and is simplifyable
-- |it is simplified and then re-tried. If a simplifyable constraint fails 
-- |it is saved to be tried again later. Unification fails if either a 
-- |non-simplifyable constraint is broken, or if we get to a fixed point where
-- |none of the remaining saved simplifyable constraints will pass.
unify3 :: (Monad m, MonadCatch m) => 
  IM.IntMap Expr -> IM.IntMap TySchemeEx -> VarSubsts TyTerm -> [TyConstr] -> 
  (IdxMonad m) (Either (VarSubsts TyTerm) (TyConstr, VarSubsts TyTerm))
unify3 expEnv varTys subsSoFar cl = do
  -- check for empty constraint list
  if cl == [] 
  then return $ Left subsSoFar
  else do 
    -- unify constraints
    (either, (residualCl, passCount)) <- runStateT (evalStateT (evalStateT (monadicUnifyTrans [Tok $ Ty "FBoth"] cl) $ simplifyFunsUniferEx3 expEnv {-(trace ("cl: " ++ (intercalate "\n" $ map show cl) ++ "\n\n"))-} varTys) emptyTermEnv) ([],0)
    case either of
      -- if success then check for any residual constraints
      (Left sl)   -> do
        -- transform subs
        let subs2 = Variables.fromList $ map (\(v :|-> e) -> (fromMaybe (error $ "Types2/DepTyAss:unify3:lambda only takes vars! " ++ (show v)) $ isVar v, e)) sl
        let subs3 = Variables.composeVarSubsts subs2 subsSoFar
        -- if there are residual constraints
        if residualCl /= []
        then if passCount > 0 
          -- and some constraints passed then iterate 
          then do
            -- apply subs to cons
            let residualCl' = map (\(a :=: b) -> (applyVarSubsts subs3 a) :=: (applyVarSubsts subs3 b)) residualCl
            -- iterate (tail recur)
            unify3 expEnv varTys subs3 residualCl'
          -- or no constraints passed then fail
          else return $ Right (head residualCl, subs3)
        -- else if there are no residual constraints then pass
        else return $ Left subs3
      -- if fail, then failed
      (Right (con,sl)) -> do
        let subs2 = Variables.fromList $ map (\(v :|-> e) -> (fromMaybe (error $ "Types2/DepTyAss:unify3:lambda only takes vars! " ++ (show v)) $ isVar v, e)) sl
        let subs3 = Variables.composeVarSubsts subs2 subsSoFar
        return $ Right (con, subs3)

-- |solveDepConstrs3 expEnv varTys tyEnv consL. Tries to solve all constraints
-- |in consL, returning the substitutions that make the constraints in consL
-- |unify if they unify, or the subsititutions so far and the failing constraint
-- |if it fails.
solveDepConstrs3 :: (Monad m, MonadCatch m) => 
  IM.IntMap Expr -> IM.IntMap TySchemeEx -> 
  TyEnv -> [TyConstr] -> IdxMonad m (Either TyEnv (TyConstr,TyEnv))
solveDepConstrs3 expEnv varTys tyEnv cl = do
  -- check constaints are disjoint (no circular vars)
  let cl1 = checkConstraints cl
  -- try and unify them (ignoring refs)
  res <- unify3 expEnv varTys Variables.emptyVarSubsts cl1
  case res of
    -- passed
    Left subs -> do
      -- apply substituions to type env
      let tyEnv2 = map (\(i,s) -> (i, applyVarSubstsToScheme subs s)) tyEnv
      return $ Left tyEnv2
    -- failed
    Right (c@(a :=: b), subs) -> do
      -- apply substituions to type env
      let tyEnv2 = map (\(i,s) -> (i, applyVarSubstsToScheme subs s)) tyEnv
      return $ Right (c, tyEnv2)

-- |assignDepTypes3 varEnv expr. Tries to infer the types for expr, building and solving constraints
-- |and simplifying those constraints that can be (i.e. embedded functions).
assignDepTypes3' :: (Monad m, MonadCatch m) => VarMap TySchemeEx -> Expr -> IM.IntMap Expr -> IdxMonad m (Either TyEnv (TyConstr, TyEnv))
assignDepTypes3' varEnv expr expEnv = do
  -- create constraints
  ((cl,_),tyEnv) <- runStateT (buildConstrs varEnv IM.empty expr) emptyTermEnv
  -- solve constrs
  res <- solveDepConstrs3 expEnv varEnv tyEnv $ trace' (
    "Constraints:\n" ++ (intercalate "\n" $ map show cl) ++ "\n" ++ 
    "TyEnv:\n" ++ (intercalate "\n" $ map show tyEnv) ++ "\n") $ cl
  --error $ intercalate "\n" $ map show cl
  return res

-- |assignDepTypes3 varEnv expr. Tries to infer the types for expr, building and solving constraints
-- |and simplifying those constraints that can be (i.e. embedded functions).
assignDepTypes3 :: (Monad m, MonadCatch m) => VarMap TySchemeEx -> Expr -> IdxMonad m (Either TyEnv (TyConstr, TyEnv))
assignDepTypes3 varEnv expr = do
  -- create expr environment
  let expEnv = IM.fromList $ E.makeExprMap expr 
  -- assign types
  assignDepTypes3' varEnv expr expEnv


