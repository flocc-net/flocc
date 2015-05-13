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
module Compiler.Types2.Builder where

import Compiler.Front.Common (delimList, maybeError)
import Compiler.Front.Indices (Idx, IdxSet, IdxMonad)
import Compiler.Front.ExprTree (Expr(Let, Lit, Tup, Rel, If, App, Fun), renewIdAndExprIds, StructEq(..), showExprTree)
import qualified Compiler.Front.ExprTree as ExprTree (Expr(Var))

import Compiler.Types2.TermLanguage (Term(..), Constr(..), Subst(..), MonadicUnifierExtension, 
  Scheme(..), SchemeEx(..), getIdsInIdTree, IdTree(..), forAllSubs, subInTerm,
  FunctionToken(..), Subst, monadicUnifyTrans, emptyTermEnv, applyVarSubstsToConstr,
  bindTermInState, instantiateScheme, generalizeTerm, bindNewTermVarInState,
  instantiateSchemeEx, instantiateSchemeEx2, schemeEnvToSchemeExEnv, lookupTermMaybe,
  unifyConstraints, labelTerm, newTermVarFromState)
import Compiler.Types2.TermBuilder (ExpLbl(..), buildForIdxTree, fun, tup)
import Compiler.Types2.TypeAssignment (TyToken(..), TyTerm, TyConstr, TyScheme, TySchemeEx, TyEnv, 
  typeOfVal, rel, relNonOrd, showExprWithTypes)
import Compiler.Types2.Variables (VarSubsts, VarsIn(..), emptyVarSubsts, composeVarSubsts)
import qualified Compiler.Types2.Variables as Variables (fromList)
import Compiler.Types2.EmbeddedFunctions

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

varMapFromSchemeEnv :: [(Idx, Scheme l t)] -> VarMap (Term l t)
varMapFromSchemeEnv l = varMapFromList $ map (\(i, Scheme l t) -> if length l /= 0 then error $ "varMapFromSchemeEnv:non empty var list:" ++ (show l) else (i,t)) l

-- |composeVarMaps creates the left biased union of 
-- |VarMaps a and b.
composeVarMaps :: VarMap a -> VarMap a -> VarMap a
composeVarMaps a b = a `IM.union` b

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
instantiateSchemeEx3 :: Monad m => VarMap TySchemeEx -> TySchemeEx -> Expr -> IdxMonad m TyTerm
instantiateSchemeEx3 varTys (SchemeEx it inner) expr = do
  term <- instantiateScheme inner
  let varPairs = getIdExprPairs (it, expr)
  varSubs <- mapM (\(from,to) -> evalEmFunM (embedFun [] to) (error "DepTyAss:instSchemeEx3: call to embedFun should not use efsExpEnv!") varTys
    >>= (\t -> return $ trace ("Embed: " ++ (show to) ++ " => \n" ++ (show t) ++ "\n") $ (Var from) :|-> t)) varPairs 
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
    let ty = labelTerm (ProdLbl i) $ typeOfVal vl
    bindTermInState (Scheme [] ty) i
    return ([], ty)
  -- look for var binding in local var env
  (ExprTree.Var i vi s) -> case lookupVar globalEnv localEnv vi of
    (Just scheme) -> do
      term <- lift $ instantiateSchemeEx2 scheme
      let term' = labelTerm (ProdLbl i) term
      bindTermInState (Scheme [] term') i
      return ([], term')
    (Nothing) -> error $ "Unbound var " ++ (show vi) ++ " " ++ s
                      ++ " when building dep type constraints."
  (Tup i l) -> do -- new tup term
    l' <- mapM (buildConstrs globalEnv localEnv) l
    let (cl,tl) = unzip l'
    let term = labelTerm (ProdLbl i) $ tup tl
    bindTermInState (Scheme [] term) i
    return (concat cl, term)
  (Rel i l) -> case l of
    -- empty list: just a term var
    [] -> do
      v <- lift $ newTermVarFromState
      let v' = labelTerm (ProdLbl i) v
      bindTermInState (Scheme [] v') i
      return ([], v')
    -- non empty list: all children same type
    _  -> do
      l' <- mapM (\e -> buildConstrs globalEnv localEnv e) l
      let (cl,tl) = unzip l'
      let (headTy:tail) = tl
      let cl' = map (\ty -> headTy :=: ty) tail
      let ty = rel headTy (relNonOrd)
      let ty' = labelTerm (ProdLbl i) ty 
      bindTermInState (Scheme [] ty') i -- TODO: change so not just non ord
      return (cl' ++ (concat cl), ty)
  (If i pe te ee) -> do
    v <- lift $ newTermVarFromState
    let v' = labelTerm (ProdLbl i) v
    bindTermInState (Scheme [] v') i    
    (c1,t1) <- buildConstrs globalEnv localEnv pe
    (c2,t2) <- buildConstrs globalEnv localEnv te
    (c3,t3) <- buildConstrs globalEnv localEnv ee
    return ((v :=: t2):(v :=: t3):(c1 ++ c2 ++ c3), v')
  (Let i it be ie) -> do
    (c1,t1)          <- buildConstrs globalEnv localEnv be
    (newVarEnv, t1') <- buildForIdxTree it
    let newVarEnv' = varMapFromList $ schemeEnvToSchemeExEnv newVarEnv
    (c2, t2)  <- buildConstrs globalEnv (newVarEnv' `composeVarMaps` localEnv) ie
    let t2' = labelTerm (ProdLbl i) t2
    bindTermInState (Scheme [] t2') i
    return ((t1 :=: t1'):(c1 ++ c2), t2')
  -- check if application of function with pi type
  (App i fe ae) -> do
    v <- lift $ newTermVarFromState
    let v' = labelTerm (ProdLbl i) v
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
            bindTermInState (Scheme [] t1) fi
            let constr = (t1 :=: fun t2 v')
            return $ trace ("AppConstr: " ++ s ++ ": " ++ (show constr) ++ "\n") $ (constr:c2, v')
          (Nothing) -> error $ "Unbound function var " ++ (show vi) ++ " " ++ s
                    ++ " when building dep type constraints." 
      -- otherwise treat like any other function typed valueassignDepTypes
      _                      -> do 
        (c1,t1) <- buildConstrs globalEnv localEnv fe
        return ((t1 :=: fun t2 v'):(c1 ++ c2), v')
  -- dive another level down
  (Fun i it e) -> do
    (newVarEnv, t1) <- buildForIdxTree it
    let newVarEnv' = varMapFromList $ schemeEnvToSchemeExEnv newVarEnv
    (cl, t2) <- buildConstrs globalEnv (newVarEnv' `composeVarMaps` localEnv) e
    let term = (fun t1 t2)
    bindTermInState (Scheme [] term) i
    return (cl, term)

-- |Check that the constraints are all disjoint (no circular variables)
checkConstraints :: [TyConstr] -> [TyConstr]
checkConstraints l = l'
  where l' = map (\(a :=: b) -> if (not $ Data.Set.null $ (getVars a) `intersection` (getVars b))
                   then error $ "circle: " ++ (show (a,b)) ++ "\n"
                   else (a :=: b) ) l
