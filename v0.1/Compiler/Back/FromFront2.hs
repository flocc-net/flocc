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
module Compiler.Back.FromFront2 (translateTypes, translateTyMap, translateTyEnv) where

import Compiler.Front.Indices (IdxMonad)
import Compiler.Front.Common (intersects, ShowP(..), debug)

import qualified Compiler.Front.ExprTree as E
import qualified Compiler.Types2.TypeInfo as F
import qualified Compiler.Types2.Variables as F
import qualified Compiler.Types2.TermLanguage as F
import qualified Compiler.Types2.TypeAssignment as F
import qualified Compiler.Types2.DepTypeAssignment as F
import qualified Compiler.Types2.EmbeddedFunctions as F
import qualified Compiler.Back.Graph as B
import qualified Compiler.Back.GraphBuilder as B

import qualified Data.IntMap.Strict as IM
import Data.Maybe (fromMaybe, isJust)
import Control.Monad.State.Strict ( lift, StateT, runStateT, get, gets, modify )
import Control.Monad.Catch
import Debug.Trace (trace)
import Data.List ((\\))

trace' = if debug then trace else \_ -> id

-- |translateTy type. Translates a front end type to a back end type.
{-translateTy :: F.TyTerm -> B.Ty
translateTy ty = case ty of
  (F.Term t l) -> case t of
    (F.FunTok) | length l == 2 -> (translateTy $ head l) B.:-> (translateTy $ head $ tail l) 
    (F.TupTok) -> B.Tup $ map translateTy l
    (F.Tok (F.Ty name)) -> B.Lf $ B.LfTy name l'
      where l' = map translateTy l
  (F.Var idx) -> error $ "Compiler.Back.FromFront:translateTy: front end type still contains type var " ++ (show idx) ++ "!\n" -- B.Lf $ B.VarTy $ show idx
  (F.Ref idx) -> error $ "Compiler.Back.FromFront:translateTy: front end type still contains ref " ++ (show idx) ++ "!\n"

-- |translateTyEnv. Translates a front end type environment to a back end
-- |one. Throws an error if input still contains a scheme with a bound variable.
translateTyEnv :: F.TyEnv -> B.NodeEnv B.Ty 
translateTyEnv env = IM.fromList tyList
  where tyList = map (\(idx, s@(F.Scheme l t)) 
                   -> if length l /= 0 
                      then error $ "Compiler.Back.FromFront: translateTyEnv: non-concrete type: " ++ (show s) 
                      else (idx, translateTy t)) env-}

--- ----

data FromFrontSt = FromFrontSt {
    stExprMap :: IM.IntMap E.Expr,
    stVarTypes :: IM.IntMap F.TySchemeEx,
    stFrontExprTypes :: IM.IntMap F.TyTerm,
    stExprTypes :: IM.IntMap B.Ty,
    stNodeTypes :: IM.IntMap B.Ty
  } 

type FromFrontM m = StateT FromFrontSt (IdxMonad m)

-- |translateTypes expEnv varTypes expTypes. Translates an environment of frontend types
-- |into back end types.
translateTypes :: (MonadCatch m, Monad m) => IM.IntMap E.Expr -> IM.IntMap F.TySchemeEx -> IM.IntMap F.TyTerm -> IdxMonad m (IM.IntMap B.Ty)
translateTypes expEnv varTypes expTypes = do
  (types1, st) <- runStateT (translateTyMap expTypes) $ FromFrontSt { stExprMap=expEnv, stVarTypes=varTypes, stFrontExprTypes=expTypes, stExprTypes=IM.empty, stNodeTypes=IM.empty } 
  let types = disjointOrEqUnion "translateTypes1" types1 ((stNodeTypes st) `IM.union` (stExprTypes st))
  return types 

-- |translateTyMap frontEnvTypes. Translates an environment of front end
-- |types into, one of back end types.
translateTyMap :: (MonadCatch m, Monad m) => IM.IntMap F.TyTerm -> FromFrontM m (IM.IntMap B.Ty)
translateTyMap env = do
  l' <- mapM (\(eid, tm) -> do ty' <- translateTy $ F.stripTermLabelsRec tm; return (eid, ty')) $ IM.toAscList env 
  return $ IM.fromAscList $ l'  

-- |translateTyEnv frontEnvTypes. Translates an environment of front end
-- |types into, one of back end types.
translateTyEnv :: (MonadCatch m, Monad m) => F.TyEnv -> FromFrontM m (IM.IntMap B.Ty)
translateTyEnv env = do
  l' <- mapM (\(eid, F.Scheme [] ty) -> do ty' <- translateTy $ F.stripTermLabelsRec ty; return (eid, ty')) env 
  return $ IM.fromList $ l'  

-- |translateTy type. Translates a front end type to a back end type.
translateTy :: (MonadCatch m, Monad m) => F.TyTerm -> FromFrontM m B.Ty
translateTy ty = do
  let rec = translateTy
  case ty of
    (F.Term t l) -> case (t,l) of
      (F.FunTok, [a,b]) -> do 
        a' <- rec a 
        b' <- rec b
        return $ a' B.:-> b'
      (F.TupTok,l) -> do
        l' <- mapM rec l
        return $ B.Tup l'
      (F.Tok (F.Ty name), l) -> case (name, l) of
        -- distributed collections:
        ("DArr", [mode,idx,val,layF,parF,parD,mirrD]) -> do
          -- apply recursively
          [mode', idx', val'] <- mapM rec [mode, idx, val]
          [parD', mirrD'] <- mapM translateDimTy [parD, mirrD]
          --(nullLayF,_) <- lift $ F.simplifyFun (F.Term (F.Tok (F.Ty "FNull")) []) -- fun to use if embedded fun is a UniVar
          layF' <- translateEmExpr idx layF --nullLayF
          --(nullParF,_) <- lift $F.simplifyFun (F.Term (F.Tok (F.Ty "FId")) [])
          parF' <- translateEmExpr idx parF --nullParF 
          -- nest in type
          return $ B.Lf $ B.LfTy "DArr" [mode', idx', val', layF', parF', parD', mirrD'] 
        ("DMap", [mode,key,val, ordF, parF,parD,mirrD]) -> do
           -- apply recursively
          [mode', key', val'] <- mapM rec [mode, key, val]
          [parD', mirrD'] <- mapM translateDimTy [parD, mirrD]
          --(nullOrdF,_) <- lift $ F.simplifyFun (F.Term (F.Tok (F.Ty "FNull")) []) -- if is univar
          ordF' <- translateEmExpr (F.Term F.TupTok [key,val]) ordF --nullOrdF
          --(nullParF,_) <- lift $ F.simplifyFun (F.Term (F.Tok (F.Ty "FId")) []) -- if is univar
          parF' <- translateEmExpr (F.Term F.TupTok [key,val]) parF --nullParF
          -- nest in type
          return $ B.Lf $ B.LfTy "DMap" [mode', key', val', ordF', parF', parD', mirrD']  
        -- other named types:
        other -> do 
          -- check for vars with defaults
          let l1 = map (\(idx,v) -> if isJust $ F.isVar v then fromMaybe v (F.typeDefault name idx) else v) $ zip [0..] l
          -- translate any dim ids
          let diml = F.dimLocs name
          l2 <- mapM (\(i,v) -> if elem i diml then translateDimTy v else rec v) $ zip [0..] l1      
          return $ B.Lf $ B.LfTy name l2
          --mapM rec l >>= (return.(B.Lf).(B.LfTy name))
    --(F.UniVar idx) -> return $ B.unknownFunTy
    (F.Var idx) -> error $ "Compiler.Back.FromFront:translateTy: front end type still contains type var " ++ (show idx) ++ " (check TypeInfo)!\n" -- B.Lf $ B.VarTy $ show idx
    (F.Ref idx) -> error $ "Compiler.Back.FromFront:translateTy: front end type still contains ref " ++ (show idx) ++ "!\n"

-- |Check intersection is empty before unioning.
disjointUnion :: Show a => String -> IM.IntMap a -> IM.IntMap a -> IM.IntMap a
disjointUnion err a b = case IM.intersection a b of
  c | IM.null c -> IM.union a b
  c             -> error $ err ++ "FromFront:distjointUnion: map domains not disjoint!\n" ++ 
                                   "A /\\ B = " ++ (show c) ++ "\n" ++
                                   "B /\\ A = " ++ (show $ IM.intersection b a) ++ "\n" ++
                                   (show a) ++ "\n" ++ (show b)
-- |Check intersection is empty, or vals are equal for any keys that appear in both. 
disjointOrEqUnion :: (Eq a, Show a) => String -> IM.IntMap a -> IM.IntMap a -> IM.IntMap a
disjointOrEqUnion err a b = case IM.intersection a b of
  c | IM.null c -> IM.union a b
  c -> case c == (IM.intersection b a) of
         True -> IM.union a b
         False -> error $ err ++ "FromFront:distjointOrEqUnion: map domains not disjoint!\n" ++ 
                                   "A /\\ B = " ++ (show c) ++ "\n" ++
                                   "B /\\ A = " ++ (show $ IM.intersection b a) ++ "\n" ++
                                   (show a) ++ "\n" ++ (show b)

scmEx :: F.TyTerm -> F.TySchemeEx
scmEx ty = F.SchemeEx F.IdBlank (F.Scheme [] ty)

-- |translateEmExp domainType funTerm. Translates a function embedded in a 
-- |front end type, into a backend FunTy type. This involves translating it
-- |into a front end expression, inferring types, translating these types,
-- |and building a backend graph from the front end expression.
translateEmExpr :: (MonadCatch m, Monad m) => F.TyTerm -> F.TyTerm -> {- F.TyTerm ->-} FromFrontM m B.Ty
translateEmExpr domTy term {-nullTerm-} = do
  -- convert from type to function expr
  expEnv <- gets stExprMap
  varTys <- gets stVarTypes
  (term',_) <- lift $ F.evalEmFunM (F.fullySimplifyFun term) expEnv varTys
  -- CHECK SIMPLIFIED EMBEDDED FUN HAS NO FUN APPS REMAINING
  --if F.termContains (F.Tok $ F.Ty "FApp") term' 
  --then error $ "Back:FromFront2:translateEmExpr: simplified embedded function still contains fun apps:\n" ++ (F.showEmbeddedFuns term') 
  --else return ()
  exp <- lift $ F.unembedFun expEnv term'
  case exp of
    -- function contained a unique var, so function is unknown
    Nothing -> {-translateEmExpr domTy nullTerm (error $ "Back:FromFront2:translateEmExpr: default fun is UniVar:\n" ++ (show nullTerm))-} return B.nullTy
    -- function was successfully unembedded
    Just expr -> do
      -- for any vars bound outside the expr, find their exp ids, 
      -- and use these to get their type from the original ast
      varTypes <- gets stVarTypes
      expTypes1 <- gets stFrontExprTypes
      let freeVars = E.getFreeExprVars expr
      let outerVids = (map snd freeVars) \\ (IM.keys varTypes)
      let varEids = E.getVarExprIds expr
      let outerVarTypes = map (\vid -> let eid = fromMaybe (error $ "FromFront2:transEmExpr: no eid for var " ++ (show vid) ++ 
                                                                    " in " ++ (show varEids) ++ " from " ++ (show expr)) $ lookup vid varEids in
                                        let ty = fromMaybe (error $ "FromFront2:transEmExpr: no type for var exp with eid " ++ (show eid) ++ " exp:" ++ (show expr) ++ "\n" ++ (E.showExprTreeWithIds expr)) $ IM.lookup eid expTypes1 in
                               (vid,ty)) outerVids
      let varTypes' = varTypes `IM.union` (IM.map scmEx $ IM.fromList outerVarTypes)
      -- infer type of function
      let assTys = lift $ F.assignFunDepTypes varTypes' domTy (trace' ("Back:FromFront2:translateEmExpr: inferring types of embedded fun:\n" ++ (show expr) ++ "\nwith domty:\n" ++ (show domTy)) expr)
      exprTypes <- catch assTys (\e -> error $ "assigning types in translateEmExpr for\n" ++ (showP expr) ++ "\ndom ty = " ++ (showP domTy) ++ "\n" ++ "do all your embedded functions match their collections' key/value types?" ++ "\n\n" ++ (show (e :: SomeException)))
      -- convert types to back end types, and add to state
      exprTypes' <- translateTyEnv $ trace' ("Back:FromFront2:translateEmExpr: infered types of embedded fun:\n" ++ (show expr) ++ "\n") $ exprTypes
      modify (\st -> st { stExprTypes=(disjointOrEqUnion "translateEmExpr1") (stExprTypes st) exprTypes' })
      -- convert function to graph, and add node types to state 
      (graph, nodeTypes) <- lift $ B.graphFromExpr exprTypes' expr
      modify (\st -> st { stNodeTypes=(disjointOrEqUnion "translateEmExpr2") (stNodeTypes st) nodeTypes })
      -- nest graph in a FunTy
      return $ B.Lf $ B.FunTy $ trace' ("transEmExpr: " ++ (show term) ++ " :: " ++ (show domTy) ++ " -> X = \n" ++ (E.showExprTreeWithIds expr) ++ "\n" ++ (show graph)) $ graph
  
-- |translateDimTy t. Returns a backend type representing the frontend dim type.
translateDimTy :: Monad m => F.TyTerm -> m B.Ty
translateDimTy term = case term of
  (F.Term F.TupTok l) -> mapM translateDimTy l >>= ((return).B.Tup) 
  (F.Term (F.Tok (F.Ty "Null")) []) -> return $ B.Lf $ B.LfTy "Null" []
  (F.Var vid) -> return $ B.Lf $ B.VarTy $ "v" ++ (show vid)
  (F.Term (F.Tok (F.Ty "Intersect")) l) -> do 
    let vidL = map F.getVarIdsInTerm l
    let vids = intersects vidL
    if length vids > 0
    then return $ B.Tup $ map (\v -> B.Lf $ B.VarTy $ "v" ++ (show v)) vids
    else return $ B.Lf $ B.LfTy "Null" []
  other -> error $ "FromFront:translateDimTy: Invalid dim type:\n" ++ (show other)

