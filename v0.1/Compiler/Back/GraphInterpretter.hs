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
module Compiler.Back.GraphInterpretter where

import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IM
import Data.Map.Strict as Data.Map (Map, alter)
import Control.Monad.State.Strict (StateT, get, gets, modify, lift, execStateT)
import Data.Functor.Identity (runIdentity)

import Debug.Trace (trace)

import Compiler.Front.Common (listGet)

import Compiler.Back.Graph
import Compiler.Back.GenDecls
import Compiler.Back.Gen

appLayout :: Ty -> [Int] -> [Int] 
appLayout (Lf (FunTy graph)) list = ordValToIntList $ result'
  where inNid = graphIn graph
        outNid = graphOut graph
        startEnv = IM.fromList [(inNid, intListToOrdVal list)]
        endEnv = runIdentity (execStateT (visitGraphM applyVisitor [graph]) startEnv)
        outVal = endEnv IM.! outNid
        result' = foo2 outVal
appLayout ty list = error $ "graphInterpretter:appLayout: only supports FunTys: " ++ (show ty)

--appInvLayout :: Ty -> Tree Int
--appInvLayout (Lf (FunTy graph)) =
--  where pathTree = createTreePathTree [] 

intListToOrdVal :: [Int] -> OrdVal
intListToOrdVal list = TreeOV $ Tup $ map ((Lf).(LitOV).(IntVal)) list

ordValToIntList :: OrdVal -> [Int]
ordValToIntList val = case val of
  ListOV l -> map (\(LitOV (IntVal i)) -> i) l
  TreeOV (Tup l) -> map (\(Lf (LitOV (IntVal i))) -> i) l
  other -> error $ "ordValToIntList: " ++ (show val)

-- |appFunV funNode inVar outVar. Applies funNode to value
-- |stored in inVar and stores result in outVar.
appFunV :: Monad m => NodeTreeEx -> IdTree -> Id -> GenM m
appFunV funNode inVar outVar = do
  -- get input val
  valTr <- visitTreeM (\i -> do v <- getLocalVal i; return $ Lf $ toOrdVal v) inVar
  -- lookup fun graph
  (GraphV graph) <- getFun funNode
  let inNid = graphIn graph
  let outNid = graphOut graph
  -- assign input value to input node
  let startEnv = IM.fromList [(inNid, TreeOV valTr)]
  -- visit graph (get result)
  let endEnv = runIdentity (execStateT (visitGraphM applyVisitor [graph]) startEnv)
  -- get output value from output node
  let outVal = endEnv IM.! outNid
  -- assign result to out var
  let result = fromOrdVal outVal
  --let result' = processOuts result
  let result' = foo result
  --let result' = treeValToVar "appFunV:processing output:" result
  updateThisEnv (\env -> Data.Map.alter (\_ -> Just result') outVar env)  
  return ()

-- convert subtrees of vars into vars

isTreeV :: Monad m => Val m -> Bool
isTreeV (TreeV _) = True
isTreeV _ = False

getTreeV :: Monad m => Val m -> Tree (Val m)
getTreeV (TreeV v) = v

{-isVarV :: Monad m => Val m -> Bool
isVarV (VarV _ _) = True
isVarV _ = False-}

getVarTy :: Monad m => Val m -> Ty
getVarTy (VarV ty _) = ty

getVarId :: Monad m => Val m -> IdTree
getVarId (VarV _ id) = id

foo :: Monad m => Val m -> Val m
foo v = case v of
  (TreeV (Lf v2)) -> foo v2
  (TreeV (Tup l)) -> case l' of
      _ | and $ map isTreeV l' -> TreeV $ Tup $ map getTreeV l'
      _ | and $ map isVarV l'  -> VarV (Tup $ map getVarTy l') (Tup $ map getVarId l') 
      other -> (TreeV (Tup l))
    where l' = map (foo.TreeV) l
  other -> other

isTreeOV :: OrdVal -> Bool
isTreeOV (TreeOV _) = True
isTreeOV _ = False

getTreeOV :: OrdVal-> Tree (OrdVal)
getTreeOV (TreeOV v) = v

getOVarTy :: OrdVal -> Ty
getOVarTy (VarOV ty _) = ty

getOVarId :: OrdVal -> IdTree
getOVarId (VarOV _ id) = id

foo2 :: OrdVal -> OrdVal
foo2 v = case v of
  (TreeOV (Lf v2)) -> foo2 v2
  (TreeOV (Tup l)) -> case l' of
      _ | and $ map isTreeOV l' -> TreeOV $ Tup $ map getTreeOV l'
      _ | and $ map isVarOV l'  -> VarOV (Tup $ map getOVarTy l') (Tup $ map getOVarId l') 
      other -> (TreeOV (Tup l))
    where l' = map (foo2.TreeOV) l
  other -> other

{-processOuts :: Monad m => Val m -> Val m
processOuts (TreeV tree) = varTreeToVar tree
processOuts other = other

-- TODO NEED TO WRITE A METHOD FROM TREE OF VARVs TO SINGLE VARV

varTreeToVar :: Monad m => Tree (Val m) -> Val m
varTreeToVar tree = case tree of
  (Tup l) -> if allVars then treeValToVar "appFunV:varTreeToVar:" (Tup l'') else (TreeV $ Tup l'')
    where l' = map varTreeToVar l
          allVars = and $ map isVarV l'  
          l'' = map Lf l'
  other -> TreeV other
varTreeToVar v = error $ "bla"  ++ (show v)-}

varToVarTree :: OrdVal -> Tree OrdVal
varToValTree _ = error "boom!"
varToVarTree (VarOV ty id) = case (ty,id) of
  (t, Lf i) -> Lf $ VarOV t (Lf i)
  (Tup t, Tup l) | length t == length l -> Tup $ map (\(t1,i1) -> varToVarTree (VarOV t1 i1)) $ zip t l
  other -> error $ "varToVarTree: fun node: " ++ (show other)
varToVarTree other = error $ "varToVarTree: " ++ (show other)

 -- TreeV v -> TreeOV $ mapTree toOrdVal v
valToTree :: OrdVal -> Tree OrdVal
valToTree ov = case ov of
  (TreeOV ov2) -> visitTree valToTree ov2
  (VarOV ty id) -> varToVarTree (VarOV ty id)
  (ListOV l) -> Tup $ map Lf l
  other -> Lf other

-- |propagates values through the graph
applyVisitor :: Monad m => [Graph] -> Node -> StateT (IntMap OrdVal) m ()
applyVisitor [graph] node = case nodeTy node of
  -- combine vals into tuple/tree
  (TupNd) -> do
    -- get vals from inputs
    inVals <- mapM (\nid -> gets (IM.! nid)) $ nodeIn node
    let subTrees = map valToTree inVals 
    -- combine into a tree
    let newTree = TreeOV $ Tup $ subTrees
    -- assign to env
    modify (IM.insert (nodeId node) newTree)
    return ()
  -- select val from a tuple/tree
  (TupAccNd idx) -> do
    -- get val from input
    let [nid] = nodeIn node
    inVal <- gets (IM.! nid)
    let inVal' = valToTree inVal
    -- get right leaf
    case inVal' of
      (Tup l) | length l > idx -> do
        -- get val
        let val = TreeOV $ listGet "GraphInt:applyVisitor" l idx
        -- assign to env
        modify (IM.insert (nodeId node) val)
        return ()
      other -> error $ "applyVisitor error: TupAccNd idx:" ++ (show idx) ++ "; val: " ++ (show inVal') ++ "\n"
  -- anything else
  _ -> return ()

{-
data NodeTy = 
    VarNd String
  | GlobalVarNd Ty String
  | FunNd {-NodeId-} Graph
  | AppNd
  | LitNd ScalVal
  | TupNd 
  | TupAccNd Int
  | LstNd 
-}

-- |appInvLayout graph. Returns the output idx of all the input vars.
appInvLayout :: Ty -> Tree Int
appInvLayout (Lf (FunTy graph)) = case outVal of
    -- zip paths with output idxs and convert to tree
    Lf path   -> treePathsToIdxTree [Tup [Lf path]] 
    Tup paths -> treePathsToIdxTree paths
  where -- create and propagate tree paths
        inNid = graphIn graph
        outNid = graphOut graph
        startEnv = IM.empty
        endEnv = runIdentity (execStateT (visitGraphM propTupVisitor [graph]) startEnv)
        outVal = endEnv IM.! outNid
appInvLayout ty = error $ "graphInterpretter:appInvLayout: only supports FunTys: " ++ (show ty)

-- |treePathsToIdxTree leafList. Takes a list of leaves each holding a tree path,
-- |zips each path with its output offset, and creates a tree from the paths.
treePathsToIdxTree :: [Tree TreePath] -> Tree Int
treePathsToIdxTree inPaths = tree
  where paths = map (treeLeaf "graphInterpretter:treePathsToIdxTree") inPaths
        pairs = zip paths [0..]
        tree  = createTreeFromPaths pairs []

-- |creates and propagates tree paths through the graph
propTupVisitor :: Monad m => [Graph] -> Node -> StateT (IntMap (Tree [Int])) m ()
propTupVisitor [graph] node = case nodeTy node of
  -- combine vals into tuple/tree
  (TupNd) -> do
    -- get vals from inputs
    inVals <- mapM (\nid -> gets (IM.! nid)) $ nodeIn node
    -- combine into a tree
    let newTree = Tup $ inVals
    -- assign to env
    modify (IM.insert (nodeId node) newTree)
    return ()
  -- select val from a tuple/tree
  (TupAccNd idx) -> do
    -- get val from input
    let [nid] = nodeIn node
    inVal <- gets (IM.lookup nid)
    case inVal of
      Just (Tup l) | length l > idx -> do
        -- get val
        let val = listGet "GraphInt:propTupVisitor" l idx
        -- assign to env
        modify (IM.insert (nodeId node) val)
        return ()
      -- extend the path by one
      Just (Lf path) -> do
        modify (IM.insert (nodeId node) (Lf $ idx:path))
        return ()
      -- create a new path
      Nothing -> do
        modify (IM.insert (nodeId node) (Lf [idx]))
        return ()
      other -> error $ "propTupVisitor error: TupAccNd idx:" ++ (show idx) ++ "; val: " ++ (show inVal) ++ "\n"
  -- anything else
  _ -> return ()


