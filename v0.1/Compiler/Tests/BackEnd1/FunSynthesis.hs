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
module Compiler.Tests.BackEnd1.FunSynthesis where

import Compiler.Tests.BackEnd1.NodeLayouts

import Compiler.Back.Graph
import Compiler.Back.Gen
import Compiler.Back.GenDecls

import Data.Maybe (fromMaybe, fromJust)
import Control.Monad.State.Strict (modify)
import Data.IntMap.Strict as Data.IntMap (fromList, insert, elems)
import Data.Map.Strict as DM (insert)
import Data.Char (toLower)

nd :: NodeId -> [NodeId] -> [NodeId] -> NodeTy -> (NodeId, Node)
nd nid ins outs ty = (nid, Node {nodeId=nid, nodeIn=ins, nodeOut=outs, nodeTy=ty})

-- id fun graph
graphId = Graph {
  graphIn=60,
  graphOut=60,
  graphNodes=Data.IntMap.fromList [
    nd 60 [] [61] (VarNd "in"),
    nd 61 [60] [] (VarNd "out")
  ]
}

-- proj snd
graphSnd = Graph {
  graphIn=19,
  graphOut=20,
  graphNodes=Data.IntMap.fromList [
    nd 19 [] [20]   (VarNd "in"),
    nd 20 [19] [21] (TupAccNd 1),
    nd 21 [20] []   (VarNd "out")
  ]
}

-- proj fst
graphFst = Graph {
  graphIn=19,
  graphOut=20,
  graphNodes=Data.IntMap.fromList [
    nd 19 [] [20]   (VarNd "in"),
    nd 20 [19] [21] (TupAccNd 0),
    nd 21 [20] []   (VarNd "out")
  ]
}


-- mod n fun graph
graphModN :: Ty -> Id -> Graph
graphModN ty n = Graph {
  graphIn=70,
  graphOut=74,
  graphNodes=Data.IntMap.fromList [
    nd 70 [] [72] (VarNd "in"),
    nd 71 [] [72] (GlobalVarNd ty n),
    nd 72 [70,71] [74] TupNd,
    nd 73 [] [74] (VarNd "mod"),
    nd 74 [73,72] [75] AppNd,
    nd 75 [74] [] (VarNd "out")
  ]
}

--lookupTy :: NodeEnv Ty -> NodeId -> [Ty] 

instGraph :: Monad m => Graph -> GenM1 m Graph
instGraph fgraph = do
  -- generate new ids for it
  newNids <- createNewNodeIds fgraph
  -- get ids of function vars
  let funNids = map nodeId $ findInGraph (isVarNd.nodeTy) fgraph
  -- copy types to new nids for all functions
  -- globTypes.genConsts
-- TODO finish off!
  --let tyList = concat $ map () funNids
  -- replace node ids
  let nfgraph = replaceNodeIds newNids fgraph
  return nfgraph

-- |synFun ty. Creates a fun graph for the algebraic
-- |function def in ty. Returns that 
synthesiseFun :: Monad m => Ty -> GenM1 m (Val m)
synthesiseFun ty = case ty of
  (Lf (LfTy name l)) -> case (map toLower name,l) of
    ("id", _)  -> return $ GraphV graphId
    ("fst", _) -> return $ GraphV graphFst
    ("snd", _) -> return $ GraphV graphSnd
    ("modn", [nodeLayout]) -> do 
      -- get node layout part count variable
      maybeVar <- getLayoutVar nodeLayout
      case maybeVar of
        Just (VarV _ (Lf nlVar)) -> do 
          -- make and inst graph
          let fgraph = graphModN intTy (nlVar ++ ".partitionCount")
          nfgraph <- instGraph fgraph
          -- WORKAROUND: Set mod to right type
          let [modNode] = findInGraph (\n -> (nodeTy n) == (VarNd "mod")) nfgraph
          modify (\s -> s {genConsts = (genConsts s) { 
             globTypes = Data.IntMap.insert (nodeId modNode) 
               (Tup [intTy, intTy] :-> intTy) ((globTypes.genConsts) s) } })
          -- return graph to mod by it
          return $ GraphV $ nfgraph
        Nothing -> genError $ "synthesiseFun: node layout " ++ (show nodeLayout) ++ " doesn't exist in globals!"
    other -> error $ "FunSynthesis: not implemented! can't yet deal with non-trivial functions!\n" ++ (show other) 
  other -> error $ "FunSynthesis: not implemented! can't yet deal with non-trivial functions!\n" ++ (show other) 

-- |genFun codeVarName funVal inVars outVars. Generates code to implement
-- |funVal using input vars inVars and outVars outVars (stored in local env).
-- |Stores the resultant code in the local env as codeVarName.
genFunFromTy :: Monad m => Id -> Ty -> IdTree -> IdTree -> GenM m
genFunFromTy codeVarName ty inVars outVars = do
  -- get fun
  funVal <- synthesiseFun ty
  -- get vars 
  inV <- visitTreeM (\i -> do v <- getLocalVal i; return $ Lf v) inVars
  outV <- visitTreeM (\i -> do v <- getLocalVal i; return $ Lf v) outVars
  let inVar = (treeValToVar "genFunFromTy:inV:" inV) 
  let outVar = (treeValToVar "genFunFromTy:outV:" outV)
  -- generate code
  code <- evalFun funVal inVar outVar
	-- assign code to codeVarName
  updateThisEnv (\env -> DM.insert codeVarName (CodeV code) env) 
  return ()

genFunsFromTy :: Monad m => Id -> Ty -> Ty -> IdTree -> IdTree -> GenM m
genFunsFromTy codeVarName f1Ty f2Ty inVars outVars = do
  genTrace $ "entered FunSynthesis:genFunsFromTy with " ++ codeVarName ++ " = " ++ 
    (show f2Ty) ++ "." ++ (show f1Ty) ++ " applied to " ++ (show $ inVars :-> outVars) 
    -- get funs
  (GraphV fun1) <- synthesiseFun f1Ty
  (GraphV fun2) <- synthesiseFun f2Ty
  -- sequentially compose funs
  let funVal = GraphV $ seqComposeGraphs fun1 fun2
  -- get vars 
  inV <- visitTreeM (\i -> do v <- getLocalVal i; return $ Lf v) inVars
  outV <- visitTreeM (\i -> do v <- getLocalVal i; return $ Lf v) outVars
  let inVar = (treeValToVar "genFunFromTy:inV:" inV) 
  let outVar = (treeValToVar "genFunFromTy:outV:" outV)
  -- generate code
  code <- evalFun funVal inVar outVar
	-- assign code to codeVarName
  updateThisEnv (\env -> DM.insert codeVarName (CodeV code) env)
  return ()


