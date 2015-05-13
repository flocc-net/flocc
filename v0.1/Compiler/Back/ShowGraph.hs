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
module Compiler.Back.ShowGraph where

import Compiler.Front.Common
import Compiler.Front.Indices
import Compiler.Back.Graph

import Control.Monad ( mapM )
import Control.Monad.State.Strict (State, runState, StateT, evalStateT, lift, modify, get)
import Data.Functor.Identity (runIdentity)
--import Data.Map.Strict (Map)
--import qualified Data.Map.Strict as Data.Map
import qualified Data.IntMap.Strict as IM 

-- ======= GRAPHVIZ DOT Drawing =========

-- TODO Write display code that can show variables etc at nodes
-- TODO Write code to translate value type terms into variable types.

type ShowNodeFunc n m = n -> m String 

-- |showNodeFrom map is a ShowNodeFunc that takes a map of idx's to strings
-- |and returns that string for every node in the map.
showNodeFromMap :: Monad m => ShowNodeFunc Node (StateT (NodeEnv String) m)
showNodeFromMap n = do
  let id = nodeId n
  mp <- get
  let s = lookupIntOrValue id mp "<error not in map>" 
  return $ dotDrawLabel n s

-- |showNodeNothing is the default ShowNodeFunc that just calles the dotDraw function for
-- |the node it is passed. 
showNodeNothing :: Monad m => ShowNodeFunc Node m
showNodeNothing n = return $ dotDraw n

-- creates a name for a node
nodeName :: Idx -> String
nodeName id = "n" ++ (show id)

-- |dotDrawSubgraph takes a display function and a digraph and renders it
-- |in an xdot cluster subgraph.
dotDrawSubgraph :: Monad m => ShowNodeFunc Node m -> Graph -> StateT IdxSet m String
dotDrawSubgraph showF graph = do
  clusterID <- newidST graphClusterIDs
  let n = "cluster" ++ (show clusterID)
  inner <- (dotDrawGraph showF graph)
  return $ "subgraph " ++ n ++ " {\n" ++ inner ++ "\n}\n"

-- |dotDrawSubgraphs takes a graph node and outputs all of 
-- |it's subgraphs.
dotDrawSubgraphs :: Monad m => ShowNodeFunc Node m -> Node -> StateT IdxSet m String
dotDrawSubgraphs showF node = case nodeTy node of
  FunNd subGraph  -> do 
    g <- dotDrawSubgraph showF subGraph
    return g
  other -> return ""

-- |dotDrawEdges takes a graph node and returns a ; delimited list of 
-- |edges in dot format.
dotDrawEdges :: Node -> String
dotDrawEdges node = outEdges
  where thisID = nodeId node
        --outEdges = delimList ";\n" $ map (\id -> (nodeName thisID) ++ " -> " ++ (nodeName id)) $ nodeOutputs node
        outEdges = concat $ map (\id -> (nodeName thisID) ++ " -> " ++ (nodeName id) ++ ";\n") $ nodeOut node

-- |dotDrawGraph takes a graph and draws it the internals
-- |of a graphviz dot file.
dotDrawGraph :: Monad m => ShowNodeFunc Node m -> Graph -> StateT IdxSet m String
dotDrawGraph showF graph = do 
  let nodes = snd $ unzip $ IM.toList $ graphNodes graph
  subgraphList <- mapM (dotDrawSubgraphs showF) nodes
  let subgraphs = (concat subgraphList)
  let edgeList = map dotDrawEdges nodes
  let edges = (concat $ edgeList)
  drawnNodes <- lift $ mapM showF nodes
  let outID = graphOut graph
  let drawnNodes' = ((nodeName outID) ++ " -> outnode" ++ (show outID)):drawnNodes
  let nodeAttrs = (delimList ";\n" $ drawnNodes') 
  return $ "label = \"" ++ (graphName graph) ++ "\";\n" 
        ++ "color=blue;\n" 
     --   ++ "style=filled;\n"
        ++ subgraphs 
        ++ edges
        ++ nodeAttrs

-- |DotDrawable exports the dotDraw function.
class DotDrawable a where
  dotDraw :: a -> String

dotDrawLabel :: Node -> String -> String 
dotDrawLabel node s = nodeNm ++ " [label=\"" ++ (show nid) ++ "\\n" ++ s ++ "\"]"
  where nid = nodeId node
        nodeNm = nodeName $ nodeId node

-- |Instance of DotDrawable for Digraphs.
instance DotDrawable Graph where
  dotDraw g = "digraph "++ (graphName g) ++" {\n" ++ s ++ "\n}\n"
    where s = runIdentity $ evalStateT (dotDrawGraph showNodeNothing g) (initIdxSet 0)

dotDrawWithMap :: Graph -> NodeEnv String -> String
dotDrawWithMap g env = "digraph "++ (graphName g) ++" {\n" ++ s ++ "\n}\n"
    where s = runIdentity $ evalStateT (evalStateT (dotDrawGraph showNodeFromMap g) (initIdxSet 0)) env

-- |Instance of DotDrawable for graph nodes.
instance DotDrawable Node where
  dotDraw node = dotDrawLabel node (dotDraw $ nodeTy node)

-- |Instance of DotDrawable for graph node attributes.
instance DotDrawable NodeTy where
  dotDraw = show

-- |showNodeFrom map is a ShowNodeFunc that takes a map of idx's to strings
-- |and returns that string for every node in the map.
showDFNodeFromMap :: Monad m => ShowNodeFunc Node (StateT (NodeEnv String) m)
showDFNodeFromMap n = do
  mp <- get
  let s = lookupIntOrValue (nodeId n) mp "<error not in map>" 
  let s' = (show $ nodeId n) ++ ": " ++ (show $ nodeTy n) ++ "\\n" ++ s
  return (dotDrawLabel n s')

dotDrawDFGWithMap :: Graph -> NodeEnv String -> String
dotDrawDFGWithMap g env = "digraph "++ (graphName g) ++" {\n" ++ s ++ "\n}\n"
    where s = runIdentity $ evalStateT (evalStateT (dotDrawGraph showDFNodeFromMap g) (initIdxSet 0)) env

{-
instance Nullable ExprNode where
  nullVal = IdNode
visitDigraphDepthFirst
data ExprEdge =
    NullEdge
  | ValEdge TyScheme

instance Show ExprEdge where
  show e = case e of
    NullEdge -> ""
    ValEdge ty -> case ty of 
      (Scheme l (Term TupTok l')) -> ""
      (Scheme l (Term FunTok l')) -> ""
      other -> (showTyScheme ty) 

instance Nullable ExprEdge where
  nullVal = NullEdge

class DotShow n where
  nodeName :: n -> String

--instance DotShow DFGNode where
--  nodeName n = -}

