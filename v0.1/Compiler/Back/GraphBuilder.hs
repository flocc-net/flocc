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
module Compiler.Back.GraphBuilder where

import Compiler.Front.Common (lookupIntOrError, initIdxSet, updateListItem, vids, eids, imapUnionCheckDisjoint, debug, ShowP(..))
import Compiler.Front.Indices (Idx, IdxSet, newidST, IdxMonad) 
import Compiler.Front.ExprTree (Expr(..), IdxTree(..), Val(..), getExprId, getIdxTreeId, getIdxTreeVars)

--import Compiler.Types.TermLanguage (Term(Term), Scheme(Scheme), FunctionToken(TupTok))
--import Compiler.Types.TypeAssignment (TyTerm, TyScheme, showTyScheme)

import Compiler.Back.Graph hiding (Tree(Tup){-, TyScheme, Ty-})
import qualified Compiler.Back.Graph as B

import Data.List (sort)
import qualified Data.IntMap.Strict as IM
import qualified Data.IntSet as IS
import qualified Data.Map.Strict as DM

import Data.Functor.Identity (runIdentity)
import Control.Monad.State.Strict ( StateT, get, gets, modify, runStateT, evalStateT, execStateT, mapM, lift )

import Debug.Trace (trace)

-- TODO translate types?

-- Graph helpers

emptyGraphVars = DM.empty

emptyGraph :: Graph
emptyGraph = Graph {
  graphNodes=IM.empty,
  graphIn=(-1),
  graphOut=(-1),
  graphVars=emptyGraphVars
}

modifyNodes :: (NodeEnv Node -> NodeEnv Node) -> Graph -> Graph
modifyNodes f graph = graph { graphNodes=f $ graphNodes graph}

nd :: NodeId -> [NodeId] -> [NodeId] -> NodeTy -> Node
nd nid ins outs ty = Node {nodeId=nid, nodeIn=ins, nodeOut=outs, nodeTy=ty}

addNodeOut :: Node -> NodeId -> Node
addNodeOut node outid = node { nodeOut=(nodeOut node)++[outid] }

-- ======== DFG Creation from ExprTrees ==============

-- TODO change graph to graph stack!
-- need var ids above current....
-- can we pass a var env to graphFromExpr

data GBuildSt = GBuildSt {
    stVarToNodeMap :: NodeEnv Idx,
    stExpToNodeMap :: NodeEnv Idx,
    stCurGraph :: Graph,
    stVarNames :: DM.Map String Idx
  } deriving (Show)

initGBuildSt = GBuildSt {
    stVarToNodeMap=IM.empty,
    stExpToNodeMap=IM.empty,
    stCurGraph=emptyGraph,
    stVarNames=DM.empty
  }

type GraphBuilder m = StateT GBuildSt (StateT (NodeEnv Ty) (StateT IdxSet m))

modifyGraph :: Monad m => (Graph -> Graph) -> GraphBuilder m ()
modifyGraph f = modify (\st -> st { stCurGraph=f (stCurGraph st) })

-- |addExpToNodeMapping adds a mapping between the expression id and the node id
-- |that supercedes it.
addExpToNodeMapping :: Monad m => Idx -> Idx -> (GraphBuilder m) ()
addExpToNodeMapping exprId nodeId = modify (\st -> st { stExpToNodeMap=IM.insert exprId nodeId (stExpToNodeMap st) })

-- |addNode takes a node id and a list of input node ids, along with node and edge
-- |information, within a state monad containing a map of var ids to node ids, and
-- |the DFG, and adds this node to the DFG.
addNode :: Monad m => Node -> (GraphBuilder m) ()
addNode node = do
  -- add nodeId to the output list of all of its inputs
  modifyGraph $ modifyNodes (\nodes -> 
    foldl (\g -> \inId -> IM.adjust (\inputNode -> addNodeOut inputNode (nodeId $ node)) inId g) nodes $ nodeIn node)
  -- add node to the graph
  modifyGraph $ modifyNodes (\nodes -> IM.insert (nodeId node) node nodes)
  -- add mapping from expr id to node id
  let nodeid = nodeId node
  addExpToNodeMapping nodeid nodeid
  return ()

-- |addVarBinding takes a var id and an node id, and records a binding between
-- |the two in the state.
addVarBinding :: Monad m => Idx -> String -> Idx -> (GraphBuilder m) ()
addVarBinding varId varName nodeId = modify (\st -> st { 
  stVarToNodeMap=IM.insert varId nodeId (stVarToNodeMap st), 
  stVarNames=DM.insert varName nodeId (stVarNames st) })

-- |makeTupleAccessorNodes takes an idx tree and input node id
-- |and creates tuple accessor nodes for all nodes in the tree.
makeTupleAccessorNodes :: Monad m => Idx -> IdxTree -> (GraphBuilder m) ()
makeTupleAccessorNodes inId it = case it of
  (IdxNub _) -> return ()
  (IdxLeaf _ vid _) -> modify (\st -> st { stVarToNodeMap=IM.insert vid inId (stVarToNodeMap st) })
  (IdxTup _ l) -> do
    -- make accessor nodes
    nodeIds <- mapM (\_ -> lift $ lift $ newidST eids) l
    mapM (\(i, id) -> do addNode $ nd id [inId] [] (TupAccNd i)) $ zip [0..] nodeIds
    -- add type for each node
    tyEnv <- lift $ get
    let (B.Tup inTys) = lookupIntOrError "DFG:makeTupleAccessorNodes: get input expression type." inId tyEnv
    mapM (\(nid, ty) -> lift $ modify (\env -> IM.insert nid ty env)) $ zip nodeIds inTys
    -- call recursively for each accessor node
    mapM (\(id, subIt) -> makeTupleAccessorNodes id subIt) $ zip nodeIds l
    return () 

-- |addVarBindings takes an idx tree and an expression and adds the maps 
-- |between var ids and expression ids to the bindings.
addVarBindings :: Monad m => IdxTree -> Expr -> (GraphBuilder m) ()
addVarBindings it expr = case (it, expr) of
  -- ignore nub
  (IdxNub _, _)        -> return ()
  -- leaf
  (IdxLeaf eid vid vname, e) -> do
    modify (\st -> 
      let nid = (lookupIntOrError "DFG:addVarBindings:1:expr id not found in exprid->nodeid map." (getExprId e) (stExpToNodeMap st)) 
      in st { stVarToNodeMap=IM.insert vid nid (stVarToNodeMap st), 
              stVarNames=DM.insert vname nid (stVarNames st),
              stExpToNodeMap=IM.insert eid nid (stExpToNodeMap st) } )
   -- conformable tuples
  (IdxTup _ l, Tup _ l') | length l == length l' -> do 
    mapM (\(i,e) -> addVarBindings i e) $ zip l l'
    return ()
  -- non-conformable tuples
  -- (add accessor nodes to graph, and return them...)
  (IdxTup _ l, e) -> do
    expIdsToNodeIds <- gets stExpToNodeMap
    makeTupleAccessorNodes (lookupIntOrError "DFG:addVarBindings:2:expr id not found in exprid->nodeid map." (getExprId e) expIdsToNodeIds) it
  
-- |addIdxTreeBindings adds new VarNodes to the current graph 
-- |for all of the ids in the IdxTree
{-addIdxTreeBindings :: Monad m => IdxTree -> (GraphBuilder m) ()
addIdxTreeBindings it = case it of
  (IdxLeaf eid vid name) -> do 
    addNode $ nd eid [] [] (VarNd name) -- TODO add vid to VarNds
    addVarBinding vid eid
    -- I think we can omit the following, since the graphIn nodes don't seem to be used in building the DFG
    -- so instead we explicitly set the graphIn node id to the expr id of the root idx pattern in the
    -- Fun case of exprToGraph:
    -- --------------------
    --modify (\(m,g,b) -> (m, g { graphIn=if (graphIn g) /= (-1) then error $ "GraphBuilder:addIdxTreeBindings: multiple idx leaves being set as graph input!" else eid }, b))
    --modify (\(m,g,b) -> (m, g { graphIn=eid:(graphIn g) }, b))
  (IdxTup _ l) -> do mapM addIdxTreeBindings l; return ()
  other -> return ()-}

-- |addIdxTreeBindingsR tupleOffset nodeId indexTree. Creates tuple accessor nodes
-- |for the sub tree it, using nodeid as an input. 
addIdxTreeBindingsR :: Monad m => Int -> Idx -> IdxTree -> (GraphBuilder m) ()
addIdxTreeBindingsR tupIdx nodeid it = case it of
  -- add tuple accessor nodes
  (IdxTup eid l) -> do
    addNode $ nd eid [nodeid] [] (TupAccNd tupIdx)
    mapM (\(tupIdx', it') -> addIdxTreeBindingsR tupIdx' eid it') $ zip [0..] l
    return ()
  -- add leaf node
  (IdxLeaf eid vid name) -> do
    addNode $ nd eid [nodeid] [] (TupAccNd tupIdx)
    addVarBinding vid name eid
    return ()
  (IdxNub _) -> return ()

-- |addIdxTreeBindings idxTree. Creates nodes for the idx tree pattern.
addIdxTreeBindings :: Monad m => IdxTree -> (GraphBuilder m) Idx
addIdxTreeBindings it = do
  let eid = getIdxTreeId it
  addNode $ nd eid [] [] (VarNd "in")
  case it of
    (IdxTup _ l) -> do
      mapM (\(tupIdx', it') -> addIdxTreeBindingsR tupIdx' eid it') $ zip [0..] l
      return ()
    (IdxLeaf _ vid name) -> do addVarBinding vid name eid ; return ()
    _ -> return ()
  return eid

-- |addVarNode takes a var id and a node, and adds the node to the graph
-- |and adds its id to the output list of the expression that its bound to.
addVarNode :: Monad m => Idx -> Node -> (GraphBuilder m) Idx
addVarNode varId node = do
  -- get input node id from state
  varMap <- gets stVarToNodeMap
  graphs <- gets stCurGraph
  expMap <- gets stExpToNodeMap
  varNames <- gets stVarNames
  case IM.lookup varId varMap of
    -- if we can resolve to an input expression, just return its expression id
    Just inNodeId -> do 
      return inNodeId -- OLD: adds var node too --addNode $ addNodeInput node inNodeID
    -- if can't resolve to input expression, return this var node (as extern var)
    Nothing       -> do 
      --let name = getVarNodeName node
      --if name == "x0" 
      --then error $ "GraphBuilder:addVarNode: couldn't resolve " ++ name ++ " " ++ (show varId) ++ " to a node in:\n" ++ (showP varMap) ++ "\n" ++ (show varNames) ++ "\n"
      --else do
      addNode node
      return $ nodeId node --nodeId [] (ExternVarNode varId) nullVal 
                   --error $ "addVarNode: no node bound to var " ++ (show varId) 

-- |getDFG inputs takes a DFG and returns all the node id's that occur as inputs
-- |that are not defined in the graph.
getGraphInputs :: Graph -> IS.IntSet
getGraphInputs graph = inputIDs IS.\\ nodeIDs
  where nodes = graphNodes graph
        inputIDs = IS.unions $ map (\(k, node) -> IS.fromList $ nodeIn node) $ IM.toList nodes
        nodeIDs = IM.keysSet nodes

getEdgeType :: NodeEnv Ty -> Idx -> Ty
getEdgeType env exprId = case IM.lookup exprId env of
  Just ty -> ty
  Nothing -> error $ "getEdgeType: expression " ++ (show exprId) ++ " is not in the type environment."

toScalVal :: Val -> ScalVal
toScalVal v = case v of
  (S s) -> StrVal s
  (I i) -> IntVal i
  (B b) -> BolVal b
  (F f) -> FltVal f
  (NullVal) -> NulVal
  other -> error $ "GraphBuilder:toScalVal: error can't translate Val " ++ (show v) ++ " to ScalVal."

-- |exprToDFG takes an expression and creates a DFG in the state transformer,
-- |returning the node id of the expression.
exprToGraph :: Monad m => NodeEnv Ty -> Expr -> (GraphBuilder m) Idx
exprToGraph env expr = do
  st0 <- get
  case {-trace ((showP expr) ++ "\n\n" ++ (show st0)) $-} expr of
    (Lit i v) -> do
      addNode $ nd i [] [] (LitNd $ toScalVal v)
      return i
    (Var i vid name) -> do
      varNodeID <- addVarNode vid $ nd i [] [] (VarNd name) -- newDFGNode i [] (VarNode vid name) []
      addExpToNodeMapping i varNodeID
      return varNodeID
    (Tup i l) -> do
      l' <- mapM recur l
      addNode $ nd i l' [] TupNd --newDFGNode i l' (TupNode) [] --(newEdge i)
      return i
    (Rel i l) -> do
      l' <- mapM recur l
      addNode $ error "GraphBuilder:exprToGraph:Rel case: not implemented."  --newDFGNode i l' (RelNode) [] --(newEdge i)
      return i
    (App i fe ae) -> do
      fi <- recur fe
      ai <- recur ae
      addNode $ nd i [fi,ai] [] AppNd --newDFGNode i [fi, ai] (AppNode) [] --(newEdge i)
      return i
    (If i pe te ee) -> do -- TODO should be nested 
      error $ "GraphBuilder:exprToGraph:If not implemented. Pre-process to convert to 'if' func apps." 
      {--- visit predicate
      pi <- recur pe
      (m1, g1, b1) <- get
      -- visit 'then' subtree
      modify (\(m,g,b) -> (m, emptyGraph, b))
      ti <- recur te
      (_, thenGraph, _) <- get
      let thenGraph' = Digraph {
          graphParent=graphParent thenGraph,
          graphName=graphName thenGraph, 
          graphNodes=graphNodes thenGraph, 
          graphInNodes=graphInNodes thenGraph,
          graphOutNode=ti 
        }
      -- visit 'else' subtree
      modify (\(m,g,b) -> (m, emptyGraph, b))
      ei <- recur ee
      (_, elseGraph, _) <- get
      let elseGraph' = Digraph {
          graphParent=graphParent elseGraph,
          graphName=graphName elseGraph, 
          graphNodes=graphNodes elseGraph, 
          graphInNodes=graphInNodes elseGraph,
          graphOutNode=ei 
        }
      -- return to top level graph and add ifthenelse node
      modify (\(_,_,b) -> (m1, g1, b))
      addNode $ newDFGNode i [pi] (IfNode) [thenGraph', elseGraph'] -- (newEdge i)
      return i-}
    (Let i it be ie) -> do
      recur be
      varEnv <- gets stVarToNodeMap
      varNames <- gets stVarNames
      addVarBindings it be
      inExpID <- recur ie
      --st <- get
      --if elem "y0" (map fst $ getIdxTreeVars it) then error $ "Let: " ++ (show st) ++ "\n\n" else return ()
      modify (\st -> st { stVarToNodeMap=varEnv , stVarNames=varNames })
      addExpToNodeMapping i inExpID
      return inExpID -- go straight from inExpression (can omit the let entirely)
    (Fun i it exp) -> do
      -- save current graph
      m1 <- gets stVarToNodeMap
      names0 <- gets stVarNames
      g1 <- gets stCurGraph
      b1 <- gets stExpToNodeMap
      -- create subgraph
      modify (\st -> st { stCurGraph=emptyGraph })
      inNodeId <- addIdxTreeBindings it
      expI <- recur exp
      -- add output var node
      outEid <- lift $ lift $ newidST eids
      addNode $ nd outEid [expI] [] (VarNd "out")
      -- add in and out to current subgraph
      modify (\st -> st { stCurGraph=(stCurGraph st) { graphIn=inNodeId, graphOut=expI, graphVars=names0 } })
      m2 <- gets stVarToNodeMap
      innerGraph <- gets stCurGraph
      b2 <- gets stExpToNodeMap
      let inputIDs = getGraphInputs innerGraph
      -- return to original graph
      modify (\st -> st { stVarToNodeMap=m1, stVarNames=names0, stCurGraph=g1 } )
      addNode $ nd i (IS.toList inputIDs) [] (FunNd innerGraph) --newDFGNode i (Data.Set.toList inputIDs) (FunNode it) [innerGraph] --(newEdge i)
      let i' = {-trace ("exprToGraph:FunNd:created from:\nGraph:"++ (show innerGraph) ++ "\nExpr: " ++ (show expr) ++ "\n\n")-} i
      return i'
    where recur = exprToGraph env
          --newEdge = (\i -> ValEdge $ getEdgeType env i)

-- |graphFromExpr takes an expression and returns the corresponding 
-- |data flow graph.
graphFromExpr :: Monad m => NodeEnv Ty -> Expr -> IdxMonad m (Graph, NodeEnv Ty)
graphFromExpr env expr = do
  -- build graph from expr
  --let tyEnv = IM.map (\(Scheme _ t) -> t) env
  ((outID, st1), tyEnv') <- runStateT (runStateT (exprToGraph env expr) initGBuildSt) env
  let (varMap, graph, eidsToNids, varNames) = (stVarToNodeMap st1, stCurGraph st1, stExpToNodeMap st1, stVarNames st1)
  let graph' = graph { graphOut=outID, graphVars=varNames {-imapUnionCheckDisjoint "GraphBuilder:graphFromExpr:adding varMap:" (graphVars graph) varMap-} }
  -- update node ids of all the graphs in tyEnv'
  let tyEnv'' = IM.map (mapGraphsInTy (replaceNodeIds eidsToNids)) tyEnv'
  return (graph', if debug then trace ("graphFromExpr: new types: \n" ++ (show tyEnv') ++ "\nupdated types: " ++ (show tyEnv'')) tyEnv'' else tyEnv'')

-- =======================

mapNodeM :: Monad m => (Node -> m Node) -> Node -> m Node
mapNodeM f n = do
  n' <- f n
  case nodeTy n' of
    (FunNd g) -> do
      g' <- mapGraphM f g
      return $ n' { nodeTy=(FunNd g') }
    _ -> return n'

mapGraphM :: Monad m => (Node -> m Node) -> Graph -> m Graph
mapGraphM f g = do
  let nodes = IM.elems $ graphNodes g
  nodes' <- mapM f nodes
  let nodes'' = IM.fromList $ map (\n -> (nodeId n, n)) nodes' 
  return $ g { graphNodes=nodes'' }

-- |encapFun node ty. Encapsulates n in a FunNd subgraph, and adds types of new
-- |expressions to the state.
encapFun :: Monad m => Node -> Ty -> StateT (NodeEnv Ty) (IdxMonad m) Node
encapFun n ty = do
  let (VarNd vname) = nodeTy n
  -- create expression
  varVid <- lift $ newidST vids
  varEid <- lift $ newidST eids
  let varName = ("v" ++ (show varVid))
  let varExpr = Var varEid varVid varName
  funVid <- lift $ newidST vids
  let funExpr = Var (nodeId n) funVid vname
  appEid <- lift $ newidST eids
  let appExpr = App appEid funExpr varExpr
  patEid <- lift $ newidST eids
  let patExpr = IdxLeaf patEid varVid varName
  lamEid <- lift $ newidST eids
  let lamExpr = Fun lamEid patExpr appExpr
  -- add new types for new exprs
  let (inTy :-> outTy) = ty
  types <- get
  let types' = IM.union types $ IM.fromList [
                 (varEid, inTy),
                 (nodeId n, ty),
                 (appEid, outTy),
                 (patEid, inTy),
                 (lamEid, ty) 
               ]
  -- build graph for it
  (g, types'') <- lift $ graphFromExpr types' lamExpr
  -- create FunNd to contain graph
  nid <- lift $ newidST eids
  let n' = nd nid (nodeIn n) (nodeOut n) (FunNd g)
  modify (\_ -> IM.insert nid ty types'')  
  return n'

-- |encapFun n. If n is a var with a function type, then encapsulate it: replace it with a 
-- |a simple FunNd with a subgraph that calls it.
encapFuns :: Monad m => Node -> StateT (NodeEnv Ty) (IdxMonad m) Node
encapFuns n = case nodeTy n of
  -- a var node
  -- TODO NEED TO ADD CHECK TO SEE IF THIS IS BEING IMMEDIATELY APPLIED.
  --   IF IT IS A CHILD OF AN APPNODE, THEN ITS A COMBINATOR RATHER THAN A 
  --   FUNCTION PARAMTER AND SHOULD NOT BE ENCAPSULATED.
  (VarNd vname) -> do
    -- get var type
    let nid = nodeId n
    ty <- gets (lookupIntOrError ("GraphBuilder:encapFun: missing type for node " ++ (show n)) nid) 
    case isFunTree ty of
      -- var is a function
      True -> encapFun n ty
      -- is not a function
      False -> return n
  -- any other node 
  other -> return n

--postProcessGraph :: Monad m => Graph -> IdxMonad m Graph
--postProcessGraph g = mapGraphM () g

