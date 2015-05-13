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
module Compiler.Back.GenDecls where

import Compiler.Front.Common (debug)

import Compiler.Back.Graph
import Compiler.Back.StrTemplates
import Compiler.Back.Helper

import qualified Data.Set (toList)
import qualified Data.Set as DS
import qualified Data.IntSet as IS
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as Data.IntMap
import qualified Data.IntMap.Strict as IM
import Data.Map.Strict (Map, adjust, update, unionWith, unionsWith)
import qualified Data.Map.Strict as Data.Map (map, toList, lookup, empty, alter, keys, insert)
import Control.Monad.State.Strict (StateT, lift, get, gets, modify, execStateT)
import Data.Maybe (fromMaybe, isJust, fromJust)
import Data.Functor.Identity (runIdentity)
import Data.List (intersperse, partition)

import Debug.Trace (trace)

data Kind =
    CodeK
  | VarK
  | TypeK
  | GraphK
  deriving (Show, Eq)

type Id = String

type IdTree = Tree Id

{-decomposeIdTreeForType :: Ty -> IdTree -> IdTree
decomposeIdTreeForType ty id = case (ty, id) of
  (Lf v) -> 
  (Tup l) -> 
  (a :-> b) -> -}

type Code = String

data Val m =
    CodeV Code
  | VarV Ty IdTree
  | TyV Ty
  | IdV Id
  | GraphV {-NodeId-} Graph
  | FunV (Maybe IdTree) (TemplateProc m)
  | BoolV Bool
  | TreeV (Tree (Val m))
  | ListV [Val m]
  | LitV ScalVal

isVarV (VarV _ _) = True
isVarV _ = False

isTyV (TyV _) = True
isTyV _ = False

instance Show (Val m) where
  show val = case val of
    (CodeV code) -> "code {" ++ code ++ "}"
    (VarV ty id) -> "var:" ++ (show id) ++ " :: " ++ (show ty)
    (TyV ty) -> "ty:" ++ (show ty)
    (IdV id) -> "id:" ++ (show id)
    (GraphV {-inNid-} graph) -> "graph :" {-(in:" ++ (show inNid) ++ ") "-} ++ (show graph)
    (FunV idTree proc) -> "FunV" 
    (BoolV v) -> show v
    (TreeV v) -> "tree:" ++ (show v)
    (ListV l) -> "[" ++ (concat $ intersperse ", " $ map show l) ++ "]"
    (LitV v) -> show v

instance Monad m => Eq (Val m) where 
  a == b = case (a, b) of
    (CodeV x, CodeV y) -> x == y
    (VarV t1 i1, VarV t2 i2) -> (t1 == t2) && (i1 == i2)
    (IdV i1, IdV i2) -> i1 == i2
    (GraphV g1, GraphV g2) -> g1 == g2
    (BoolV x, BoolV y) -> x == y
    (TreeV t1, TreeV t2) -> t1 == t2
    (ListV l1, ListV l2) -> and $ map (\(x,y) -> x == y) $ zip l1 l2
    other -> error $ "Eq (Val m). Can't compare " ++ (show a) ++ " and " ++ (show b)
  a /= b = not $ a == b 

fromIntVal :: Monad m => Val m -> Int
fromIntVal (LitV (IntVal i)) = i
fromIntVal other = error $ "Back:GenDecls:fromIntVal: expected LitV (IntVal i)), got: " ++ (show other)

-- |fromTreeVal val. If val is a TreeV val, returns the
-- |value it encloses, otherwise throws an error.
fromTreeVal :: Monad m => Val m -> Tree (Val m)
fromTreeVal v = case v of
  TreeV t -> t
  other -> error $ "fromTreeVal: non TreeV passed: " ++ (show v) 

-- |fromFunNode funNode. Takes a FunNd and returns the
-- |same value as a GraphV.
fromFunNode :: Monad m => NodeTy -> Val m
fromFunNode (FunNd {-nid-} graph) = GraphV {-nid-} graph

fromTyVal :: Monad m => String -> Val m -> Ty
fromTyVal msg (TyV v) = v
fromTyVal msg other = error $ msg ++ ":GenDecls:fromTyVal: is not a TyVal: " ++ (show other)

-- |mergeVals v1 v2. Tries to merge v1 and v2. Only
-- |works if they are both code values.
mergeVals :: Monad m => String -> Val m -> Val m -> Val m
mergeVals errCtx v1 v2 = case (v1,v2) of
  (CodeV c1, CodeV c2) -> CodeV (c1 ++ c2)
  other -> error $ "mergeVals: Can't merge vals: " ++ (show v1) ++ "\n"
              ++ (show v2) ++ "\n" ++ errCtx

-- TODO fix so actually visits all types
tidyTy :: Ty -> Ty
tidyTy ty = tidyTree ty

-- TODO fix so actually visits all subtrrees of TreeV
-- |tidyVal val. Removes redundant tuples from all
-- |nested trees. 
tidyVal :: Monad m => Val m -> Val m
tidyVal v = case v of
  VarV ty id -> VarV (tidyTy ty) (tidyTree id)
  TyV ty -> TyV (tidyTy ty)
  TreeV v -> TreeV $ tidyTree v
  other -> other  

type ValEnv m = Map Id (Val m)

emptyValEnv = Data.Map.empty

-- |Convert a val to code
renderVal :: Monad m => String -> String -> Val m -> Code
renderVal msg valName v = case v of
  CodeV c   -> c
  VarV ty it -> case it of
    (Lf i) -> i
    other  -> error $ msg ++ "renderVal: can't convert non-leaf variable " ++ (show other) ++ " called " ++ valName ++ " to code!"
  TyV ty    -> error $ msg ++ "renderVal: can't convert type " ++ (show ty) ++ " called " ++ valName ++ " to code!"
  IdV id    -> id
  GraphV {-nid-} g  -> error $ msg ++ "renderVal: can't convert graph " ++ (show g) ++ " called " ++ valName ++ " to code!"
  FunV _ _ -> error $ msg ++ "renderVal: can't convert function to code!"
  BoolV v -> if v then "true" else "false"
  TreeV v -> error $ msg ++ "renderVal: can't convert tree val " ++ (show v) ++ " called " ++ valName ++ " to code!"
  ListV l -> error $ msg ++ "renderVal: can't convert list val " ++ (show l) ++ " called " ++ valName ++ " to code!"
  LitV v -> show v

applyTem :: Monad m => String -> StrTem -> [(Id, Val m)] -> Code
applyTem msg tem [] = tem
applyTem msg tem ((id,v):tail) = applyTem msg (applyT tem [(id, renderVal (msg ++ ":applyTem:" ++ tem ++ ":") id v)] ) tail

-- |lookups up a value from a ValEnv and throws error if it doesn't
-- |exist.
lookupVal :: Monad m => String -> Id -> ValEnv m -> Val m
lookupVal errMsg key env = fromMaybe 
  (error (errMsg ++ "\nlookupVal: val " ++ key ++ " is not in the env:\n" ++ (show env))) 
  $ Data.Map.lookup key env

lookupValMaybe :: Monad m => Id -> ValEnv m -> Maybe (Val m)
lookupValMaybe = Data.Map.lookup

-- |varVal errMsg val returns the type and idtree of a val if it is a var
-- |or throws the error message if it is not.
varVal :: Monad m => String -> Val m -> (Ty, IdTree)
varVal errMsg val = case val of
  VarV ty it -> (ty, it)
  other      -> error $ errMsg ++ "\nvarVal: " ++ (show other) ++ " is not a var!" 

-- |lookupSubVal val path. Looks up the sub var, or sub type
-- |found using the path. Throws an error if the path is non
-- |null and the val doesn't contain a tree, or doesn't contain
-- |a node for the path.
lookupSubVal :: Monad m => String -> Val m -> TreePath -> Val m
lookupSubVal errMsg1 val path = case path of
    -- an empty path
    [] -> val
    -- a non-empty path (so must be a var or type)
    _  -> case val of
            -- variables
            VarV ty id -> case lookupTreeNodeMaybe id path of
                -- if found var then return it
                Just subId -> VarV subTy subId
                -- if haven't, i.e. id tree is smaller than type tree
                -- try and expand it out using tuple accessors
                Nothing    -> VarV subTy (Lf subId)
                  where exIds = expandIdTreeL id ty
                        msg = "lookupSubVal: can't extend idTree to get id for path " ++ (show path) ++ "\n" ++ (show ty) ++ "\n" ++ (show exIds)
                        subId = fromMaybe (error msg) $ treeLabel $ labelledTreePath exIds path
              where subTy = lookupTreeNode errMsg ty path
            -- types
            TyV ty     -> TyV $ lookupTreeNode errMsg ty path
            other      -> error $ "lookupSubVal: Can't lookup subval of " ++ (show val) 
                           ++ " with tree path " ++ (show path) ++ " (only applicable for vars and types)" ++ errMsg
  where errMsg = errMsg1 ++ "lookupSubVal:"

-- |replaceSubVal path newSubVal oldVal. If newSubVal and oldVal
-- |are values with a tree structures (vals or types), this returns
-- |oldVal with the node at path replaced with newSubVal.
replaceSubVal :: Monad m => TreePath -> Val m -> Val m -> Val m 
replaceSubVal path newVal oldVal = case path of
  -- empty path
  [] -> newVal
  -- non-empty path
  _  -> case (newVal, oldVal) of
          -- vars
          (VarV newTy newId, VarV oldTy oldId) -> VarV resTy resId
            where resTy = replaceTreeNode path newTy oldTy
                  resId = replaceTreeNode path newId oldId
          -- types
          (TyV newTy, TyV oldTy) -> TyV resTy
            where resTy = replaceTreeNode path newTy oldTy
          other -> error $ "replaceSubVal: Can't replace " ++ 
                     (show path) ++ " in " ++ (show oldVal) ++ " with " ++ (show newVal) 

-- |alterSubVal path newSubVal oldVal. Replaces the sub val at path in
-- |oldVal with newSubVal. Throws error if path doesn't exist in oldVal
-- |or if path is non-empty and oldVal is Nothing.
alterSubVal :: Monad m => TreePath -> Val m -> Maybe (Val m) -> Maybe (Val m)
alterSubVal path newSubVal oldVal = case (path, oldVal) of
  ([], _) -> Just newSubVal
  (_, Just oldVal') -> Just $ replaceSubVal path newSubVal oldVal'
  (_, Nothing) -> error $ "alterSubVal: Can't alter the subVal of a Nothing oldVal! At " 
     ++ (show path) ++ " to make it " ++ (show newSubVal)

-- |Values that can be used as Map keys.
data OrdVal = 
    CodeOV Code
  | VarOV Ty IdTree
  | TyOV Ty
  | IdOV Id
  | BoolOV Bool
  | TreeOV (Tree OrdVal)
  | ListOV [OrdVal]
  | LitOV ScalVal
  deriving (Eq, Show, Ord) 

isVarOV (VarOV _ _) = True
isVarOV _ = False

-- |toOrdVal val. Returns the OrdVal version of val, or 
-- |throws an error if val is a graph or function.
toOrdVal :: Monad m => Val m -> OrdVal
toOrdVal val = case val of
  CodeV c -> CodeOV c
  VarV ty idt -> VarOV ty idt
  TyV ty -> TyOV ty
  IdV id -> IdOV id
  BoolV v -> BoolOV v
  TreeV v -> TreeOV $ mapTree toOrdVal v
  ListV l -> ListOV $ map toOrdVal l
  LitV v -> LitOV v
  other -> error $ "toOrdVal: can't convert " ++ (show val) ++ " to an ord val!"

-- |fromOrdVal oval. Returns the Val version of oval.
fromOrdVal :: Monad m => OrdVal -> Val m
fromOrdVal val = case val of
  CodeOV code  -> CodeV code
  VarOV ty idt -> VarV ty idt
  TyOV ty      -> TyV ty
  IdOV idv     -> IdV idv
  BoolOV v     -> BoolV v
  TreeOV v -> TreeV $ mapTree fromOrdVal v
  ListOV l -> ListV $ map fromOrdVal l
  LitOV v -> LitV v

-- |Map from ord values to values
type ValMap m = Map (Tree OrdVal) (Val m)

emptyValMap = Data.Map.empty

-- |The code generator monad state object
data GenState m = GenState {
  genGraphs :: [Graph],             -- graph stack
  genCurrentNode :: NodeId,      -- current node id
  genCurrentInt :: Int,          -- current max numerical index
  genTemEnvs :: NodeEnv (ValEnv m),     -- local vars inside template instances
  genObjMembers :: NodeEnv (ValEnv m),  -- public vars attached to outputs
  genOutBuffs :: Map Id Code,     -- code outputted
  genGlobals :: Map String (ValMap m),   -- global maps
  genDebugOut :: String,          -- debugger output
  genConsts :: GenConsts m        -- constants (types, templates...)
} deriving (Show)

-- |The code generator monad
type GenM m = StateT (GenState m) m ()
type GenM1 m a = StateT (GenState m) m a

-- |A template
type Template m = Ty -> NodeTreeEx -> GenM m
-- |A map of templates for function
type Templates m = Map Id (Template m)

-- |A generator function (generates builtins)
type Generator m = [Val m] -> GenM1 m (Val m)
type Generators m = Map Id (Generator m)

-- |Types, and templates etc
data GenConsts m = GenConsts {
  globTypes :: NodeEnv Ty,
  globTemplates :: Templates m,
  globGenerators :: Generators m,
  globNumTopDims :: Int
}

instance Show (GenConsts m) where
  show glob = "GenConsts {" ++ 
    "\nglobTypes: " ++ (show $ globTypes glob) ++
    "\nglobTemplates: " ++ (show $ Data.Map.keys $ globTemplates glob) ++
    "\nglobNumTopDims: " ++ (show $ globNumTopDims glob) ++
    "\n}\n" 

type TemplateProc m = Tree (Val m) -> GenM m

-- Helper functions
-- -------------------------

-- |getTemplateName. Returns the function name
-- |of the currently 
getTemplateName :: Monad m => GenM1 m Id
getTemplateName = do
  appNodeId <- gets genCurrentNode
  graphs <- gets genGraphs
  -- get app node
  let [appNode] = getNodes ("Back:Gen:getTemplateName:trace: getting app node for nid " ++ 
                            (show appNodeId) {-++ " in graphs:\n" ++ (show graphs) ++ "\n\n\n"-}) graphs [appNodeId]
  case nodeTy appNode of
    AppNd -> do
      -- get the function var node
      let [fvarNodeId, _] = nodeIn appNode
      let [fvarNode] = getNodes ("Back:Gen:getTemplateName:trace: getting fun var node for nid " ++ 
                                 (show fvarNodeId) {-++ " in graphs:\n" ++ (show graphs) ++ "\n\n\n"-}) graphs [fvarNodeId]
      -- get the name of the var node
      let (VarNd temName) = nodeTy fvarNode
      return temName
    other -> error $ "Back:Gen:getTemplateName: current node " ++ (show appNode) ++ " is not an app node."

-- |getTemplateName. Returns the function name
-- |of the currently 
getNodeDesc :: Monad m => NodeId -> GenM1 m Id
getNodeDesc appNodeId = do
  graphs <- gets genGraphs
  -- get app node
  let [appNode] = getNodes ("Back:Gen:getTemplateName:trace: getting app node for nid " ++ 
                            (show appNodeId) {-++ " in graphs:\n" ++ (show graphs) ++ "\n\n\n"-}) graphs [appNodeId]
  case nodeTy appNode of
    AppNd -> do
      -- get the function var node
      let [fvarNodeId, _] = nodeIn appNode
      let [fvarNode] = getNodes ("Back:Gen:getTemplateName:trace: getting fun var node for nid " ++ 
                                 (show fvarNodeId) {-++ " in graphs:\n" ++ (show graphs) ++ "\n\n\n"-}) graphs [fvarNodeId]
      -- get the name of the var node
      let (VarNd temName) = nodeTy fvarNode
      return $ (show appNode) ++ " template=" ++ temName
    other -> return $ (show appNode)

genError :: Monad m => String -> GenM1 m a
genError msg = do
  genTrace msg
  out <- gets genDebugOut
  return $ error out

genTrace :: Monad m => String -> GenM m
genTrace msg = if debug then trace ("genTrace: " ++ msg ++ "\n") $ modify (\st -> st { genDebugOut=(genDebugOut st) ++ "\n" ++ msg } ) else return ()

assertM :: Monad m => (GenM1 m Bool) -> String -> GenM m
assertM check errMsg = do
  result <- check
  temName <- getTemplateName
  nid <- gets genCurrentNode
  case result of
    True  -> return ()
    False -> do
      res <- genError $ temName ++ "(" ++ (show nid) ++ "): " ++ errMsg
      error $ temName ++ "(" ++ (show nid) ++ "): " ++ errMsg

-- |pushGraph graph. Pushes the graph onto the stack
-- |and returns the new stack list.
pushGraph :: Monad m => Graph -> GenM1 m ([Graph])
pushGraph graph = do
  modify (\st -> st { genGraphs=(graph:genGraphs st) } )
  stack <- gets genGraphs
  return stack

-- |popGraph. Removes the head graph off the stack and
-- |returns it.
popGraph :: Monad m => GenM1 m Graph
popGraph = do
  hd <- gets (head . genGraphs)
  modify (\st -> st { genGraphs=(tail $ genGraphs st) } )
  return hd

-- |newInt generates a fresh integer, by incrementing the current int
-- |in the generator monad. 
newInt :: Monad m => GenM1 m Int
newInt = do
  st1 <- get
  let i = genCurrentInt st1
  modify (\st -> st { genCurrentInt=(genCurrentInt st) + 1 } )
  return i

-- |skipInts n. If n is greater than the current int, makes the current 
-- |int n.
skipInts :: Monad m => Int -> GenM m
skipInts skipTo = do
  modify (\st -> st { genCurrentInt=(genCurrentInt st) `max` skipTo } )
  return ()

-- |createNewNodeIds graph. Returns a Map of old node ids
-- |to new node ids for all the node ids in the graph.
createNewNodeIds :: Monad m => Graph -> GenM1 m (IntMap NodeId)
createNewNodeIds graph = do
  -- get max node if
  let maxId = maxNodeId graph
  skipInts (maxId+1)
  curInt <- gets genCurrentInt
  let nodes = graphNodes graph
  -- get current node ids
  let oldNidSet = Data.IntMap.keysSet nodes
  -- (remove any node ids, that are the same as nodes in a parent graph)
  -- actually now checks that there are no nodes with same ids as nodes  
  -- in parent graphs
  gstack <- gets genGraphs
  let parentNidSet = IS.unions $ map (\g -> Data.IntMap.keysSet $ graphNodes g) gstack
  let oldNids = IS.toList $ oldNidSet `IS.difference` parentNidSet
  if (oldNidSet `IS.intersection` parentNidSet) /= IS.empty 
  then error $ "createNewNodeIds: graph includes nodes with name ids as nodes in a parent graph!\n" ++ 
               (show $ oldNidSet `IS.intersection` parentNidSet) ++ "\n" ++ (show graph)
  else return ()
  -- create new node ids for this graph
  newNids1 <- mapM (\oldId -> do newId <- newInt; return (oldId, newId)) $ oldNids
  -- create new nids for nested graphs (in fun nodes)
  -- TODO pass parentNids to nested graphs
  newNids2 <- mapM (\n -> 
          case nodeTy n of
            FunNd {-_-} g -> createNewNodeIds g
            _         -> return Data.IntMap.empty
       ) $ Data.IntMap.elems nodes 
  let newNids = Data.IntMap.unions ((Data.IntMap.fromList newNids1):newNids2)
  -- create identity mappings for all other values
  --let sameNids = Data.IntMap.fromList $ zip [1..curInt] [1..curInt]
  -- return left biased union (all newIds, and sameIds to fill in any gaps)
  return $ newNids --`Data.IntMap.union` sameNids

-- |varToTreeVars varVal. If varVal is a VarV with a tuple of
-- |types and lists, this decomposes that tuple (one level) into a tree of 
-- |var vals.
varToTreeVars :: Monad m => Val m -> Maybe (Tree (Val m))
varToTreeVars var = case var of
  (VarV (Tup tyL) (Tup idL)) | length tyL == length idL -> 
     Just $ Tup $ map (\(ty, id) -> Lf $ VarV ty id) $ zip tyL idL 
  (VarV _ _) -> Nothing
  other      -> error $ "varToTreeVars: can't decompose non VarV vals!\n" ++ (show var)

-- |zipTrees treeA treeB. Assuming treeA is a subset of treeB
-- |returns a new tree with all children in b dangling from those
-- |in a. Throws error otherwise.
zipValTrees :: Monad m => IdTree -> Tree (Val m) -> Tree (Id, Val m)
zipValTrees treeA treeB = case (treeA, treeB) of
  (Lf a, Lf b) -> Lf (a, b)
  (a1 :-> a2, b1 :-> b2) -> (zipValTrees a1 b1) :-> (zipValTrees a2 b2)
  (Tup al, Tup bl) | length al == length bl -> Tup $ map (\(a,b) -> zipValTrees a b) $ zip al bl
  (a, Lf (VarV tyTree idTree)) -> case varToTreeVars (VarV tyTree idTree) of 
    Just decompVar -> zipValTrees a decompVar
    Nothing        -> error $ "zipValTrees: can't zip IdTree with ValTree!\n" ++ (show treeA) ++ "\n" ++ (show treeB)
  other -> error $ "zipValTrees: trees do not align \n" ++ (show treeA) ++ "\n" ++ (show treeB)

-- |expandIdTreeL type idTree. Expands the idTree so it is the
-- |same shape as the type tree, i.e. there is an id label (which may
-- |be a struct reference) for all the original leaf nodes, 
-- |and all nodes below them.
expandIdTreeL :: IdTree -> Ty -> LabelledTree (Maybe Id) (Id)
expandIdTreeL idTree ty = case (idTree, ty) of
  (Lf i, Lf t) -> LLf (Just i) i
  (Lf i, Tup l) -> LTup (Just i) $ map (\(idx,t) -> expandIdTreeL (Lf $ i ++ ".v" ++ (show idx)) t) $ zip [treeIndexBase..] l
  (Tup il, Tup tl) | length il ==  length tl -> LTup Nothing $ map (\(idx, t) -> expandIdTreeL idx t) $ zip il tl
  other -> error $ "expandIdTree: idTree and type tree have incompatible shapes:\n" 
             ++ (show idTree) ++ "\n" ++ (show ty) 

-- |expandIdTree type idTree. Expands the idTree so it is the
-- |same shape as the type tree, i.e. there is an id (which may
-- |be a struct reference) for each leaf type.
expandIdTree :: IdTree -> Ty -> IdTree
expandIdTree idTree ty = fromLabelledTree $ expandIdTreeL idTree ty

-- partitionByTy
partitionByTy :: Monad m => [NodeId] -> GenM1 m [[NodeId]]
partitionByTy nids = do
  -- get types of all nodes if available.
  typeEnv <- gets (globTypes.genConsts)
  let types = map (\nid -> Data.IntMap.findWithDefault nullTy nid typeEnv) nids
  -- partition into those that have stream types,
  -- and those that don't
  let (areStream, notStream) = partition (isStreamTy.snd) $ zip nids types 
  -- return partitioned list of nids
  return [map fst notStream, map fst areStream]
  

