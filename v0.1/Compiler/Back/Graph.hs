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
{-# LANGUAGE ViewPatterns #-}
module Compiler.Back.Graph where

import Compiler.Front.Common (findAndReplaceAll, listGet, imapUnionCheckDisjoint, mapUnionCheckDisjoint, debug, ShowP(..))

import Compiler.Types2.TypeInfo

import Compiler.Back.Helper
import Compiler.Back.Vars
import Compiler.Back.StrTemplates (indentString)

import Data.List (intercalate, intersperse, sort, reverse, elemIndices, isPrefixOf, isInfixOf, nub)
import Data.Map.Strict (Map, fromList)
import qualified Data.Map.Strict as DM
import Data.Set (Set, union)
import qualified Data.Set (insert, member, empty, fromList, toList)
import qualified Data.Set as DS
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as Data.IntMap
import qualified Data.IntMap.Strict as IM
import qualified Data.IntSet
import qualified Data.IntSet as IS
import Data.Maybe (fromMaybe, isJust, fromJust)
import Control.Monad.State.Strict (StateT, get, gets, modify, lift, execStateT)
import Data.Functor.Identity (runIdentity)

-- TODO Change Data.IntMap to DI

import Debug.Trace (trace)

trace' = if debug then trace else \_ -> id

data Tree a = 
    Lf a
  | (Tree a) :-> (Tree a)
  | Tup [Tree a]
  deriving (Eq, Ord)  

-- |treeIndexBase. Index of first element of
-- |a tree tuple.
treeIndexBase = 0

isFunTree :: Tree a -> Bool
isFunTree (a :-> b) = True
isFunTree _ = False

instance Show a => Show (Tree a) where
  show tree = case tree of 
    Lf a -> "(Lf:" ++ (show a) ++ ")"
    a :-> b -> (show a) ++ " -> " ++ (show b)
    Tup l -> "(" ++ (intercalate ", " $ map show l) ++ ")"

showTree :: Show a => Tree a -> String
showTree t = case t of
  Lf a -> "Lf " ++ (show a)
  a :-> b -> (showTree a) ++ " :-> " ++ (showTree b)
  Tup l -> "Tup [" ++ (intercalate ", " $ map showTree l) ++ "]"

{-instance Show a => Show (Tree a) where
  show tree = case tree of
    (Lf a) -> "- " ++ (indentString "  " (show a))
    a :-> b -> "- fun\n" ++ (indentString "  " $ show a) ++ "\n" ++
                          (indentString "  " $ show b)
    Tup l -> "- tup" ++ (concat $ map ((indentString "  ").("\n"++).show) l)-}

-- |flattenTree tree. Flattens tree using a depth first traversal,
-- |returning the list of its leaves. 
flattenTree :: Tree v -> [v]
flattenTree tree = map snd $ flattenLTree $ toLabelledTree tree

-- |treeLeaf takes a tree and if it is a leaf, returns it, or otherwise
-- |throws the error message given.
treeLeaf :: Show a => String -> Tree a -> a
treeLeaf errMsg tree = case tree of
  Lf v -> v
  other -> error $ errMsg ++ "\ntreeLeaf: " ++ (show other) ++ " is not a leaf!\n"

-- |alignTrees treeA treeB aligns treeA and treeB to produce
-- |a mapping from treeA leaves to treeB nodes. If the trees 
-- |don't fit/have the same shape, then an error is thrown.
alignTrees :: Show a => Show b => String -> Tree a -> Tree b -> [(a, Tree b)]
alignTrees errMsg trA trB = treeToList $ zipTrees ("alignTrees;" ++ errMsg) trA trB --case (trA, trB) of
  --(Lf a, b) -> [(a, b)]
  --(a1 :-> a2, b1 :-> b2) -> (alignTrees a1 b2) ++ (alignTrees a2 b2)
  --(Tup al, Tup bl) | length al == length bl -> concat $ map (\(a,b) -> alignTrees a b) $ zip al bl
  --other -> error $ "alignTrees: trees do not align: \n" ++ (show trA) ++ "\n" ++ (show trB)

-- |zipTrees treeA treeB. Assuming treeA is a subset of treeB
-- |returns a new tree with all children in b dangling from those
-- |in a. Throws error otherwise.
zipTrees :: (Show a, Show b) => String -> Tree a -> Tree b -> Tree (a, Tree b)
zipTrees errMsg treeA treeB = case (treeA, treeB) of
  (Lf a, b) -> Lf (a, b)
  (a1 :-> a2, b1 :-> b2) -> (zipTrees errMsg a1 b1) :-> (zipTrees errMsg a2 b2)
  (Tup al, Tup bl) | length al == length bl -> Tup $ map (\(a,b) -> zipTrees errMsg a b) $ zip al bl
  other -> error $ "zipTrees: trees do not align \n" ++ (show treeA) ++ "\n" ++ (show treeB) ++ "\n" ++ errMsg

-- |zipSubTrees treeA treeB. Returns a list of associated subtrees, for e.g.
-- | zipSubTrees (Tup [Tup [Lf a, Lf b], Lf c]) (Tup [Lf x, Tup [Lf y, Lf z]]) = 
-- | [(Tup [Lf a, Lf b], Lf x), (Lf c, Tup [Lf y, Lf z])]. This will fail if two
-- |tuples at the same level have different numbers of children, or if a tuple is
-- |at the same level as a lambda etc.
zipSubTrees :: (Show a, Show b) => Tree a -> Tree b -> [(Tree a, Tree b)]
zipSubTrees treeA treeB = case (treeA, treeB) of
  (a1 :-> b1, a2 :-> b2) -> (zipSubTrees a1 a2) ++ (zipSubTrees b1 b2)
  (Tup l1, Tup l2) | length l1 == length l2 -> concat $ map (\(a,b) -> zipSubTrees a b) $ zip l1 l2
  (Lf a, b) -> [(Lf a, b)]
  (a, Lf b) -> [(a, Lf b)]
  other     -> error $ "zipSubTrees: Can't zip " ++ (show other)

-- |visitTreeM visits the tree using a depth first traversal
-- |and creates a new tree using the monadic function to transform
-- |its leaf values.  
visitTreeM :: Monad m => (a -> m (Tree b)) -> Tree a -> m (Tree b)
visitTreeM f tree = case tree of
  (Lf a)      -> do b <- f a; return b
  (a1 :-> a2) -> do b1 <- (visitTreeM f) a1; b2 <- (visitTreeM f) a2; return $ b1 :-> b2   
  (Tup l)     -> do l' <- mapM (visitTreeM f) l ; return $ Tup l'

-- |mapTree f tree. Returns a tree where all leaf values have been transformed
-- |using f.
visitTree :: (a -> Tree b) -> Tree a -> Tree b
visitTree f tree = runIdentity $ visitTreeM (\a -> return $ f a) tree

-- |mapTree f tree. Returns a tree where all leaf values have been transformed
-- |using f.
mapTree :: (a -> b) -> Tree a -> Tree b
mapTree f tree = runIdentity $ visitTreeM (\a -> return $ Lf $ f a) tree

-- |treeToList takes a tree and returns a list of its elements
-- |created using a depth first traversal
treeToList :: Tree a -> [a]
treeToList tree = case tree of
  (Lf v) -> [v]
  (a :-> b) -> (treeToList a) ++ (treeToList b)
  (Tup l) -> concat $ map treeToList l

type TreePath = [Int]

visitTreeWithPath :: Monad m => (TreePath -> a -> m (Tree b)) -> TreePath -> Tree a -> m (Tree b)
visitTreeWithPath f path tree = case tree of
  (Lf a)      -> do b <- f path a; return b
  (a1 :-> a2) -> do b1 <- (visitTreeWithPath f (0:path)) a1; b2 <- (visitTreeWithPath f (1:path)) a2; return $ b1 :-> b2   
  (Tup l)     -> do l' <- mapM (\(idx,l) -> visitTreeWithPath f (idx:path) l) $ zip [treeIndexBase..] l ; return $ Tup l'

-- |growTree smallTree largeTree  newLeaf. Grows smallTree
-- |to be the same size and shape of largeTree, by creating
-- |new nodes with newLeaf.
growTree :: (Show a, Show b) => String -> (TreePath -> a -> b -> c) -> Tree a -> Tree b -> Tree c
growTree errMsg newLeaf smallTree largeTree = 
    runIdentity $ visitTreeM (\(a, bTr) -> visitTreeWithPath (\p -> \b -> return $ Lf $ newLeaf p a b) [] bTr) zipped
  where zipped = zipTrees errMsg smallTree largeTree

-- |lookupTreeNodeMaybe tree path. Looks up the node at path
-- |in tree, or returns Nothing if doesn't exist.
lookupTreeNodeMaybe :: Show a => Tree a -> TreePath -> Maybe (Tree a)
lookupTreeNodeMaybe tree path = case (path, tree) of
  ([], n) -> Just n 
  (h:r, a :-> b) -> case h of
    0 -> lookupTreeNodeMaybe a r
    1 -> lookupTreeNodeMaybe b r
    o -> error $ "lookupTreeNodeMaybe: Can't access " ++ (show path) ++ " of " ++ (show tree)
  (h:r, Tup l) | h < length l -> lookupTreeNodeMaybe (listGet "Graph:lookupTreeNodeMaybe" l h) r
  other -> Nothing

-- |lookupTreeNode errMsg tree path. Looks up the node at path
-- |in tree, or throws an error if it does not exist.
lookupTreeNode :: Show a => String -> Tree a -> TreePath -> Tree a
lookupTreeNode errMsg tree path = case lookupTreeNodeMaybe tree path of
  Just val -> val
  Nothing  -> error $ errMsg ++ "lookupTreeNode: Can't access " ++ (show path) ++ " of " ++ (show tree)

-- |lookupTreeNodeOrLeaf errMsg tree path. Follows the tree path,
-- |to return either the node at the path, or a leaf, 
-- |whatever comes first. 
lookupTreeNodeOrLeaf :: Show a => String -> Tree a -> TreePath -> Tree a
lookupTreeNodeOrLeaf errMsg tree path = case (path, tree) of
  ([], n) -> n 
  (h:r, a :-> b) -> case h of
    0 -> lookupTreeNodeOrLeaf errMsg a r
    1 -> lookupTreeNodeOrLeaf errMsg b r
    o -> error $ errMsg ++ "lookupTreeNodeOrLeaf: Can't access " ++ (show path) ++ " of " ++ (show tree)
  (h:r, Tup l) | h < length l -> lookupTreeNodeOrLeaf errMsg (listGet "Graph:lookupTreeNodeOrLeaf" l h) r
  (_, Lf v) -> Lf v
  other -> error $ errMsg ++ "lookupTreeNodeOrLeaf: Can't access " ++ (show path) ++ " of " ++ (show tree) 

-- |replaceTreeNode path newNode oldTree. Returns oldTree where the node
-- |at path has been replaced with newNode, or throws error if no such path
-- |exists in oldTree.
replaceTreeNode :: Show a => TreePath -> Tree a -> Tree a -> Tree a
replaceTreeNode path newNode oldTree = case (path, oldTree) of
  ([], n) -> newNode
  (h:r, a :-> b) -> case h of
    0 -> (replaceTreeNode r newNode a) :-> b
    1 -> a :-> (replaceTreeNode r newNode b)
    o -> error $ "replaceTreeNode: Can't access " ++ (show path) ++ " of " ++ (show oldTree)
  (h:r, Tup l) | h < length l -> Tup $ map (\(idx,n) -> 
    if idx == h 
    then replaceTreeNode r newNode n 
    else n) $ zip [treeIndexBase..] l
  other -> error $ "replaceTreeNode: Can't access " ++ (show path) ++ " of " ++ (show oldTree)
   
-- |subPaths pathList pathPrefix. Filters pathList returning only
-- |those for which pathPrefix is a prefix. Note: Here first element
-- |is root of tree.
subPaths :: [(TreePath, a)] -> TreePath -> [(TreePath, a)]
subPaths l prefix = filter (\(p,v) -> isPrefixOf prefix p) l

-- |createTreeFromPaths paths currentPathPrefix. Takes a list of tree paths, with labels and leaves 
-- |and builds them into a labelled tree.Note: head element of paths is root node in tree.
createTreeFromPaths :: Show v => [(TreePath, v)] -> TreePath -> Tree v
createTreeFromPaths l prefix = case subPaths l prefix of
    -- if got to a leaf
    [(path, val)] | prefix == path -> Lf val 
    -- not at a leaf 
    l' | length l' > 0 -> Tup branches
      where idxs = sort $ nub $ map (head.fst) l'
            mx = (length idxs) - 1
            idxs' = if idxs == [0..mx] then idxs else error $ "createTreeFromPaths: paths missing: " ++ (show prefix) ++ "\n" ++ (show l')
            branches = map (createTreeFromPaths l') $ map (\i -> prefix++[i]) idxs' 
    -- anything else 
    l' -> error $ "createTreeFromPaths: invalid path list: " ++ (show prefix) ++ "\n" ++ (show l')

-- |searchTree searchFun tree. Visits all leaves
-- |returning a list of values generated by the searchFun.
searchTree :: (a -> [b]) -> Tree a -> [b]
searchTree f tree = case tree of
  Lf a -> f a
  Tup l -> concat $ map (searchTree f) l  
  a :-> b -> (searchTree f a) ++ (searchTree f b)

-- |filterTree pred tree. Accumulates all leaf values for which the
-- |predicate pred holds.
filterTree :: (a -> Bool) -> Tree a -> [a]
filterTree pred tree = runIdentity (execStateT (visitTreeM (\val -> if pred val then (do modify (\l -> val:l); return $ Lf val) else (return $ Lf val)) tree) [])

-- |treeContains pred tree. Returns true if tree contains
-- |a leaf for which the predicate pred holds.
treeContains :: (a -> Bool) -> Tree a -> Bool
treeContains pred tree = case filterTree pred tree of
  [] -> False
  _  -> True

-- |tidyTree tree. Pulls up tuples of length 1.
tidyTree :: Tree a -> Tree a
tidyTree t = case t of
  Tup [Tup l]  -> Tup $ map tidyTree l
  (a :-> b) -> (tidyTree a) :-> (tidyTree b)
  Lf a -> Lf a

-- |LabelledTree l v - a tree where every node has a label
data LabelledTree l v = 
    LLf l v
  | LFun l (LabelledTree l v) (LabelledTree l v)
  | LTup l [LabelledTree l v]
  deriving (Eq)

-- |Show instance for labelled trees
{-instance (Show a, Show l) => Show (LabelledTree l a) where
  show tree = case tree of 
    LLf l a -> "LLf:" ++ (show a) ++ "[" ++ (show l) ++ "]"
    LFun l a b -> (show a) ++ " ->[" ++ (show l) ++ "] " ++ (show b)
    LTup lb l -> "LTup" ++ (show $ length l) ++ ": (" ++ (intercalate ", " $ map show l) ++ ")[" ++ (show lb) ++ "]"-}

instance (Show a, Show l) => Show (LabelledTree l a) where
  show tree = case tree of
    (LLf l a) -> "- " ++ (show l) ++ ": " ++ (indentString "  " (show a))
    LFun l a b -> "- fun\n" ++ (indentString "  " $ show a) ++ "\n" ++
                          (indentString "  " $ show b)
    LTup lb l -> "- tup" ++ (concat $ map ((indentString "  ").("\n"++).show) l)

-- |flattenLTree tree. Flattens tree using a depth first
-- |traversal, returning a list of its leaves and their labels.
flattenLTree :: LabelledTree l v -> [(l, v)]
flattenLTree tree = case tree of
  LLf l v ->    [(l,v)]
  LFun l a b -> (flattenLTree a) ++ (flattenLTree b)
  LTup l lst -> concat $ map flattenLTree lst

-- |treeLabel tree. Returns the label of a labelled tree. 
treeLabel :: Show l => Show v => LabelledTree l v -> l
treeLabel tree = case tree of
  (LLf l _)    -> l
  (LFun l _ _) -> l
  --_ :--> _     -> error $ "treeLabel: funs don't have labels!\n" ++ (show tree)
  (LTup l _)   -> l

-- |labelledTreePath tree path. Looks up the node at path
-- |in tree, or throws an error if it does not exist.
labelledTreePath :: (Show a, Show b) => LabelledTree a b -> TreePath -> LabelledTree a b
labelledTreePath tree path = case (path, tree) of
  ([], n) -> n 
  (h:r, LFun _ a b) -> case h of
    0 -> labelledTreePath a r
    1 -> labelledTreePath b r
    o -> error $ "labelledTreePath: Can't access " ++ (show path) ++ " of " ++ (show tree)
  (h:r, LTup _ l) | h < length l -> labelledTreePath (listGet "Graph:labelledTreePath" l h) r
  other -> error $ "labelledTreePath: Can't access " ++ (show path) ++ " of " ++ (show tree)

-- |zipLabelledTrees treeA treeB. Assuming treeA is a subset of treeB
-- |returns a new tree with all children in b dangling from those
-- |in a. Throws error otherwise. Keeps labels from treeA.
zipLabelledTrees :: (Show l1, Show l2, Show v1, Show v2) => 
  LabelledTree l1 v1 -> LabelledTree l2 v2 -> LabelledTree l1 (v1, LabelledTree l2 v2)
zipLabelledTrees treeA treeB = case (treeA, treeB) of
  (LLf l a, b) -> LLf l (a, b)
  (LFun la a1 a2, LFun lb b1 b2) -> LFun la (zipLabelledTrees a1 b1) (zipLabelledTrees a2 b2)
  (LTup l1 al, LTup l2 bl) | length al == length bl -> LTup l1 $ map (\(a,b) -> zipLabelledTrees a b) $ zip al bl
  other -> error $ "zipLabelledTrees: trees do not align \ntreeA: " ++ (show treeA) ++ "\ntreeB: " ++ (show treeB)

-- |toLabelledTree tree. Converts a tree to a labelled tree.
toLabelledTree :: Tree a -> LabelledTree () a
toLabelledTree tree = case tree of
  Lf a    -> LLf () a
  Tup l   -> LTup () $ map toLabelledTree l
  a :-> b -> LFun () (toLabelledTree a) (toLabelledTree b)

-- |Converts from a labelled tree back to a normal
-- |tree, disgarding the labels.
fromLabelledTree :: LabelledTree a b -> Tree b
fromLabelledTree tree = case tree of
  LLf _ b -> Lf b  
  LTup _ l  -> Tup $ map fromLabelledTree l
  LFun _ a b -> (fromLabelledTree a) :-> (fromLabelledTree b) 

-- |visitLabelledTreeM visits the tree using a depth first traversal
-- |and creates a new tree using the monadic function to transform
-- |its leaf values.  
visitLabelledTreeM :: Monad m => (l -> a -> m (LabelledTree l b)) -> LabelledTree l a -> m (LabelledTree l b)
visitLabelledTreeM f tree = case tree of
  (LLf n a)    -> do b <- f n a; return b
  (LFun l a1 a2) -> do b1 <- (visitLabelledTreeM f) a1; b2 <- (visitLabelledTreeM f) a2; return $ LFun l b1 b2   
  (LTup n l)   -> do l' <- mapM (visitLabelledTreeM f) l ; return $ LTup n l'

-- |mapLabels f tree. Natural transformation of labelled tree labels.
mapLabels :: (l1 -> a -> b) -> (l1 -> l2) -> LabelledTree l1 a -> LabelledTree l2 b
mapLabels f g tree = case tree of
  LLf l1 v    -> LLf (g l1) (f l1 v)
  LTup l1 lst -> LTup (g l1) $ map (mapLabels f g) lst
  LFun l a b    -> LFun (g l) (mapLabels f g a) (mapLabels f g b)

-- |createTreePathTree rootPath tree. Returns a tree with labels that are 
-- |tree paths for each node.
createTreePathTree :: TreePath -> LabelledTree a b -> LabelledTree TreePath ()
createTreePathTree path tree = case tree of
  LLf _ _  -> LLf path ()
  LTup _ l -> LTup path $ map (\(idx, child) -> createTreePathTree (idx:path) child) $ zip [treeIndexBase..] l
  LFun _ a b -> LFun path (createTreePathTree (treeIndexBase:path) a) (createTreePathTree ((treeIndexBase+1):path) b)

-- |Contains vars instance for Tree
{-instance ContainsVars a => ContainsVars (Tree a) where
  visitVars f tree = case tree of
    (Lf a) -> do
      a' <- visitVars f a
      return $ Lf a'
    (a :-> b) -> do
      a' <- visitVars f a
      b' <- visitVars f b
      return (a' :-> b')
    (Tup l) -> do
      l' <- mapM (visitVars f) l
      return (Tup l')
  createVar name = Lf $ createVar ((createVar name) :: a)-}

-- |Data types
data LfTy = 
    IntTy
  | NullTy
  | VarTy String
  | ListTy Ty
  | StrmTy Ty
  | IterTy Ty
  | OMapTy Ty Ty
  | HMapTy Ty Ty
  | LfTy String [Ty]
  | FunTy Graph
  deriving (Eq, Ord)

type Ty = Tree LfTy

-- |Contains vars instance for LfTy
{-instance ContainsVars LfTy where
  visitVars f ty = case ty of
    VarTy vname -> do
      ty' <- f vname
      return ()
    other -> return () -}

type TyScheme = Scheme Ty

instance Show LfTy where
  show t = case t of 
    IntTy -> "Int"
    NullTy -> "Null"
    VarTy name -> name
    ListTy e -> "List " ++ (show e)
    StrmTy e -> "Stream " ++ (show e)
    IterTy e -> "Iter " ++ (show e)
    OMapTy k v -> "OMap " ++ (show k) ++ " " ++ (show v)
    HMapTy k v -> "HMap " ++ (show k) ++ " " ++ (show v)
    LfTy name l -> "(" ++ (name) ++ " " ++ (concat $ map show l) ++ ")"
    FunTy g -> "FunTy:(" ++ (show $ graphName g) ++ ")"

funTy :: Graph -> Ty
funTy g = Lf $ FunTy g

-- lfTy tyName tyArgs. Shorthand for creating leaf types.
lfTy :: String -> [Ty] -> Tree LfTy
lfTy n l = Lf $ LfTy n l

listTy et = Lf $ ListTy et
iterTy ct = lfTy "Iter" [ct]
idxIterTy ct = lfTy "IdxIter" [ct]
intTy = lfTy "Int" []
uintTy = lfTy "UInt" []
floatTy = lfTy "Float" []
boolTy = lfTy "Bool" []
strTy = lfTy "String" []
nullTy = lfTy "Null" []
mpiTyTy = lfTy "MPIType" []
--unknownFunTy = lfTy "UnknownFun" [] -- use nullTy for now

isStreamTy :: Ty -> Bool
isStreamTy (Lf (LfTy name l)) = trace' ("isStreamTy " ++ name ++ (show l) ++ " = " ++ (show stmModeOn) ++ "\n") $ (isInfixOf "Stream" name) || stmModeOn
  where modePosL = map fst $ typeModes name
        modes = map (\i -> (listGet "Graph:isStreamTy" l i) == (lfTy "Stm" [])) modePosL
        stmModeOn = or modes
isStreamTy (Lf (StrmTy _)) = True
isStreamTy _ = False

-- |isScalTy type. Returns if type is a 
-- |scalar type.
isScalTy :: Ty -> Bool
isScalTy ty = case ty of
  _ | ty == intTy   -> True
  _ | ty == floatTy -> True
  _ | ty == boolTy  -> True
  _ | ty == strTy   -> True
  _ | ty == nullTy  -> True
  _ -> False

getVarsInTy :: Ty -> DS.Set String
getVarsInTy ty = DS.unions $ map getVarsInLfTy $ treeToList ty

-- |getVarTys lfTy. Returns the set of var ids in a leaf type.
getVarsInLfTy :: LfTy -> DS.Set String
getVarsInLfTy (VarTy vid) = DS.singleton vid
getVarsInLfTy (LfTy n l) = DS.unions $ map getVarsInTy l

-- |mapGraphsInTy f ty. Applies f to all graphs in ty.
mapGraphsInTyM :: Monad m => (Graph -> m Graph) -> Ty -> m Ty
mapGraphsInTyM f ty = case ty of
  Tup l -> do
    l' <- mapM (mapGraphsInTyM f) l
    return $ Tup l'
  (a :-> b) -> do
    a' <- mapGraphsInTyM f a
    b' <- mapGraphsInTyM f b
    return (a' :-> b')
  Lf lf -> case lf of
    (LfTy name l) -> do
      l' <- mapM (mapGraphsInTyM f) l
      return $ Lf $ LfTy name l'
    (FunTy graph) -> do
      graph' <- f graph
      return $ Lf $ FunTy graph' 
    other -> return ty

-- |mapGraphsInTy f ty. Applies f to all graphs in ty.
mapGraphsInTy :: (Graph -> Graph) -> Ty -> Ty
mapGraphsInTy f ty = runIdentity $ mapGraphsInTyM (\g -> return $ f g) ty

-- |returns list of all graphs in this type.
getGraphsInTy :: Ty -> [Graph]
getGraphsInTy ty = runIdentity $ execStateT (mapGraphsInTyM (\g -> do modify (\l -> g:l) ; return g) ty) []

data IgnoreFunsTy = 
   IgnoreFunsLfTy LfTy
 | IgnoreFunsTy Ty

instance Eq IgnoreFunsTy where
  a == b = case (a,b) of
    -- compare leaf types
    (IgnoreFunsLfTy (FunTy g1), IgnoreFunsLfTy (FunTy g2)) -> True -- don't compare graphs!
    (IgnoreFunsLfTy (LfTy n1 l1), IgnoreFunsLfTy (LfTy n2 l2)) -> 
      (n1 == n2) && (length l1 == length l2) && (and $ map (\(x,y)->(IgnoreFunsTy x == IgnoreFunsTy y)) $ zip l1 l2)
    (IgnoreFunsLfTy x, IgnoreFunsLfTy y) -> x == y
    -- compare tuple and fun types
    (IgnoreFunsTy (Tup l1), IgnoreFunsTy (Tup l2)) -> (length l1 == length l2) && (and $ map (\(x,y)->(IgnoreFunsTy x == IgnoreFunsTy y)) $ zip l1 l2)
    (IgnoreFunsTy (x1 :-> y1), IgnoreFunsTy (x2 :-> y2)) -> (IgnoreFunsTy x1 == IgnoreFunsTy x2) && (IgnoreFunsTy y1 == IgnoreFunsTy y2)
    (IgnoreFunsTy (Lf x), IgnoreFunsTy (Lf y)) -> (IgnoreFunsLfTy x == IgnoreFunsLfTy y)
    _ -> False

ignoreFunsTy :: Ty -> IgnoreFunsTy
ignoreFunsTy t = IgnoreFunsTy t

-- |Scalar literals
data ScalVal =
    IntVal Int
  | UIntVal Int
  | FltVal Float
  | StrVal String
  | BolVal Bool
  | NulVal
  deriving (Eq, Ord)

instance Show ScalVal where
  show v = case v of
    IntVal v -> show v
    UIntVal v -> show v
    FltVal f -> show f
    StrVal s -> "\"" ++ (show s) ++ "\""
    BolVal b -> if b then "true" else "false"
    NulVal   -> "NULL"

-- |scalValType val. Returns the type of this literal value.
scalValType :: ScalVal -> Ty
scalValType val = case val of
  IntVal _ -> intTy
  UIntVal _ -> uintTy
  FltVal _ -> floatTy
  StrVal _ -> strTy
  BolVal _ -> boolTy
  NulVal   -> nullTy

-- |Node ids
type NodeId = Int

-- |Node types
data NodeTy = 
    VarNd String
  | GlobalVarNd Ty String
  | FunNd {-NodeId-} Graph
  | AppNd
  | LitNd ScalVal
  | TupNd 
  | TupAccNd Int
  | LstNd 
  deriving (Eq, Ord)

instance Show NodeTy where
  show n = case n of 
    VarNd s -> "varNode:" ++ s
    GlobalVarNd ty id -> "globalVarNd(" ++ id ++ " :: " ++ (show ty) ++ ")"
    FunNd g -> "funNode:" ++ (graphName g) -- ++ " = " ++ (show g)
    AppNd   -> "appNode"
    LitNd v -> "litNode:" ++ (show v)
    TupNd   -> "tupNode"
    TupAccNd idx -> "tupAcc:" ++ (show idx)
    LstNd   -> "lstNode"

isFunNd :: NodeTy -> Bool
isFunNd (FunNd _) = True
isFunNd _ = False

isVarNd :: NodeTy -> Bool
isVarNd (VarNd _) = True
isVarNd _ = False

isTupAcc :: NodeTy -> Bool
isTupAcc ty = case ty of
  TupAccNd _ -> True
  _          -> False

getFunNdGraph :: Node -> Graph
getFunNdGraph node = case nodeTy node of 
  FunNd g -> g
  _ -> error $ "getFunNdGraph: can't return graph from non FunNd node: " 
                 ++ (show node)

getTupAccIdx :: Node -> Int
getTupAccIdx node = case nodeTy node of
  TupAccNd idx -> idx
  other        -> error $ "getTupAccIdx: node is not a tuple accessor:\n" ++ (show node) 

getVarNodeName :: Node -> String
getVarNodeName node = case nodeTy node of
  VarNd n -> n
  _       -> error $ "getVarNodeName: node is not a var node:\n" ++ (show node)

-- |DFG nodes
data Node = Node {
    nodeId :: NodeId,
    nodeIn :: [NodeId],
    nodeOut :: [NodeId],
    nodeTy :: NodeTy
  } deriving (Eq, Ord)

instance Show Node where
  show n = "(N" ++ (show $ nodeId n) ++ " " ++ (show $ nodeIn n) ++ " " ++ (show $ nodeOut n) ++ " " ++ (show $ nodeTy n) ++ ")"

-- |Map from node ids to objects
type NodeEnv a = IntMap a

emptyNodeEnv = Data.IntMap.empty

-- |looks up a member from a node environment or throws an
-- |error with the given message
lookupNode :: Show a => String -> NodeId -> NodeEnv a -> a
lookupNode errMsg nid env = fromMaybe 
  (error (errMsg ++ "\nlookupNode: node " ++ (show nid) ++ " is not in the env:\n" ++ (show env))) 
  $ Data.IntMap.lookup nid env

-- |lookupNodeMaybe nodeId nodeEnv. Looks up the node, or
-- |returns Nothing if it could not be found.
lookupNodeMaybe = Data.IntMap.lookup

-- |duplicateNodeEnvIds newIds oldEnv. Duplicates all entries in oldEnv
-- |that exist in newIds, giving them the new ids defined in newIds, and then
-- |returns all the original entries, and these new duplicated ones. 
duplicateNodeEnvIds :: Show a => NodeEnv NodeId -> NodeEnv a -> NodeEnv a
duplicateNodeEnvIds newIds oldEnv = 
    -- check domain of oldEnv and codomain of newIds are disjoint
    case Data.IntSet.null overlap of
      -- are not disjoint
      False -> error $ "duplicateNodeEnvIds: newIds maps to some old ids!\nnewIds: " ++ (show newIds) ++ "\noldEnv: " ++ (show oldEnv) ++ "\noverlap: " ++ (show overlap) 
      -- are disjoint
      True -> resEnv 
        where -- translate nodeIds in oldEnv using newIds, to give newEnv
              newEnv = Data.IntMap.mapKeys (\oldNid -> fromMaybe oldNid $ Data.IntMap.lookup oldNid newIds) oldEnv
              -- union oldEnv together with newEnv
              resEnv = newEnv `Data.IntMap.union` oldEnv
  where overlap = (Data.IntMap.keysSet oldEnv) `Data.IntSet.intersection` (Data.IntSet.fromList $ Data.IntMap.elems newIds)

type NodeTree = LabelledTree NodeId () --Tree NodeId

-- |buildNodeTree graph nodeId type. Takes a graph and a node, and returns a 
-- |node tree of all its neighbours node ids. However this tree now also contains
-- |leaves that access tuple values within a given node, which are identified 
-- |by treepaths.
buildNodeTree :: [Graph] -> NodeId -> Ty -> NodeTreeEx
buildNodeTree graphs@(graph:tail) nid ty = case nodeTy node of
    AppNd -> exNodeTree
      where [funId, inId] = nodeIn node
            [inNode] = getNodes "buildNodeTree" graphs [inId] 
            nodeTree = LFun funId (buildInputNodeTree graphs inNode) (buildOutputNodeTree graphs node)
            exNodeTree = extendNodeTreeWithType nodeTree ty
    other -> error $ "buildNodeTree: should only be called at function applictions:\n" ++ (show node)
  where --nodes = graphNodes graph
        --node  = lookupNode "buildNodeTree" nid nodes
        node = fromMaybe (error $ "\nbuildNodeTree: node " ++ (show nid) ++ " not in graph: " ++ (show graph)) $ lookupGraphNodeMaybe "buildNodeTree" nid graphs

-- |buildInputNodeTree graph node. Builds a node tree from the input nodes
-- |of a node. 
buildInputNodeTree :: [Graph] -> Node -> NodeTree
buildInputNodeTree graphs node = case nodeTy node of
    TupNd -> if nodeTreeList == [] then LLf nid () else LTup nid nodeTreeList
      where idList = nodeIn node
            nodeTreeList = map (buildInputNodeTree graphs) $ getNodes "buildInputNodeTree(TupNd):" graphs idList
    -- _ -> LLf nid ()
    _ -> LLf (nodeId srcNode) ()
      where srcNode = getInputNodeBeforeTuple graphs node
  where nid = nodeId node 

-- TODO make so works for arbitrary chains of TupNd and TupAccNds...
-- |If node is a TupAccNode and it's input is a TupNd, shortcuts them
-- |to immediately get the original node. 
getInputNodeBeforeTuple :: [Graph] -> Node -> Node
getInputNodeBeforeTuple graphs node0 = case nodeTy node0 of
  (TupAccNd idx) -> case nodeTy node1 of
      TupNd -> getInputNodeBeforeTuple graphs node2
        where nidList = nodeIn node1
              nid2 = if idx >= length nidList then error $ "Graph:getInNodeBefTup: invalid tup acc node!" else nidList !! idx
              [node2] =  getNodes "getInputNodeBeforeTuple(Original):" graphs [nid2]
      other -> node0
    where [nid1] = nodeIn node0
          [node1] = getNodes "getInputNodeBeforeTuple(TupNd):" graphs [nid1]
  other -> node0

-- |buildOutputNodeTree takes a node, and looks through all its outputs
-- |for tuple accessors, creating a labelled tree of output nodes. 
buildOutputNodeTree :: [Graph] -> Node -> NodeTree
buildOutputNodeTree graphs thisNode = if outTreeList == [] then LLf thisNodeId () else LTup thisNodeId outTreeList 
  where -- get this node id
        thisNodeId = nodeId thisNode
        -- get output nodes
        nodes = getNodes "buildOutputNodeTree" graphs $ nodeOut thisNode
        -- keep only tuple accessors
        tupAccNodes = filter (isTupAcc . nodeTy) nodes
        -- sort them by their tuple access index
        outList = sortWith getTupAccIdx tupAccNodes
        -- check none are missing!
        checkList = zip [0..] outList
        outList2 = map (\(i1,n) -> if i1 == getTupAccIdx n 
          then n 
          else error $ "buildOutputNodeTree: tuple acc wrong index! one missing, or duplicate?\n" ++ (show checkList)) checkList
        -- call recursively and combine them
        outTreeList = map (buildOutputNodeTree graphs) outList

-- |Returns all graphs in a type env.
getGraphsInTys :: NodeEnv Ty -> [Graph]
getGraphsInTys env = Data.IntMap.foldl (++) [] $ Data.IntMap.map getGraphsInTy env 

type NodeTreeEx = LabelledTree (NodeId, TreePath) ()

emptyNodeTreeEx = LLf (-1 :: Int, []) ()

-- |extendTyTree nodeId typeTree. Converts type tree into a tree of labels
-- |for paths into it.
extendTyTree :: v1 -> LabelledTree v2 v3 -> LabelledTree (v1, TreePath) ()
extendTyTree v tree = exTree
  where tuplePaths = createTreePathTree [] tree
        exTree = mapLabels (\_ -> \_ -> ()) (\p -> (v, p)) tuplePaths
  
-- |extendNodeTreeWithType tree type. Align tree with the 
-- |type and expand any leaves of tree that have tuple type
-- |to provide leaves to access each of the tuple parts.
extendNodeTreeWithType :: NodeTree -> Ty -> NodeTreeEx
extendNodeTreeWithType tree ty = exTree'
  where labelledTy = toLabelledTree ty
        zipped = zipLabelledTrees tree labelledTy
        exTree = mapLabels (\nid -> \(_,lty) -> extendTyTree nid lty) (\nid -> (nid, [])) zipped
        exTree' = runIdentity $ visitLabelledTreeM (\lbl -> \val -> return val) exTree

data Graph = Graph {
  graphNodes :: NodeEnv Node,
  graphVars :: Map String NodeId, -- maps var names to node ids
  --graphTypes :: Map NodeId Ty,
  graphIn :: NodeId,
  graphOut :: NodeId
} deriving (Eq, Ord)

instance Show Graph where
  show g = "-- " ++ (graphName g) ++ "\n" ++
      "Graph {\n" ++ 
      "graphIn=" ++ (show $ graphIn g) ++ "\n" ++
      "graphOut=" ++ (show $ graphOut g) ++ "\n" ++ 
      "graphNodes=\n" ++ (concat $ intersperse ",\n" $ map show $ Data.IntMap.toList ns) ++ 
      "graphVars=\n" ++ (concat $ intersperse ",\n" $ map show $ DM.toList vs) ++ "\n}\n"
    where ns = graphNodes g
          vs = graphVars g

graphName :: Graph -> String
graphName g = "g" ++ st ++ "to" ++ end
  where st = findAndReplaceAll (=='-') 'M' $ show $ graphIn g
        end = findAndReplaceAll (=='-') 'M' $ show $ graphOut g

-- |showSubgraphs g. Shows g and all the subgraphs nested in FunNds.
showSubgraphs :: Graph -> String
showSubgraphs g = (show g) ++ (concat $ map showSubgraphs funNodeL)
  where funNodes = Data.IntMap.filter (isFunNd.nodeTy) (graphNodes g)
        funNodeL = map (getFunNdGraph.snd) $ Data.IntMap.toList funNodes

--instance Show Graph where
--  show (Graph d a b c) = (show a) ++ (show b)  ++ (show c) ++ (show $ Data.IntMap.keys d) ++ (show $ Data.IntMap.elems d) ++ (concat $ [(show $ d Data.IntMap.! k) | k <- --Data.IntMap.keys d, k < 5])

-- |newGraph creates a new graph from a list of nodes
newGraph :: [Node] -> NodeId -> NodeId -> Map String NodeId -> Graph
newGraph l inid outnid vars = Graph {
  graphNodes=Data.IntMap.fromList $ map (\n -> (nodeId n, n)) l,
  graphIn=inid,
  graphOut=outnid,
  graphVars=vars
}

-- |Sequentially compose graphs so g2 is applied after g1.
seqComposeGraphs :: Graph -> Graph -> Graph
seqComposeGraphs g1 g2 = Graph {
    graphIn=graphIn g1,
    graphOut=graphOut g2,
    graphNodes=nodes',
    graphVars=mapUnionCheckDisjoint "Graph:seqComposeGraphs:graphVars:" (graphVars g1) (graphVars g2) 
  }
  where g1Out = graphOut g1
        g2InVar = graphIn g2
        g2InNode = lookupNode "seqComposeGraphs" g2InVar (graphNodes g2)
        g2InNids = nodeOut g2InNode
        nodes = (graphNodes g1) `Data.IntMap.union` (graphNodes g2)
        nodes' = Data.IntMap.mapWithKey (\k -> \n -> case k of
          _ | k == g1Out      -> n { nodeOut=g2InNids }
          _ | elem k g2InNids -> n { nodeIn=map (\nid -> if nid == g2InVar then g1Out else nid) $ nodeIn n } 
          _     -> n) nodes

-- |graphsContain graph nodeId. Returns true if one of the graphs
-- |contains a node with id nodeId.
graphsContain :: [Graph] -> NodeId -> Bool
graphsContain [] _ = False
graphsContain (hd:tail) nid = (Data.IntMap.member nid (graphNodes hd)) || (graphsContain tail nid)

-- |findInGraph nodeTy graph. Searches graph for 
-- |nodes with nodeTy and returns a list of all the nodes
-- |that do.
findInGraph :: (Node -> Bool) -> Graph -> [Node]
findInGraph pred graph = l' ++ l''
  where l = Data.IntMap.elems $ graphNodes graph
        l' = filter pred l
        funs = filter (isFunNd.nodeTy) l
        l'' = concat $ map (\n -> let (FunNd g) = nodeTy n 
                 in findInGraph pred g) funs

-- |lookupGraphNodeMaybe nid graph. Searches up graphs,
-- |checking the current graph, and if it doesn't contain it
-- |checking it's parent.
lookupGraphNodeMaybe :: String -> NodeId -> [Graph] -> Maybe Node
lookupGraphNodeMaybe callId nid graphs@(graph:tail) = case lookupNodeMaybe (trace' msg nid) thisEnv of
    Just node -> Just $ lookupGraphVarNode msg node graphs graphs --Just node
    Nothing   -> case tail of
      []     -> Nothing
      parent -> lookupGraphNodeMaybe (callId ++ ":lkpGraphNdMaybe(recur)") nid parent
  where thisEnv = graphNodes graph
        msg = callId ++ ":lkpGraphNdMaybe: " ++ (show nid)

-- |lookupGraphVarNode msg node allGraphs graphs. If node is a varNode called
-- |something other than "in" or "out", then this function searches up the
-- |graph stack for a node bound to that name. If one exists, it then searches
-- |from the leaf graph up to the root again (using allGraphs) to find this node,
-- |returning it if it is found, or throwing an error otherwise.
lookupGraphVarNode :: String -> Node -> [Graph] -> [Graph] -> Node
lookupGraphVarNode msg node allGraphs [] = node -- no graphs, return node
lookupGraphVarNode msg node@(nodeTy -> VarNd vname) allGraphs graphs@(graph:tail) = case DM.lookup vname (graphVars graph) of
    -- node id for this var found, so return the node
    Just nid -> if nid == nodeId node then error $ "Graph:lookupGraphVarNode: cycle! " ++ (show node) else case lookupGraphNodeMaybe msg' nid allGraphs of
      -- found node
      Just srcNode -> error $ "Graph:lookupGraphVarNode: found node for var " ++ (show node) ++ "; = " ++ (show srcNode)  --srcNode
      -- can't find node for this var
      Nothing      -> error $ "Graph:lookupGraphVarNode: can't find node " ++ (show nid) ++ " for var " ++ (show node) ++ ".\n" ++ (show allGraphs)
    -- try parent graph
    Nothing  -> lookupGraphVarNode msg node allGraphs tail
  where msg' = msg ++ ":lkpGraphVarNode: " ++ (show $ nodeId node)
lookupGraphVarNode msg node allGraphs (graph:tail) = node -- node is non-var, return node
        
lookupGraphNode :: String -> NodeId -> [Graph] -> Node
lookupGraphNode errMsg nid graphs = case lookupGraphNodeMaybe (errMsg++":lookupGraphNode") nid graphs of
  Just node -> node
  Nothing   -> error $ errMsg ++ "\nlookupGraphNode: node " ++ (show nid) ++ " is not in graph:\n" ++ (show graphs)

-- |lookupNodeLeafGraph errMsg nid graph. If in leaf graph, returns it.
-- |If in parent graphs, returns Nothing. If in none of them, throws error.
lookupNodeLeafGraph :: String -> NodeId -> [Graph] -> Maybe Node
lookupNodeLeafGraph errMsg nid graphs@(graph:tail) = case lookupNodeMaybe nid thisEnv of
    Just node -> Just node
    Nothing   -> case lookupGraphNodeMaybe (errMsg++":lookupNodeLeafGraph") nid graphs of
      Just node -> Nothing
      Nothing   -> error $ errMsg ++ "\nlookupNodeLeafGraph: node " ++ (show nid) ++ " is not in graph or parents:\n" ++ (show graph)
  where thisEnv = graphNodes graph

-- |maxNodeId graph. Finds the maximum node id
-- |in the graph, grahp's parents, and all fun nodes of that graph.
maxNodeId :: Graph -> NodeId
maxNodeId graph = maximum $ 0:(nids1 ++ nids2)
  where nodes = graphNodes graph
        nids1 = Data.IntMap.keys nodes
        nids2 = map (\n -> 
          case nodeTy n of
            FunNd {-_-} g -> maxNodeId g
            _         -> 1
         ) $ Data.IntMap.elems nodes 

-- |replaceNodeIds newNidMap graph. Returns a copy of the graph,
-- |with the node ids replaced with the new ones in newNidMap.
replaceNodeIds :: IntMap NodeId -> Graph -> Graph
replaceNodeIds newNidMap graph = Graph {graphIn=newIn, graphOut=newOut, graphNodes=nodes'', graphVars=vars'}
  -- nolonger raises error if node id is not in replacement map, and just leaves it the same
  -- i.e. useful for when graphs reference nodes in parent graphs
  -- fromMaybe (error $ "dupGraph: new nid for " ++ (show oldId) ++ " not found!\n" ++ (show newNidMap)
  where newNidFun = (\oldId -> fromMaybe oldId $ Data.IntMap.lookup oldId newNidMap)
        -- replace old ids with new ones
        out = graphOut graph
        inn = graphIn graph
        nodes = graphNodes graph
        newOut = newNidFun out
        newIn = newNidFun inn
        -- (change all nodes)
        nodes' = Data.IntMap.map (\n -> n { 
          nodeId=newNidFun (nodeId n),
          nodeIn=map newNidFun (nodeIn n),
          nodeOut=map newNidFun (nodeOut n), 
          nodeTy=case nodeTy n of
            FunNd {-i-} g -> FunNd {-i-} $ replaceNodeIds newNidMap g
            other     -> other}) nodes
        -- (change all node keys)
        nodes'' = Data.IntMap.mapKeys newNidFun nodes'
        -- (change var node ids) 
        vars' = DM.map newNidFun $ graphVars graph

-- |removeParentNodes parNodes graph. Removes all nodes with 
-- |id's that exist in parNodes from graph. Also removes all
-- |nodes with ids in parNodes or graph, from all graphs nested
-- |in FunNd in graph.
removeParentNodes :: IM.IntMap Node -> Graph -> Graph
removeParentNodes parNids g0 = g1 { graphNodes=nodes' }
  where -- check that nodes to remove are vars
        remNodes = (graphNodes g0) `IM.intersection` parNids
        remNodeNotVars = IM.filter (not . isVarNd . nodeTy) remNodes
        g0Nodes = if remNodeNotVars /= IM.empty
          then error $ "Graph:removeParentNodes: removing non-var nodes!\n" ++ (show remNodeNotVars) 
          else graphNodes g0
        -- remove nodes from this graph
        g1 = g0 { graphNodes=g0Nodes `IM.difference` parNids }
        -- add this graph's nodes to parNids
        parNids' = parNids `IM.union` (graphNodes g1)
        -- remove these nids from all nested graphs (in fun nodes)
        nodes' = Data.IntMap.map (\n -> n {  
          nodeTy=case nodeTy n of
            FunNd g -> FunNd $ removeParentNodes (parNids') g
            other     -> other}) $ graphNodes g1

-- |gets the nodes from node ids for a given graph
getNodes :: String -> [Graph] -> [NodeId] -> [Node]
--getNodes errMsg graph ids = map (\nid -> lookupNode (errMsg ++ ":getNodes") nid nodeSet) ids
--  where nodeSet = graphNodes graph
getNodes errMsg graphs ids = map (\nid -> case lookupGraphNodeMaybe (errMsg++":getNodes") nid graphs of
  Just n  -> n
  Nothing -> error (errMsg ++ ":getNodes: node " ++ (show nid) ++ " not in graph " ++ (show graphs) ++ ".\n")) ids

-- |getNodeCons graph prevNodeId curNodeId tupPaths. Recursively looks at node
-- |outputs to find all consumers of the value identified by the
-- |current node and tuple paths (which identify the relevant
-- |subvalues of the current node's value). Returns a set of
-- |all tup and tup acc that proceed the consumers, and the set of
-- |consumers themselves.
getNodeCons :: Graph -> NodeId -> NodeId -> Set [Int] 
  -> (Set NodeId, Set NodeId)
getNodeCons graph prevNodeId curNodeId tupPaths = case nodeTy (trace' ("getNodeCons: " ++ (show (prevNodeId, curNodeId, tupPaths))) $ curNode) of
    -- if this is a tuple node, call rescurively passing on
    -- paths to identity which parts of the node's value we are
    -- interested in.
    TupNd        -> res'
      where -- find the tuple indices of the previous value in this tuple
            curIns = nodeIn curNode
            indices = elemIndices prevNodeId curIns
            -- make new path set to describe which subparts of the
            -- value at this node refer to the original node's value
            curPaths = Data.Set.toList tupPaths
            nxtPaths = [ idx:path | idx <- indices, path <- curPaths ]
            nxtPathSet = Data.Set.fromList nxtPaths
            -- call for all outputs of this tuple
            curOuts = nodeOut curNode
            results = map (\outId -> 
              getNodeCons graph curNodeId outId nxtPathSet) curOuts
            -- merge results
            (r1,r2) = foldl 
               (\(a1,a2) -> \(b1,b2) -> (union a1 b1, union a2 b2)) 
               (Data.Set.empty, Data.Set.empty) results
            -- add this node to the set of those that proceed the
            -- consumers
            res' = (Data.Set.insert curNodeId r1, r2)
    -- if this is a tuple accessor, call recursively for all paths
    -- that begin with idx
    TupAccNd idx -> case subPaths of 
        -- none of this value is interesting, so explore no further
        [] -> (Data.Set.empty, Data.Set.empty)
        -- this value contains the value being traced so continue
        _  -> (Data.Set.insert curNodeId r1, r2)
          where -- call outputs recursively
                curOuts = nodeOut curNode
                results = map (\outId -> 
                  getNodeCons graph curNodeId outId nxtPathSet) curOuts
                -- merge results
                (r1,r2) = foldl 
                   (\(a1,a2) -> \(b1,b2) -> (union a1 b1, union a2 b2)) 
                   (Data.Set.empty, Data.Set.empty) results
      where -- get all paths that start with this idx
            paths = filter (\l -> (not $ null l) && (head l) == idx) $ Data.Set.toList tupPaths
            subPaths = map tail paths
            nxtPathSet = Data.Set.fromList subPaths
    -- otherwise assume this is a consumer, and add it to the consumer
    -- set
    other        -> (Data.Set.empty, Data.Set.fromList [curNodeId]) 
  where --curNode = lookupNode "getNodeCons:curNode:" curNodeId nodes
        curNode = lookupGraphNode "getNodeCons:curNode:" curNodeId [graph]

-- |getConsumers graph nodeId. Searches through all outputs,
-- |and tuple, and tuple accessor nodes, finding consumers of the
-- |value produced by this node. Returns a set of the nodes that
-- |proceed these consumer nodes (and so may receive
-- |values from the consumers), and the node ids of the consumer
-- |nodes themselves. 
getNodeConsumers :: Graph -> NodeId -> (Set NodeId, Set NodeId)
getNodeConsumers graph nodeId = res
  where -- get current node
        --nodes = graphNodes graph
        --node = lookupNode "getNodeConsumers" nodeId nodes
        node = lookupGraphNode "getNodeConsumers" nodeId [graph]
        -- init tuple path to [] (meaning the whole value
        -- is the what we currently care about)
        initPath = Data.Set.fromList [[]]
        -- call for all outputs
        curOuts = nodeOut node
        results = map (\outId -> 
          getNodeCons graph nodeId outId initPath) curOuts
        -- merge results
        res = foldl (\(a1,a2) -> \(b1,b2) -> (union a1 b1, union a2 b2)) 
               (Data.Set.empty, Data.Set.empty) results 

-- |visitNodeM f graph nodeId. if the node specified by nodeId has not already been visited
-- |visits all its inputs, and then applies f to itself.
visitNodeM :: Monad m => ([Graph] -> Node -> m ()) -> [Graph] -> NodeId -> StateT (NodeEnv ()) m ()
visitNodeM f graphs nid = do
  -- check if already visited
  visited <- get
  case Data.IntMap.member nid visited of
    -- if has -> ignore
    True -> return ()  
    -- if not -> visit inputs
    False -> do
      -- get the node
      -- depreceated - before parent graphs:
      --let nodes = graphNodes graph
      --let node = lookupNode "visitNodeM" nid nodes
      -- new code -
      let node = fromMaybe (error $ "visitNodeM: node " ++ (show nid) ++ " is not in graph.") $ lookupGraphNodeMaybe "visitNodeM" nid graphs
      -- get its inputs
      let inputs = nodeIn node
      case elem nid inputs of
        True -> do
          -- cannot be an input of itself!
          error $ "visitNodeM: cycle in graph! node " ++ (show nid) ++ " cannot be its own input!"
        False -> do
          -- visit them
          mapM (visitNodeM f graphs) inputs
          -- visit this
          lift $ f graphs node
          -- mark this as visited
          modify (\set -> Data.IntMap.insert nid () set)

-- |visitGraphM visitF graph. Depth first traversal of a graph, applying
-- |visitF to each node, never visiting the same node twice.
visitGraphM :: Monad m => ([Graph] -> Node -> m ()) -> [Graph] -> m ()
visitGraphM f graphs = do
  -- get the output node id
  let outId = graphOut $ head graphs 
  -- visit it
  execStateT (visitNodeM f graphs outId) Data.IntMap.empty
  return ()

-- |maxDepthVisitor graph node. Records the maximum depth of this node in
-- |the state. I.e. the number of nodes above it's deepest input.
maxDepthVisitor :: Monad m => [Graph] -> Node -> StateT (NodeEnv Int) m ()
maxDepthVisitor graphs node = do
  -- get the depths of all its inputs
  inDepths <- mapM (\nid -> do depth <- gets (lookupNode "maxDepthVisitor" nid); return depth) $ nodeIn node
  -- get the max
  let maxDepth = if inDepths == [] then 0 else maximum inDepths
  -- record in the state
  modify (\env -> Data.IntMap.insert (nodeId node) (maxDepth+1) env)
  return ()

type PartNodeFun m = [NodeId] -> m [[NodeId]]

-- |visitDeepestNodeM pf f graph depths nodeId. if the node specified by nodeId has not already been visited
-- |visits all its inputs, in order of descending depth, and then applies f to itself.
-- |Uses pf to partition node lists into different groups, where the groups should be visited
-- |in the order they appear in the list, but where members of groups can appear in any order.
visitDeepestNodeM :: Monad m => PartNodeFun m -> ([Graph] -> Node -> m ()) -> [Graph] -> (NodeEnv Int) -> NodeId -> StateT (NodeEnv ()) m ()
visitDeepestNodeM pf f graphs@(head:tail) depths nid = do
  -- check if already visited
  visited <- get
  case Data.IntMap.member nid visited of
    -- if has -> ignore
    True -> return ()  
    -- if not -> visit inputs
    False -> do
      -- get the node
      let node = fromMaybe (error $ "visitDeepestNodeM: node " ++ (show nid) ++ " is not in graph.") $ lookupGraphNodeMaybe "visitDeepestNodeM" nid graphs
      -- get its inputs 
      let inputs = nodeIn node
      -- remove any of them that are in parent graphs
      -- i.e. assume they have already been visited, and 
      --      shouldn't be again.
      let inputs' = filter (not . graphsContain tail) inputs
      let inputs'' = map (\nid -> if graphsContain [head] nid then nid else error $ "visitDeepestNodeM: node " ++ (show nid) ++ " not in head graph.") inputs'
      case elem nid inputs'' of
        True -> do
          -- cannot be an input of itself!
          error $ "visitDeepestNodeM: cycle in graph! node " ++ (show nid) ++ " cannot be its own input!"
        False -> do
          -- group inputs
          inGroups <- lift $ pf inputs'' 
          -- get input depths
          let inDepths = map (map (\id -> (lookupNode "visitDeepestNodeM:nodedepth:" id depths, id))) inGroups --inputs''
          -- visit them in order of descending depth
          let sortedGroups = map (reverse.sort) inDepths
          --let sortedInDepths = reverse $ sort inDepths
          let (_,sortedInputs) = unzip $ concat $ sortedGroups
          --let (_,sortedInputs) = unzip sortedInDepths
          mapM (visitDeepestNodeM pf f graphs depths) sortedInputs
          -- visit this
          lift $ f graphs node
          -- mark this as visited
          modify (\set -> Data.IntMap.insert nid () set)

-- |cycleVisitor checks there are no cycles in our graph.
cycleVisitor :: Monad m => [Graph] -> Node -> StateT (Set Int, [Int]) m ()
cycleVisitor graphs node = do
  let nid = nodeId node
  (visitedSet, visitList) <- get
  case Data.Set.member nid visitedSet of
    True -> error $ "Cycle in graph!\n" ++ (show visitList) ++ "," ++ (show nid) ++ "\n" ++ (show graphs)
    False -> do
      modify (\(st,lst) -> (Data.Set.insert nid st, nid:lst))
      return ()
  
-- |visitDeepestGraphM visitF graph. Visits the nodes in the graph in deepest
-- |first depth first traversal. I.e. it visits the deepest leaves, before shallower
-- |ones. 
visitDeepestGraphM :: Monad m => PartNodeFun m -> ([Graph] -> Node -> m ()) -> [Graph] -> m ()
visitDeepestGraphM pf f graphs = do
  -- check for cycles
  execStateT (visitGraphM cycleVisitor graphs) (Data.Set.empty, [])
  -- get the output node
  let outId = graphOut $ head graphs
  let outNode = lookupGraphNode "visitDeepestGraphM" outId graphs  
  -- compute the depths of the nodes
  depths <- execStateT (visitGraphM maxDepthVisitor graphs) Data.IntMap.empty
  -- visit them in deepest first order
  execStateT (visitDeepestNodeM pf f graphs depths outId) Data.IntMap.empty
  return ()

 



