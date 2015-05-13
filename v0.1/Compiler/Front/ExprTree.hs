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
module Compiler.Front.ExprTree (Expr(..), IdxTree(..), Val(..), NeverEq(..), 
  getExprId, getIdxTreeIds, getIdxTreeId, makeExprMap, showExprTreeWithIds,
  showExprTree, makeDemoGraph, renewExprIds, newExpr, newExprId, newExprVarId, renewIdAndExprIds, 
initExprVarIds, initIdxTreeExpIds, initIdxTreeVarIds,
replaceIdxTreeIds, replaceExprIds, visitExprTree, replaceExprIdsOnly, 
 StructEq(..), getLetVarExprIds, countExprs, isAppExpr, isLeafExpr, getIdxTreeVars, isVarExpr, getVarExprName, getExprById,
 checkExpIdsUnique, checkExpIdsUnique2, maxExpId, removeEmptyTups, getFreeExprVars, getVarExprIds, foldExpr,
 filterExprs, removeFunApps) where

import Compiler.Front.Indices
import Compiler.Front.Common (eids, vids, rndnums, droplast, indent, delimList, ShowP(..))

import Control.Monad ( mapM )
import Control.Monad.State.Strict (State, execStateT, runState, runStateT, StateT, evalStateT, lift, modify, get)
import Data.Functor.Identity (runIdentity)

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Data.Map (insert, unions, empty, lookup, singleton, union)
import Data.Maybe (isJust)

import Debug.Trace (trace)

-- |Class for types that have structural equality defined on them
class StructEq a where
  structEq :: a -> a -> Bool

-- |Shows the a var id in a show function
showVarId :: Idx -> String
showVarId i = "" --"_" ++ (show i)

newVarName :: Idx -> String -> String
newVarName id s = s ++ "_" ++ (show id)

-- |Identifier patterns
data IdxTree = 
     IdxLeaf Idx Idx String
   | IdxTup  Idx [IdxTree] 
   | IdxNub Idx -- blank
 deriving (Eq, Ord, Show, Read)

isIdxLeaf :: IdxTree -> Bool
isIdxLeaf (IdxLeaf _ _ _) = True
isIdxLeaf _ = False

{-instance Show IdxTree where
  show (IdxLeaf i v s) = s ++ (showVarId v)
  show (IdxTup i l) = "(" ++ (droplast 2 $ concat $ map (\e -> (show e) ++ ", ") l) ++ ")"
  show (IdxNub i) = "_"-}

instance ShowP IdxTree where
  showP (IdxLeaf i v s) = s ++ (showVarId v)
  showP (IdxTup i l) = "(" ++ (droplast 2 $ concat $ map (\e -> (showP e) ++ ", ") l) ++ ")"
  showP (IdxNub i) = "_"

-- |idxTreeStructEqual takes two idx trees and returns true if
-- |they are structurally the same and returns a map from ids in
-- |the fst tree to those in the snd.
idxTreeStructEqual :: (IdxTree, IdxTree) -> (Bool, Map Idx Idx)
idxTreeStructEqual ab = case ab of
  (IdxTup _ l1, IdxTup _ l2) | length l1 == length l2 -> (and bools, Data.Map.unions envs)
    where (bools, envs) = unzip $ map idxTreeStructEqual $ zip l1 l2
  (IdxLeaf _ v1 _, IdxLeaf _ v2 _) -> (True, Data.Map.singleton v1 v2)
  (IdxNub _, IdxNub _) -> (True, Data.Map.empty)
  other -> (False, Data.Map.empty)

instance StructEq IdxTree where
  structEq a b = fst $ idxTreeStructEqual (a,b)

-- |Returns a list of all the var ids in the idx tree
getIdxTreeIds :: IdxTree -> [Idx]
getIdxTreeIds it = case it of
  (IdxLeaf _ vid _) -> [vid]
  (IdxTup _ l) -> concat $ map getIdxTreeIds l
  _ -> []

getIdxTreeId :: IdxTree -> Idx
getIdxTreeId it = case it of 
  (IdxLeaf i _ _) -> i
  (IdxTup i _) -> i
  (IdxNub i) -> i

-- |Create a new IdxTree. Takes a list of string identifiers and returns a new 
-- |Idx tree based on those strings
nIdxT :: [String] -> State IdxSet IdxTree
nIdxT (h:t) =
  if t == [] then 
    do lf <- nExp IdxLeaf; vid <- newid vids; return (lf vid h)
  else 
    do tf <- nExp IdxTup
       ls <- mapM (\s -> do lf <- nIdxT [s] ; return lf) (h:t)
       return (tf ls)
nIdxT [] = error "tuples must be non empty"

-- |Queries an IdxTree. Takes a path (list of indices into IdxTup lists) and returns the Idx of 
-- |the IdxTree at that location in the tree
qIdxT :: [Int] -> IdxTree -> Idx
qIdxT (h:r) t = case t of 
  (IdxLeaf i vi s) -> error "found a leaf, leaves do not have children"
  (IdxNub i) -> error "found a blank underscore, underscores don't have children"
  (IdxTup i l) -> qIdxT r (l !! h) 
qIdxT [] t = case t of 
  (IdxLeaf i _ _) -> i
  (IdxTup  i _) -> i
  (IdxNub  i) -> i
 
-- |Freshens the ids in an IdxTree. Replaces all expression ids with new ones
-- |and creates new consistant variable ids.
fIdxT :: IdxTree -> StateT [(Idx, Idx)] (State IdxSet) IdxTree
fIdxT (IdxLeaf i v s) = do
  i' <- lift (newid eids)
  v' <- newid' vids v
  return (IdxLeaf i' v' s {-(newVarName v' s)-})
fIdxT (IdxTup i l) = do
  i' <- lift (newid eids)
  l' <- mapM (\t -> do t' <- fIdxT t; return t') l
  return (IdxTup i' l')
fIdxT (IdxNub i) = do
  i' <- lift (newid eids)
  return (IdxNub i')
fIdxTr :: IdxTree -> State IdxSet IdxTree
fIdxTr t = evalStateT (fIdxT t) []

-- |Replaces all expression ids with new ones
-- |and creates new consistant variable ids.
replaceIdxTreeIds :: Monad m => 
  IdxTree -> StateT [(Idx, Idx)] (StateT IdxSet m) IdxTree
replaceIdxTreeIds it = case it of
  (IdxLeaf i v s) -> do
    i' <- lift (newidST eids)
    v' <- newidST' vids v
    return (IdxLeaf i' v' s)
  (IdxTup i l) -> do
    i' <- lift (newidST eids)
    l' <- mapM (\t -> do t' <- replaceIdxTreeIds t; return t') l
    return (IdxTup i' l')
  (IdxNub i) -> do
    i' <- lift (newidST eids)
    return (IdxNub i')
  
-- |Returns the same tree with the expression ids ialized
initIdxTreeExpIds :: Monad m => IdxTree -> StateT IdxSet m IdxTree
initIdxTreeExpIds idpat = do
  id <- newid'' eids
  case idpat of
    (IdxNub _) -> return $ IdxNub id
    (IdxLeaf _ v s) -> return $ IdxLeaf id v s
    (IdxTup _ l) -> do
      l' <- mapM initIdxTreeExpIds l
      return $ IdxTup id l'

-- |A value where comparisons with itself are never equal
data NeverEq = NeverEq
  deriving (Show, Read)

instance Eq NeverEq where
  x == y = False

instance Ord NeverEq where 
  compare x y = LT

  x <= y           =  compare x y /= GT
  x <  y           =  compare x y == LT
  x >= y           =  compare x y /= LT
  x >  y           =  compare x y == GT

  max x y 
       | x >= y    =  x
       | otherwise =  y
  min x y
       | x <  y    =  x
       | otherwise =  y

-- |Value carriers
data Val = 
     S String
   | I Int
   | B Bool
   | F Float
   | NullVal
   | EveryVal NeverEq
 deriving (Eq, Ord, Show, Read)

{-instance Show Val where
  show (S s) = show s
  show (I i) = show i
  show (B b) = show b
  show (F f) = show f
  show (NullVal) = "null"
  show (EveryVal _) = "every"-}

instance ShowP Val where
  showP (S s) = show s
  showP (I i) = show i
  showP (B b) = show b
  showP (F f) = show f
  showP (NullVal) = "null"
  showP (EveryVal _) = "every"

-- |Expression tree grammar
data Expr =
     Lit Idx Val
   | Var Idx Idx String
   | Tup Idx [Expr]
   | Rel Idx [Expr]
   | Fun Idx IdxTree Expr
   | App Idx Expr Expr
   | If  Idx Expr Expr Expr
   | Let Idx IdxTree Expr Expr
  deriving (Eq, Ord, Show, Read)

isVarExpr :: Expr -> Bool
isVarExpr (Var _ _ _) = True
isVarExpr _ = False

isAppExpr :: Expr -> Bool
isAppExpr (App _ _ _) = True
isAppExpr _ = False

isLeafExpr :: Expr -> Bool
isLeafExpr (Var _ _ _) = True
isLeafExpr (Lit _ _) = True
isLeafExpr _ = False

getVarExprName :: Expr -> String
getVarExprName (Var _ _ n) = n
getVarExprName other = error $ "getVarExprName applied to non-var expression: " ++ (showP other)

{-instance Show Expr where 
  show (Lit i v) = show v
  show (Var i v s) = s ++ (showVarId v) -- ++ ":" ++ (show v)
  show (Tup i l) = "(" ++ (droplast 2 $ concat $ map (\e -> (show e) ++ ", ") l) ++ ")"
  show (Rel i l) = "[" ++ (droplast 2 $ concat $ map (\e -> (show e) ++ ", ") l) ++ "]"
  show (Fun i it e) = "(\\" ++ (show it) ++ " -> " ++ (show e) ++ ")"
  show (App i f e) = "(" ++ (show f) ++ " " ++ (show e) ++ ")"
  show (If i p t e) = "if " ++ (show p) ++ " then " ++ (show t) ++ " else " ++ (show e)
  show (Let i it be ie) = "(let " ++ (show it) ++ " = " ++ (show be) ++ " in " ++ (show ie) ++ ")"-}

instance ShowP Expr where
  showP (Lit i v) = showP v
  showP (Var i v s) = s ++ (showVarId v) -- ++ ":" ++ (show v)
  showP (Tup i l) = "(" ++ (droplast 2 $ concat $ map (\e -> (showP e) ++ ", ") l) ++ ")"
  showP (Rel i l) = "[" ++ (droplast 2 $ concat $ map (\e -> (showP e) ++ ", ") l) ++ "]"
  showP (Fun i it e) = "(\\" ++ (showP it) ++ " -> " ++ (showP e) ++ ")"
  showP (App i f e) = "(" ++ (showP f) ++ " " ++ (showP e) ++ ")"
  showP (If i p t e) = "if " ++ (showP p) ++ " then " ++ (showP t) ++ " else " ++ (showP e)
  showP (Let i it be ie) = "(let " ++ (showP it) ++ " = " ++ (showP be) ++ " in " ++ (showP ie) ++ ")"

-- |structEqual takes to expressions and returns true if they
-- |are structurally equal (i.e. equal up to renaming of variables)
structEqual :: Map Idx Idx -> (Expr, Expr) -> Bool
structEqual env ab = case ab of
    (Lit _ v1, Lit _ v2) -> v1 == v2
    -- vars equal up to renaming
    (Var _ v1 _, Var _ v2 _) -> case Data.Map.lookup v1 env of
      Just v2' -> v2 == v2'
      Nothing  -> v1 == v2
    -- recursion
    (Tup _ l1, Tup _ l2) -> and $ map recur $ zip l1 l2
    (Rel _ l1, Rel _ l2) -> and $ map recur $ zip l1 l2
    (Fun _ it1 e1, Fun _ it2 e2) -> case itseq of
        True  -> structEqual (Data.Map.union env env') (e1, e2)
        False -> False 
      where (itseq, env') = idxTreeStructEqual (it1, it2) 
    (App _ f1 a1, App _ f2 a2) -> (recur (f1, f2)) && (recur (a1, a2))
    (If _ p1 t1 e1, If _ p2 t2 e2) -> (recur (p1,p2)) && (recur (t1,t2)) && (recur (e1,e2))
    (Let _ it1 b1 e1, Let _ it2 b2 e2) -> case itseq && (recur (b1,b2)) of
        True  -> structEqual (Data.Map.union env env') (e1, e2)
        False -> False 
      where (itseq, env') = idxTreeStructEqual (it1, it2) 
    other -> False 
  where recur = structEqual env

instance StructEq Expr where
  structEq a b = structEqual Data.Map.empty (a,b)

showExprTy :: Expr -> String
showExprTy expr = case expr of
  Lit _ _ -> "lit"
  Var _ _ _ -> "var" 
  Tup _ _ -> "tup"
  Rel _ _ -> "rel" 
  Fun _ _ _ -> "fun"
  App _ _ _ -> "app"
  If _ _ _ _ -> "if"
  Let _ _ _ _ -> "let"

-- |Returns the expression idx of the expression
getExprId :: Expr -> Idx
getExprId (Lit i _) = i
getExprId (Var i _ _) = i
getExprId (Tup i _) = i
getExprId (Rel i _) = i
getExprId (Fun i _ _) = i
getExprId (App i _ _) = i
getExprId (If i _ _ _) = i
getExprId (Let i _ _ _) = i

-- |Creates a new expr id 
newExprId :: Monad m => StateT IdxSet m Idx
newExprId = do
  id <- newid'' eids
  return id

-- |Creates a new expr var id 
newExprVarId :: Monad m => StateT IdxSet m Idx
newExprVarId = do
  id <- newid'' vids
  return id

-- |Creates a new expr with a new expression id using the data constructor passed
newExpr :: Monad m => (Idx -> a) -> StateT IdxSet m a
newExpr dataCon = do id <- newid'' eids; return (dataCon id)

-- |Creates a new expression by generating a new Id
-- |and currying the data constructor passed it with it.
nExp :: (Idx -> a) -> State IdxSet a
nExp dc = do id <- newid eids; return (dc id)

-- |Freshens an expression with new exp ids and variable ids. Variable 
-- |ids are assumed to be unique in the original tree.
fExp :: Expr -> StateT [(Idx, Idx)] (State IdxSet) Expr
fExp (Lit i v) = do i' <- lift (newid eids) ; return (Lit i' v)
fExp (Var i v s) = do
  i' <- lift (newid eids)
  v' <- getid' v
  -- if number has changed use new name
  --let s' = if v' /= v then newVarName v' s else s
  return (Var i' v' s)
fExp (Tup i l) = do
  i' <- lift (newid eids)
  l' <- mapM fExp l
  return (Tup i' l')
fExp (Rel i l) = do
  i' <- lift (newid eids)
  l' <- mapM fExp l
  return (Rel i' l')
fExp (Fun i it e) = do
  i' <- lift (newid eids)
  it' <- fIdxT it
  e' <- fExp e
  return (Fun i' it' e')
fExp (App i f e) = do
  i' <- lift (newid eids)
  f' <- fExp f
  e' <- fExp e
  return (App i' f' e')
fExp (If i p t e) = do
  i' <- lift (newid eids)
  p' <- fExp p
  t' <- fExp t
  e' <- fExp e
  return (If i' p' t' e')
fExp (Let i it be ie) = do
  i' <- lift (newid eids)
  be' <- fExp be
  it' <- fIdxT it
  ie' <- fExp ie
  return (Let i' it' be' ie')
fExpr :: Expr -> State IdxSet Expr
fExpr e = evalStateT (fExp e) [] 

-- |Renew all expression ids in the expression
renewExprIds :: Monad a => Expr -> StateT IdxSet a Expr
renewExprIds exp = do 
  idxset <- get
  let (exp', idxset') = runState (fExpr exp) idxset
  modify (\_ -> idxset')
  return exp'

-- |Replaces all exp ids with new ones and create new
-- |consistant variable ids. 
replaceExprIds :: Monad m => Expr -> StateT [(Idx, Idx)] (StateT IdxSet m) Expr
replaceExprIds exp = case exp of
  (Lit i v) -> do i' <- lift (newidST eids) ; return (Lit i' v)
  (Var i v s) -> do
    i' <- lift (newidST eids)
    v' <- getidST v
    return (Var i' v' s)
  (Tup i l) -> do
    i' <- lift (newidST eids)
    l' <- mapM replaceExprIds l
    return (Tup i' l')
  (Rel i l) -> do
    i' <- lift (newidST eids)
    l' <- mapM replaceExprIds l
    return (Rel i' l')
  (Fun i it e) -> do
    i' <- lift (newidST eids)
    it' <- replaceIdxTreeIds it
    e' <- replaceExprIds e
    return (Fun i' it' e')
  (App i f e) -> do
    i' <- lift (newidST eids)
    f' <- replaceExprIds f
    e' <- replaceExprIds e
    return (App i' f' e')
  (If i p t e) -> do
    i' <- lift (newidST eids)
    p' <- replaceExprIds p
    t' <- replaceExprIds t
    e' <- replaceExprIds e
    return (If i' p' t' e')
  (Let i it be ie) -> do
    i' <- lift (newidST eids)
    be' <- replaceExprIds be
    it' <- replaceIdxTreeIds it
    ie' <- replaceExprIds ie
    return (Let i' it' be' ie')

fIdxTreefExpr :: IdxTree -> Expr -> StateT [(Idx, Idx)] (State IdxSet) (IdxTree, Expr)
fIdxTreefExpr id exp = do
  id' <- fIdxT id
  exp' <- fExp exp
  return (id', exp') 

-- |Renew all expression ids and var ids in an idx pattern and expression 
renewIdAndExprIds :: Monad a => IdxTree -> Expr -> StateT IdxSet a (IdxTree, Expr)
renewIdAndExprIds idtree exp = do
  idxset <- get
  let ((id', exp'),idxset') = runState (evalStateT (fIdxTreefExpr idtree exp) []) idxset
  modify (\_ -> idxset')
  return (id', exp')

-- |Uses variable names to create new variable ids for all var ids
initIdxTreeVarIds :: Monad m => IdxTree -> StateT IdxSet m (IdxTree, [(String, Idx)])
initIdxTreeVarIds it = case it of
  (IdxNub _) -> return (it, [])
  (IdxLeaf i _ n) -> do
    vid <- newid'' vids
    return (IdxLeaf i vid n, [(n, vid)])
  (IdxTup i l) -> do
    l' <- mapM initIdxTreeVarIds l
    let (itlst, maplst) = unzip l'
    return (IdxTup i itlst, concat maplst) 

-- |Uses variable names to create new variable ids for all vars
initExprVarIds :: Monad m => [(String, Idx)] -> Expr -> StateT IdxSet m Expr 
initExprVarIds env exp = case exp of
  -- recursive calls
  (App i fe ae) -> do
    fe' <- initExprVarIds env fe
    ae' <- initExprVarIds env ae
    return (App i fe' ae')
  (Tup i l) -> do
    l' <- mapM (initExprVarIds env) l
    return (Tup i l')
  (Rel i l) -> do
    l' <- mapM (initExprVarIds env) l
    return (Rel i l')
  (If i pe te ee) -> do
    pe' <- initExprVarIds env pe
    te' <- initExprVarIds env te
    ee' <- initExprVarIds env ee
    return (If i pe' te' ee')
  -- variable lookup
  (Var i _ n) -> case lookup n env of
    Just vid -> return (Var i vid n)
    Nothing  -> error $ "Variable '" ++ n ++ "' not declared at expression " ++ (show i) ++ " while creating var ids."
  -- expressions that start scopes
  (Let i it be ie) -> do
    be' <- initExprVarIds env be
    (it', env') <- initIdxTreeVarIds it
    ie' <- initExprVarIds (env' ++ env) ie
    return (Let i it' be' ie')
  (Fun i it e) -> do
    (it', env') <- initIdxTreeVarIds it
    e' <- initExprVarIds (env' ++ env) e
    return (Fun i it' e')
  -- literals
  _ -> return exp

-- |saveNewExprId generates a new expression id and keeps a map
-- |of old ids to new ids.
saveNewExprId :: Monad m => Idx -> StateT (Map Idx Idx) (StateT IdxSet m) Idx
saveNewExprId id = do
  nid <- lift $ newidST eids  
  modify (\mp -> Data.Map.insert id nid mp)
  return nid 

-- |Replaces all expression ids with new ones
-- |and leaves var ids as is
replaceIdxTreeIdsOnly :: Monad m => 
  IdxTree -> StateT (Map Idx Idx) (StateT IdxSet m) IdxTree
replaceIdxTreeIdsOnly it = case it of
  (IdxLeaf i v s) -> do
    i' <- saveNewExprId i
    return (IdxLeaf i' v s)
  (IdxTup i l) -> do
    i' <- saveNewExprId i
    l' <- mapM (\t -> do t' <- replaceIdxTreeIdsOnly t; return t') l
    return (IdxTup i' l')
  (IdxNub i) -> do
    i' <- saveNewExprId i
    return (IdxNub i')

-- |Replaces all exp ids with new ones in exps for which the predicate holds, and leaves var ids as is.
replaceExprIdsOnly :: Monad m => (Expr -> Bool) -> Expr -> StateT (Map Idx Idx) (StateT IdxSet m) Expr
replaceExprIdsOnly predicate exp = if not (predicate exp) then return exp else case exp of
  (Lit i v) -> do i' <- saveNewExprId i; return (Lit i' v)
  (Var i v s) -> do
    i' <- saveNewExprId i
    return (Var i' v s)
  (Tup i l) -> do
    i' <- saveNewExprId i
    l' <- mapM recur l
    return (Tup i' l')
  (Rel i l) -> do
    i' <- saveNewExprId i
    l' <- mapM recur l
    return (Rel i' l')
  (Fun i it e) -> do
    i' <- saveNewExprId i
    it' <- replaceIdxTreeIdsOnly it
    e' <- recur e
    return (Fun i' it' e')
  (App i f e) -> do
    i' <- saveNewExprId i
    f' <- recur f
    e' <- recur e
    return (App i' f' e')
  (If i p t e) -> do
    i' <- saveNewExprId i
    p' <- recur p
    t' <- recur t
    e' <- recur e
    return (If i' p' t' e')
  (Let i it be ie) -> do
    i' <- saveNewExprId i
    be' <- recur be
    it' <- replaceIdxTreeIdsOnly it
    ie' <- recur ie
    return (Let i' it' be' ie')
  where recur = replaceExprIdsOnly predicate

--evalReplaceExprIdsOnly :: (Expr -> Bool) -> Expr -> Expr
--evalReplaceExprIdsOnly pred expr = evalStateT (replaceExprIdsOnly pred expr) Data.Map.empty

-- |visitIdxTree takes two functions, 
{-visitIdxTree :: Monad m =>
  (a -> IdxTree -> m (IdxTree, a)) ->
  (a -> a -> a) -> 
  a -> IdxTree -> m (IdxTree, a)
visitIdxTree f combineF a it = case it of
  -- recursive
  IdxTup i l -> do
    l' <- mapM (f combineF a) l  
    let (its, as) = unzip l'
    case length as of
      0 -> error "visitIdxTree empty idx tup list!"
      _ -> do
        let a' = foldl1 combineF as 
        return (IdxTup i its, a')
  -- base case
  other -> do
    (other', a') <- f combineF a other  
    return (other', a')-}

-- |visitExprTree takes three functions, one to process
-- |exprs, another process idx trees, and one to combine
-- |'a' (environment) values, such that one
-- |can easily override basic expr visitor functionality.
-- |Note: to recursively visit, exprF must call visitExprTree exprF idxF
-- |unless expr is a leaf.
visitExprTree :: Monad m => 
  (a -> Expr -> m Expr) -> 
  (a -> IdxTree -> m (IdxTree,a)) -> 
 -- (a -> a -> a) -> 
  a -> Expr -> m Expr
visitExprTree exprF idxF {-comF-} a expr = case {-trace ("visiting " ++ (show $ getExprId expr) ++ " => " ++ (show expr) ++ "\n") $ -} expr of
  -- recursive cases
  (Tup i l) -> do
    l' <- mapM (exprF a) l
    return $ Tup i l'
  (Rel i l) -> do
    l' <- mapM (exprF a) l
    return $ Rel i l'
  (If i pe te ee) -> do
    pe' <- exprF a pe
    te' <- exprF a te
    ee' <- exprF a ee
    return $ If i pe' te' ee'  
  (App i fe ae) -> do
    fe' <- exprF a fe
    ae' <- exprF a ae
    return $ App i fe' ae'
  (Let i it be ie) -> do
    be' <- exprF a be
    (it',a') <- idxF a it
    ie' <- exprF a' ie
    return $ Let i it' be' ie'
  (Fun i it e) -> do
     (it',a') <- idxF a it
     e' <- exprF a' e
     return $ Fun i it' e'
  -- base case
  other -> do
    other' <- exprF a other
    return other'

getIdxTreeVars :: IdxTree -> [(String, Idx)]
getIdxTreeVars it = case it of
  IdxTup _ l -> concat $ map getIdxTreeVars l
  IdxLeaf _ v n -> [(n,v)]
  other -> []

getFreeExprVarsM :: Monad m => [(String, Idx)] -> Expr -> StateT [(String, Idx)] m Expr 
getFreeExprVarsM env expr = do
  -- apply recursively to children first
  expr' <- if isLeafExpr expr 
           then return expr -- base case
           else visitExprTree getFreeExprVarsM (\env1 -> \it -> let env2 = getIdxTreeVars it in return (it, env1 ++ env2)) env expr -- rec case
  -- if this is a var and not in env, then add to state
  case expr' of
    (Var eid vid nam) -> case lookup nam env of
      Just vid' -> if vid /= vid' then error $ "ExprTree:getFreeExprVars: vids don't match for vars called " ++ nam ++ " " ++ (show $ (vid, vid')) else return expr'
      Nothing   -> do modify (\st -> (nam, vid):st) ; return expr'
    other -> return expr'

getFreeExprVars :: Expr -> [(String, Idx)]
getFreeExprVars exp = runIdentity $ execStateT (getFreeExprVarsM [] exp) []

removeEmptyIdxTups :: IdxTree -> IdxTree
removeEmptyIdxTups idx = case idx of
  (IdxTup eid l) -> case map removeEmptyIdxTups l of
    [] -> error $ "removeEmptyIdxTups: Empty idx tuple!"
    [v] -> v
    l -> IdxTup eid l
  other -> other

removeEmptyTupsM :: Monad m => () -> Expr -> m Expr
removeEmptyTupsM msg expr = do
  -- apply recursively to children first
  expr' <- if isLeafExpr expr 
           then return expr -- base case
           else visitExprTree removeEmptyTupsM (\_ -> \it -> return (removeEmptyIdxTups it, msg)) msg expr -- rec case
  -- remove empty tups
  case expr' of
    Tup _ [] -> error $ "removeEmptyTups: Empty tuple!"
    Tup _ [v] -> return v
    other -> return other

removeEmptyTups :: Expr -> Expr
removeEmptyTups expr = runIdentity (removeEmptyTupsM () expr)

-- |removeFunAppsM pred msg expr. Removes all fun app exprs for which
-- |pred returns true.
removeFunAppsM :: Monad m => (Expr -> Bool) -> () -> Expr -> m Expr
removeFunAppsM pred msg expr = do
  -- apply recursively to children first
  expr' <- if isLeafExpr expr 
           then return expr -- base case
           else visitExprTree (removeFunAppsM pred) (\_ -> \it -> return (it, msg)) msg expr -- rec case
  -- remove empty tups
  case expr' of
    App eid fune arge -> if pred expr' then return arge else return expr' 
    other -> return other

-- |removeFunApps pred expr. Returns expr where all fun apps for which
-- |pred returns true have been removed (i.e. replaced by their argument exp).
removeFunApps :: (Expr -> Bool) -> Expr -> Expr
removeFunApps pred expr = runIdentity (removeFunAppsM pred () expr)

maxExpIdM :: Monad m => () -> Expr -> StateT Idx m Expr
maxExpIdM msg expr = do
  -- apply recursively to children first
  expr' <- if isLeafExpr expr 
           then return expr -- base case
           else visitExprTree maxExpIdM (\_ -> \it -> return (it, msg)) msg expr -- rec case
  -- check if already in list
  let eid1 = (getExprId expr') 
  modify (\eid2 -> max eid1 eid2)
  return expr'

maxExpId :: Monad m => Expr -> m Idx
maxExpId expr = execStateT (maxExpIdM () expr) (-1000)

checkExpIdsUniqueM :: Monad m => String -> Expr -> StateT [Idx] m Expr
checkExpIdsUniqueM msg expr = do
  -- apply recursively to children first
  expr' <- if isLeafExpr expr 
           then return expr -- base case
           else visitExprTree checkExpIdsUniqueM (\_ -> \it -> return (it, msg)) msg expr -- rec case
  -- check if already in list
  ids <- get
  let eid = (getExprId expr') 
  if elem eid ids
  then do
    error $ "Exp contains multiple exps with id " ++ (show eid) ++ " " ++ msg ++ ":\n" ++ (showExprTreeWithIds expr')   
  else do
    modify (\l -> eid:l)
    return expr'

checkExpIdsUnique :: Monad m => String -> Expr -> m Expr
checkExpIdsUnique msg expr = evalStateT (checkExpIdsUniqueM msg expr) []

checkExpIdsUniqueM2 :: Monad m => String -> Expr -> StateT [Idx] (IdxMonad m) Expr
checkExpIdsUniqueM2 msg expr = do
  -- apply recursively to children first
  expr' <- if isLeafExpr expr 
           then return expr -- base case
           else visitExprTree checkExpIdsUniqueM2 (\_ -> \it -> return (it, msg)) msg expr -- rec case
  -- check if after next id
  let eid = (getExprId expr')
  nid <- lift $ getNextIdxST msg eids
  if eid >= nid 
  then do
    error $ "Exp id is greater than next idx monad's next idx " ++ (show eid) ++ " >= " ++ (show nid) ++ " " ++ msg ++ ":\n" ++ (showExprTreeWithIds expr')  
  else 
    return ()
  -- check if already in list
  ids <- get 
  if elem eid ids
  then do
    error $ "Exp contains multiple exps with id " ++ (show eid) ++ " " ++ msg ++ ":\n" ++ (showExprTreeWithIds expr')   
  else do
    modify (\l -> eid:l)
    return expr'

checkExpIdsUnique2 :: Monad m => String -> Expr -> IdxMonad m Expr
checkExpIdsUnique2 msg expr = do
  st0 <- get
  (expr', st1) <- trace (msg ++ ":checkExpIdsUnique start idxmonad state = " ++ (show st0) ++ "\n") $ runStateT (checkExpIdsUniqueM2 msg expr) []
  return $ trace (msg ++ ":checkExpIdsUnique end idxmonad state = " ++ (show st1) ++ "\n")  expr'

-- |Makes a lookup table mapping expr ids to expressions
makeExprMap :: Expr -> [(Idx,Expr)]
makeExprMap e = case e of
  (Lit i _) -> [(i,e)]
  (Var i _ _) -> [(i,e)]
  (Tup i l) -> (i,e):(concat $ map makeExprMap l)
  (Rel i l) -> (i,e):(concat $ map makeExprMap l)
  (Fun i _ b) -> (i,e):(makeExprMap b)
  (App i f a) -> (i,e):(makeExprMap f) ++ (makeExprMap a)
  (If i pe te ee) -> (i,e):(makeExprMap pe) ++ (makeExprMap te) ++ (makeExprMap ee)
  (Let i _ be ie) -> (i,e):(makeExprMap be) ++ (makeExprMap ie)

-- |Shows idx tree with dangling data. Takes context object, and some function that 
-- |returns a string representation of the context data for each idx tree element by idx.
showIdxTree :: a -> (a -> Idx -> String) -> Int -> IdxTree -> String
showIdxTree c f n it = indent '\n' 1 $ indent ' ' n $ let n' = n+2 in case it of
  (IdxLeaf i vi str) -> (show it) ++ (f c i)
  (IdxTup i l) -> "(" ++ (delimList ", " $ map (showIdxTree c f n') l) ++ ")" ++ (f c i)
  (IdxNub i) -> (show it) ++ (f c i)

-- |Shows expression tree with dangling data
-- |Takes a context object, some function that takes a context and 
-- |an expr id and returns a string, an integer number of spaces to indent
-- |and an expression and returns a string rendering of the expression with 
-- |relevent data from the context attached.
showExprTree :: a -> (a -> Idx -> String) -> Int -> Expr -> String
showExprTree c f n e = indent '\n' 1 $ indent ' ' n $ let n' = n+2 in case e of
  (Lit i v) -> (showP v) ++ (f c i)
  (Var i v s) -> (showP e) ++ (f c i)
  (Tup i l) -> "(" ++ (droplast 2 $ concat $ map (\e -> (showExprTree c f n' e) ++ ", ") l) ++
               "\n" ++ (indent ' ' n $ ")" ++ (f c i))
  (Rel i l) -> "[" ++ (droplast 2 $ concat $ map (\e -> (showExprTree c f n' e) ++ ", ") l) ++
               "]" ++ (f c i)
  (Fun i it e) -> "\\" ++ (showIdxTree c f n' it) ++ " -> " ++ (showExprTree c f n' e) ++
                  "\n" ++ (indent ' ' n $ (f c i))
  (App i a b) -> "(" ++ (showExprTree c f n' a) ++
                 " " ++ (showExprTree c f n' b) ++ 
                 "\n" ++ (indent ' ' n $ ")") ++ " returns " ++ (f c i)
  (If i p t e) -> "if " ++ (showExprTree c f n' p) ++ 
                  " then " ++ (showExprTree c f n' t) ++ 
                  " else " ++ (showExprTree c f n' e) ++ (f c i)
  (Let i it be ie) -> "let " ++ (showP it) ++ (f c (getIdxTreeId it)) ++ " = " ++ (showExprTree c f n' be) ++ 
                      " in " ++ (showExprTree c f n' ie) ++ (f c i) 

-- |showExprTreeWithIds shows an expression with dangling expression ids for each term.
showExprTreeWithIds :: Expr -> String
showExprTreeWithIds expr = showExprTree () (\_ -> \id -> " :: " ++ "(" ++ (show id) ++ ")") 2 expr

-- |getLetVarExprIds gets the expression ids for all of the let vars
-- |in the program.
getLetVarExprIds :: Expr -> [(String, Idx)]
getLetVarExprIds expr = case expr of
  (Tup _ l) -> concat $ map getLetVarExprIds l
  (Rel _ l) -> concat $ map getLetVarExprIds l
  (Fun _ it e) -> getLetVarExprIds e
  (App _ fe ae) -> (getLetVarExprIds fe) ++ (getLetVarExprIds ae)
  (If _ pe te ee) -> (getLetVarExprIds pe) ++ (getLetVarExprIds te) ++ (getLetVarExprIds ee)
  (Let _ it be ie) ->  (getLetVarExprIdsIt it) ++ (getLetVarExprIds be) ++ (getLetVarExprIds ie)
  other -> []

-- |getLetVarExprIds gets the expression ids for all of the idxleafs
-- |in the IdxTree.
getLetVarExprIdsIt :: IdxTree -> [(String, Idx)]
getLetVarExprIdsIt it = case it of 
  (IdxNub _) -> []
  (IdxTup _ l) -> concat $ map getLetVarExprIdsIt l  
  (IdxLeaf eid vid n) -> [(n, eid)]

-- |countExprs predFun expr. Counts how many expressions match
-- |predFun in expre.
countExprs :: (Expr -> Bool) -> Expr -> Int
countExprs fun expr = case expr of
    (App i fe ae) -> v + (rec fe) + (rec ae)
    (Fun i it e) -> v + (rec e)
    (Tup i l) -> foldl (+) v $ map rec l
    (Rel i l) -> foldl (+) v $ map rec l
    (If i pe te ee) -> v + (rec pe) + (rec te) + (rec ee)
    (Let i it be ie) -> v + (rec be) + (rec ie)
    other -> v
  where v = if fun expr then 1 else 0
        rec = countExprs fun

foldIdxTree :: (IdxTree -> a) -> (a -> a -> a) -> IdxTree -> a
foldIdxTree f h it = case it of
  (IdxTup i l) -> (f it) `h` (foldl1 h $ map (foldIdxTree f h) l) 
  other -> f it

foldExpr :: (Expr -> a) -> (IdxTree -> a) -> (a -> a -> a) -> Expr -> a
foldExpr f g h e = case e of
    (App i fe ae) -> (f e) `h` (rec fe) `h` (rec ae)
    (Fun i it be) -> (f e) `h` (g it) `h` (rec be)
    (Tup i l) -> (f e) `h` (foldl1 h $ map rec l)
    (Rel i l) -> (f e) `h` (foldl1 h $ map rec l)
    (If i pe te ee) -> (f e) `h` (rec pe) `h` (rec te) `h` (rec ee)
    (Let i it be ie) -> (f e) `h` (g it) `h` (rec be) `h` (rec ie)
    (Var i vid n) -> f e
    (Lit i v) -> f e
  where rec = foldExpr f g h

getVarIdxTreeIds :: IdxTree -> [(Idx, Idx)]
getVarIdxTreeIds it = foldIdxTree (\i -> if isIdxLeaf i then let (IdxLeaf eid vid _) = i in [(vid,eid)] else []) (++) it

getVarExprIds :: Expr -> [(Idx, Idx)]
getVarExprIds exp = foldExpr (\e -> if isVarExpr e then let (Var eid vid _) = e in [(vid,eid)] else []) getVarIdxTreeIds (++) exp

getExprById :: Idx -> Expr -> Maybe Expr
getExprById idx expr = foldExpr (\e -> if getExprId e == idx then Just e else Nothing) (\_ -> Nothing) (\a -> \b -> if isJust a then a else b) expr

-- |filterExprs pred e. Returns a list of all expressions in exp that match the predicate pred.
filterExprs :: (Expr -> Bool) -> Expr -> [Expr]
filterExprs pred exp = foldExpr (\e -> if pred e then [e] else []) (\_ -> []) (++) exp

-- an example

nInt :: Int -> State IdxSet Expr
nInt n = do l <- (nExp Lit) ; return (l (I n))

nRndFlt :: State IdxSet Expr
nRndFlt = do rn <- newid rndnums ; l <- nExp Lit ; return (l (F (fromIntegral rn) ))

nGrid2d :: Int -> Int -> State IdxSet Expr
nGrid2d w h = do 
  let indcs = [ (x, y) | x <- [0..w], y <- [0..h] ]
  ts <- mapM (\(x,y) -> do 
    t <- nExp Tup ;
    k <- nExp Tup ; 
    x' <- nInt x; 
    y' <- nInt y; 
    z <- nRndFlt;
    return (t [(k [x', y']), z]) ) indcs
  r <- nExp Rel
  return (r ts)

nGraph :: State IdxSet Expr
nGraph = do
  -- inputs
  let grel = (App 0 (Var 1 15 "genmatrix") (Lit 2 (I 100)))
  arel <- fExpr grel
  brel <- fExpr grel
--  arel <- nGrid2d 1 1
--  brel <- nGrid2d 1 1

  -- join inputs
  let xyz = IdxTup 0 [IdxTup 1 [IdxLeaf 2 0 "x", IdxLeaf 3 1 "y"], IdxLeaf 4 2 "z"]
  let vy = Var 5 1 "y"
  let vx = Var 5 0 "x"
  jf1 <- fExpr (Fun 6 xyz vy)
  jf2 <- fExpr (Fun 6 xyz vx)
  join <- fExpr (App 0 (Var 1 2 "ejoin") (Tup 2 [jf1, jf2, arel, brel]))

  -- map value
  let mvfi = IdxTup 0 [IdxTup 1 [IdxTup 2 [IdxLeaf 3 0 "ax", IdxLeaf 4 1 "ay"], 
                                 IdxTup 5 [IdxLeaf 6 2 "bx", IdxLeaf 7 3 "by"]],
                       IdxTup 8 [IdxLeaf 9 4 "az", 
                                 IdxLeaf 10 5 "bz"]]
  let mvfe = Tup 11 [Var 12 0 "ax", Var 13 3 "by", 
                    (App 14 (Var 15 10 "mulf") (Tup 16 [(Var 17 4 "az"), (Var 18 5 "bz")]))]
  mvf <- fExpr (Fun 19 mvfi mvfe)
 -- mapv <- fExpr (App 0 (Var 1 1 "map-val") (Tup 2 [mvf, join]))

  -- map key
 -- mkf <- fExpr (Fun 0 (IdxNub 1) (Var 2 14 "every"))
  mkf <- fExpr (Fun 0 (IdxNub 1) (App 3 (Var 2 14 "every") (Lit 4 (NullVal))))
 -- mapk <- fExpr (App 0 (Var 1 0 "map-key") (Tup 2 [mkf, mapv])) 
  mapf <- fExpr (App 0 (Var 1 1 "map") (Tup 2 [mkf,mvf,join]))

  -- group reduce
  let gri = IdxTup 0 [IdxNub 1, IdxTup 2 [IdxLeaf 3 0 "x", IdxLeaf 4 1 "y", IdxLeaf 5 2 "z"]]
  gkf <- fExpr (Fun 6 gri (Tup 7 [Var 8 0 "x", Var 9 1 "y"]))
  gpf <- fExpr (Fun 6 gri (Var 7 2 "z"))
 -- gred <- fExpr (App 0 (Var 1 3 "greduce") (Tup 2 [gkf, gpf, (Var 3 8 "addf"), mapk]))
  gred <- fExpr (App 0 (Var 1 3 "greduce") (Tup 2 [gkf, gpf, (Var 3 8 "addf"), mapf]))


  return gred

-- |Initial index we think is safe to use for demo graph generation
--initidx = length globalTypes
-- |Initial indices we think are safe to use for demo graph generation
--initidxs = [initidx, initidx, initidx]

-- |Creates a new demo graph, in this case a matrix multiply
makeDemoGraph = nGraph --evalState nGraph initidxs

-- Todo 3 - write method to build exp alg choice map, and constraint list from program tree
  
