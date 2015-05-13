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
module Compiler.Front.Preprocess (preprocessExpr, unrollTupLets, propagateVarsTupsFuns, newVarNames, expandTupVals, showLetExprs, encapFunVars, propLets, constTrueFun, emptyExprEnv) where

import Compiler.Front.Common (delimList, lookupIntOrError, fromIntMap, toIntMap, vids, eids, ShowP(..))
import Compiler.Front.Indices (Idx, IdxSet, IdxMonad, newidST)
import Compiler.Front.ExprTree (Expr(..), IdxTree(..), Val(..), newExprId, newExprVarId, getExprId, getIdxTreeId)
import Compiler.Front.ExprTree (replaceExprIdsOnly, countExprs, isAppExpr,  removeEmptyTups)

--import Compiler.Types.TypeAssignment (getTupleAccessorFun, TyTerm, TyScheme)
--import Compiler.Types.TermLanguage (Term(Term), FunctionToken(TupTok, FunTok), Scheme(Scheme))
import Compiler.Types2.TypeAssignment (getTupleAccessorFun, TyTerm, TyScheme)
import Compiler.Types2.TermLanguage (Term(Term), FunctionToken(TupTok, FunTok), Scheme(Scheme), stripTermLabels)

import Data.Map.Strict as Data.Map (Map, unions, union, intersection, empty, singleton, (!))
import qualified Data.Map.Strict as Data.Map (lookup, toList, partition, null)
import qualified Data.IntMap.Strict as IM
import Data.Maybe (catMaybes, fromMaybe)
import Data.Foldable (foldlM)
import Control.Monad.State.Strict (StateT, mapM, runStateT, evalStateT, gets, modify, lift)
import Debug.Trace (trace)

-- |preprocessExpr expr. Applies all code tidying transformations to
-- |an expression.
{-preprocessExpr :: Monad m => Expr -> StateT IdxSet m Expr
--tidyCode expr = unrollTupLets expr'
--  where expr' = newVarNames empty expr
preprocessExpr expr = do
  --expr' <- propLets tupVarOrNonStrLit empty expr
  expr' <- propLets funTupOrVarFun empty expr -- $ newVarNames empty expr
  --expr'' <- unrollTupLets expr'
  --let expr''' = newVarNames empty expr'
  return expr'-}

-- |preprocessExpr expr. Applies all code tidying transformations to
-- |an expression.
preprocessExpr :: Monad m => [(String, Idx)] -> Expr -> StateT IdxSet m Expr
preprocessExpr varIds expr = do
  -- convert if's to fun apps
  expr' <- convertIfs varIds expr
  -- start preprocess loop
  preprocessExprLoop expr'

-- |preprocessExprLoop expr. Applies code tidying transformations to
-- |an expression.
preprocessExprLoop :: Monad m => Expr -> StateT IdxSet m Expr
preprocessExprLoop expr = do
  -- expand immediate applications of lambda terms to let expressions
  let expr' = applyFuns expr
  -- propagate let bound functions, tuples, and vars to leaves
  expr'' <- propLets funTupOrVarFun empty expr'
  -- count how many immediate applications of lambda terms there are now
  let numLambdaApps = countExprs isLambdaApp expr''
  -- if more than zero then repeat
  if numLambdaApps > 0 then preprocessExprLoop expr'' else return $ removeEmptyTups expr''
  
type VarNameEnv = Map Idx String

newVarName :: Idx -> String -> String
newVarName vid name = name ++ "_" ++ (show vid)

-- |newIdTreeVarNames creates and returns new var names for the 
-- |id pattern tree and returns the new idtree and environment.
newTreeVarNames :: IdxTree -> (VarNameEnv, IdxTree)
newTreeVarNames it = case it of
  (IdxTup i l) -> (unions envs, IdxTup i l')
    where (envs, l') = unzip $ map newTreeVarNames l
  (IdxLeaf i vid s) -> (singleton vid s', (IdxLeaf i vid s'))
    where s' = newVarName vid s
  other -> (empty, other)

-- |newVarNames takes a map of new var names and an expression
-- |and returns the same expression with new string names for
-- |the vars.
newVarNames :: VarNameEnv -> Expr -> Expr
newVarNames env expr = case expr of
  (Var i vid s)  -> case Data.Map.lookup vid env of 
    Just s' -> (Var i vid s')
    Nothing -> expr
  (Tup i l)      -> Tup i $ map (newVarNames env) l
  (Rel i l)      -> Rel i $ map (newVarNames env) l
  (App i fe ae)  -> App i (newVarNames env fe) (newVarNames env ae)
  (If i pe te ee)  -> If i (newVarNames env pe) (newVarNames env te) (newVarNames env ee)
  (Fun i it exp) -> Fun i it' (newVarNames (env' `union` env) exp)
    where (env', it') = newTreeVarNames it
  (Let i it be exp) -> Let i it' (newVarNames env be) (newVarNames (env' `union` env) exp)
    where (env', it') = newTreeVarNames it
  other         -> other
 
type ExprEnv = Map Idx Expr

emptyExprEnv = Data.Map.empty

-- |propLetsInIt takes an idx tree and an expression and returns 
-- |a map of variable ids to expressions if the expression can be
-- |broken down into a tuple tree that matches the idx tree, or
-- |Nothing otherwise 
propLetsInIt :: (IdxTree, Expr) -> Maybe ExprEnv
propLetsInIt (it, exp) = case (it,exp) of
  (IdxNub i, _)            -> Just empty 
  (IdxLeaf i vid s, expr) -> Just $ singleton vid expr
  (IdxTup i l, Tup i' l') | length l == length l' ->  ret
    where l'' = catMaybes $ map propLetsInIt $ zip l l'
          ret = if length l == length l'' then Just $ unions l'' else Nothing
  _                       -> Nothing 

-- |constTrueFun takes an expression and always returns true.
constTrueFun :: Expr -> Bool
constTrueFun _ = True

-- |funTupLitOrVarFun takes an expression and returns
-- |true if it is a function abstraction, tuple, var
-- |or literal.
funTupOrVarFun :: Expr -> Bool
funTupOrVarFun expr = case expr of 
  (Fun _ _ _) -> True
  (Tup _ _)   -> True
  (Var _ _ _) -> True
  (Lit _ val) -> case val of
    S _ -> False -- all lits that aren't strings get propagated down...
    _   -> True
  _           -> False

-- |tupVarOrNonStrLit takes an expression and returns
-- |true if it is a tuple, var
-- |or non string literal.
tupVarOrNonStrLit :: Expr -> Bool
tupVarOrNonStrLit expr = case expr of 
  -- (Fun _ _ _) -> True
  (Tup _ _)   -> True
  (Var _ _ _) -> True
--  (Lit _ _)   -> True -- any literal
  (Lit _ val) -> case val of
    S _ -> False -- all lits that aren't strings get propagated down...
    _   -> True
  _           -> False

-- |envToLet takes an expression environment and an IdxTree
-- |and returns those leaves of the IdxTree for which the
-- |var appears in the env, and the corresponding expressions
envToLet :: ExprEnv -> IdxTree -> ([IdxTree], [Expr])
envToLet env it = case it of
  (IdxNub _) -> ([], [])  
  (IdxTup i l) -> (concat its, concat exps)
    where l' = map (envToLet env) l
          (its, exps) = unzip l'
  (IdxLeaf i vi name) -> case Data.Map.lookup vi env of
    (Just boundExpr) -> ([it], [boundExpr]) 
    Nothing          -> ([], [])

-- |propLets propagates bindings made at let expressions 
-- | (that match the filter predicate) down
-- |to the leaves of an expression, when they can be, thus
-- |eliminating uneccesary let expressions from the program
propLets :: Monad m => (Expr -> Bool) -> ExprEnv -> Expr -> StateT IdxSet m Expr
propLets expFilter env expr = case expr of 
  -- see if this var is in map
  (Var i vid s) -> case Data.Map.lookup vid env of
    Just expr' -> do 
      -- freshen eids for this instance
      expr'' <- evalStateT (replaceExprIdsOnly (\_ -> True) expr') Data.Map.empty
      return expr''
    Nothing    -> return expr
  -- let expression
  (Let i it be exp) -> do
    be' <- propLets expFilter env be
    let env' = propLetsInIt (it, be')
    case env' of
    -- partition the bindings into those to propagate, and those not to
      (Just env'') -> case (Data.Map.null tenv, Data.Map.null fenv) of
        -- all propagated
          (False, True)  -> propLets expFilter (tenv `union` env) {- trace ("allProp: " ++ (show expr) ++ "\n") $-} exp
        -- some of each
          (False, False) -> do
            let (its, exps) = envToLet fenv it
            let itsI = getIdxTreeId it
            let beI  = getExprId be'
            ie' <- propLets expFilter (tenv `union` env) exp
            return (Let i (IdxTup itsI its) (Tup beI exps) {- trace ("someProp: " ++ (show expr) ++ "\n") $-} ie')
          -- none propagated
          (True, False)  -> do 
            exp' <- propLets expFilter env {-trace ("noneProp: " ++ (show expr) ++ "\n") $ -} exp
            return (Let i it be' exp') 
          -- nothing to bind!
          (True, True)   -> error $ "propLets both partitions are empty: " ++ (showP expr) ++ "\n" ++ (show env) ++ "\n\n" ++ (show env') 
        where (tenv, fenv) = Data.Map.partition expFilter env''
      (Nothing)    -> do 
        exp' <- (propLets expFilter env exp)
        return (Let i it be' exp')
  -- function expression
  (Fun i it exp) -> do 
    exp' <- propLets expFilter env exp
    return $ Fun i it exp'
  -- recurse
  (Tup i l)      -> do
    l' <-  mapM (propLets expFilter env) l
    return $ Tup i l'
  (Rel i l)      -> do 
    l' <- mapM (propLets expFilter env) l
    return $ Rel i l'
  (App i fe ae)  -> do
    fe' <- (propLets expFilter env fe)
    ae' <- (propLets expFilter env ae) 
    return $ App i fe' ae'  
  (If i pe te ee)  -> do
    pe' <- (propLets expFilter env pe)
    te' <- (propLets expFilter env te)
    ee' <- (propLets expFilter env ee)
    return $ If i pe' te' ee'
  other -> return other

-- |propagateVarsTupsFuns takes an expression and propagates all
-- |let bound lambdas, tuples and vars down to the leaves of the AST
-- |(thus duplicating them where neccessary).
propagateVarsTupsFuns :: Monad m => Expr -> StateT IdxSet m Expr
propagateVarsTupsFuns expr = propLets funTupOrVarFun empty expr 

-- |retLetAccessorsForIt takes an expression and an idx tree
-- |and returns a list of identifiers (and lists of tuple accessor int pairs
-- |ordered by deepest nesting to shallowest) and expressions they are bound to.
retLetAccessorsForIt :: Expr -> (IdxTree, [(Int,Int)]) -> [(((Idx, String), [(Int, Int)]), Expr)]
retLetAccessorsForIt expr (it,path) = case it of
  (IdxNub i)        -> []
  (IdxTup i l)      -> concat l'
    where tupLength = length l
          l' = map (retLetAccessorsForIt expr) $ zip l [((tupLength,off):path) | off <- [1..]]
  (IdxLeaf i vid name) -> [(((vid, name), path), expr)]

-- |tuplePathToAccessors takes a list of int pairs which are 
-- |tuple lengths and offsets, and an expression, and returns a
-- |an expression which applies the equivalent tuple accessor functions
-- |to the input expression.
tuplePathToAccessors :: Monad m => [(Int,Int)] -> Expr -> StateT IdxSet m Expr
tuplePathToAccessors []    expr = return expr
tuplePathToAccessors ((tupSize,tupOff):r) expr = do
  eid1 <- newExprId
  eid2 <- newExprId
  let (name, vid) = getTupleAccessorFun tupSize tupOff
  let expr' = App eid1 (Var eid2 vid name) expr
  tuplePathToAccessors r expr'

-- |retLetsInIt breaks down an idxtree and expression returning
-- |a list of individual identifier bindings, using tuple accessor
-- |function applications where neccessary.
retLetsInIt :: Monad m => (IdxTree, Expr) -> StateT IdxSet m [((Idx, String), Expr)]
retLetsInIt (it,exp) = case (it,exp) of
  (IdxNub i, _)       -> return []
  (IdxTup i l, Tup i' l') | length l == length l' -> do 
    l'' <- mapM retLetsInIt $ (zip l l')
    return $ concat l''
  (IdxLeaf i vid name, expr) -> return [((vid, name), expr)]
  _                       -> do
    let l' = retLetAccessorsForIt exp (it, [])
    l'' <- mapM (\(((vid, name),path),be) -> do be' <- tuplePathToAccessors path be; return ((vid, name), be')) l'
    return l''

-- |newLet takes an 'in' expr, var id, and binding expression
-- |and returns a new Let expression with new expression ids.
newLet :: Monad m => Expr -> ((Idx, String),Expr) -> StateT IdxSet m Expr
newLet inExp ((vid, name),exp) = do
  eid1 <- newExprId 
  eid2 <- newExprId 
  --let vname = "genvar" ++ (show vid)
  return (Let eid1 (IdxLeaf eid2 vid name) exp inExp)

-- |unrollTupLet takes a Let expression that takes more than 
-- |a single identifier and expands it out into a sequence of
-- |nested lets (using tuple accessor functions if neccessary).
unrollTupLet :: Monad m => IdxTree -> Expr -> Expr -> StateT IdxSet m Expr
unrollTupLet it be ie = do
  letL <- retLetsInIt (it,be)
  lets <- foldlM newLet ie letL
  return lets

-- |unrollTupLets takes an expression and expands all Let
-- |expressions with tuple Idx trees to a sequence of nested
-- |Lets - one for each identifier in the tree.
unrollTupLets :: Monad m => Expr -> StateT IdxSet m Expr
unrollTupLets expr = case expr of
  (Let i it be ie) -> do
    ie' <- unrollTupLets ie
    be' <- unrollTupLets be
    lets <- unrollTupLet it be' ie'
    return lets
  (Tup i l) -> do
    l' <- mapM unrollTupLets l
    return (Tup i l')  
  (Rel i l) -> do
    l' <- mapM unrollTupLets l
    return (Rel i l') 
  (If i pe te ee) -> do
    pe' <- unrollTupLets pe
    te' <- unrollTupLets te
    ee' <- unrollTupLets ee
    return (If i pe' te' ee')
  (Fun i it exp) -> do
    exp' <- unrollTupLets exp
    return (Fun i it exp')
  (App i fe ae) -> do
    fe' <- unrollTupLets fe
    ae' <- unrollTupLets ae
    return (App i fe' ae')
  other -> return other

-- need to get rid of let expressions that just bind one indentifier to another
-- (i.e. rhs of let must always be non-trivial expression - i.e. function application
-- or if etc...)
-- also lambdas and tuple expressions need to be moved down to leaves.
-- so if we encounter a let with: an identifier, lambda, or tuple of rhs we 
-- add it to the environement and substitute it in later.

-- |showLetExprs is a pretty print function for
-- |expressions that are mainly lists of let expressions.
showLetExprs :: String -> Expr -> String
showLetExprs pad expr = case expr of
  (Let i it be ie) -> 
    pad ++ "let " ++ (show it) ++ " = \n" ++ (showLetExprs (pad ++ "  ") be) ++ " in\n"
        ++ (showLetExprs pad ie) 
  other -> pad ++ (show other)

-- |checkDisjoint checks that the two maps are disjoint before
-- |computing their union. OPTIMIZE: make id.
checkDisjointUnion :: (Show a, Show b, Ord a) => Map a b -> Map a b -> Map a b
checkDisjointUnion a b = case Data.Map.null $ a `intersection` b of
  True  -> a `union` b
  False -> error $ "checkDisjointUnion - maps are not disjoint: " ++ (show a) ++ "\n" ++ (show b)

-- |newTupIdx takes a type (which may be a tuple) and
-- |returns an idxtree and tuple expression to match the shape
-- |of the type
newTupIdx :: Monad m => TyTerm -> String -> StateT IdxSet m (IdxTree, Expr)
newTupIdx ty name = case stripTermLabels ty of 
  -- recurse on tuple types
  (Term TupTok l) -> do
    l' <- mapM (\(t,i) -> newTupIdx t (name ++ (show i))) $ zip l [1..]
    let (its, exprs) = unzip l'
    eid1 <- newExprId
    eid2 <- newExprId  
    return (IdxTup eid1 its, Tup eid2 exprs)
  -- return a leaf
  other           -> do 
    eid1 <- newExprId
    eid2 <- newExprId
    vid <- newExprVarId
    return (IdxLeaf eid1 vid name, Var eid2 vid name)

-- |expandTupIdxs finds ids in the idxtree with tuple types, and expands them to 
-- |become one 
expandTupIdxs :: Monad m => (TyTerm, IdxTree) -> StateT IdxSet m (IdxTree, Map Idx Expr)
expandTupIdxs (ty, it) = case it of
  -- discard nubs
  (IdxNub _)   -> return (it, Data.Map.empty)
  -- recurse over idx tuples
  (IdxTup i tupL) -> case stripTermLabels ty of 
    (Term TupTok tyL) | length tupL == length tyL -> do    
      l' <- mapM expandTupIdxs $ zip tyL tupL
      let (itL, mapL) = unzip l'
      let mapS = unions mapL
      return (IdxTup i itL, mapS)
    other -> error $ "expandTupIdxs: Type not same shape as IdxTup pattern: " ++ (show ty) ++ " /= " ++ (show it)
  -- expand leaves of tuple type
  (IdxLeaf i vid name) -> case stripTermLabels ty of 
    (Term TupTok _) -> do
      (it', expr') <- newTupIdx ty name
      return (it', Data.Map.singleton vid expr')
    other -> return (it, Data.Map.empty)

-- |checkHasType looks up a type in a type scheme environment
-- |and returns it if found, and throws an error otherwise.
checkHasType :: Map Idx TyScheme -> Idx -> TyTerm
checkHasType tyEnv eid = case Data.Map.lookup eid tyEnv of
  (Just (Scheme _ ty)) -> ty
  (Nothing) -> error $ "expandTupVals: Can't find type for " ++ (show eid) ++ " in type env " ++ (show tyEnv) 

-- |expandTupVals takes the types of all expressions in the AST
-- |and replaces all identifiers of tuple type, with tuple expressions of
-- |other identifiers, such that identifiers only ever refer to single values,
-- |not tuples.
expandTupVals :: Monad m => Map Idx TyScheme -> Map Idx Expr -> Expr -> StateT IdxSet m Expr
expandTupVals tyEnv tupEnv expr = case expr of
    -- analyse bindings
    (Fun i it e) -> do
      let ty = checkHasType tyEnv (getIdxTreeId it)
      (it', tupEnv') <- expandTupIdxs (ty, it)
      e' <- expandTupVals tyEnv (tupEnv' `checkDisjointUnion` tupEnv) e
      return (Fun i it' e')
    (Let i it be ie) -> do
      be' <- recur be
      let ty = checkHasType tyEnv (getIdxTreeId it)
      (it', tupEnv') <- expandTupIdxs (ty, it)
      ie' <- expandTupVals tyEnv (tupEnv' `checkDisjointUnion` tupEnv) ie
      return (Let i it' be' ie')
    -- expand var to tuple of vars
    (Var i vid name) -> case Data.Map.lookup vid tupEnv of
      (Just expr') -> do 
        -- create new eids for this use of the expr
        expr'' <- evalStateT (replaceExprIdsOnly (\_ -> True) expr') Data.Map.empty
        return expr''
      (Nothing)    -> return expr
    -- recursive cases
    (Tup i l) -> do 
      l' <- mapM recur l
      return $ Tup i l'
    (Rel i l) -> do 
      l' <- mapM recur l
      return $ Rel i l'
    (App i fe ae) -> do
      fe' <- recur fe
      ae' <- recur ae
      return $ App i fe' ae'
    (If i pe te ee) -> do
      pe' <- recur pe
      te' <- recur te
      ee' <- recur ee
      return $ If i pe' te' ee'
    other -> return other
  where recur = expandTupVals tyEnv tupEnv

-- |applyFuns expr. Assuming have already propagates lambdas to leaves,
-- |applies all applications of lambda expressions by converting them
-- |to let expressions.
applyFuns :: Expr -> Expr
applyFuns expr = case expr of
  (App i1 (Fun i2 it ie) be) -> (Let i1 it be ie)
  (App i fe ae) -> App i (applyFuns fe) (applyFuns ae)
  (Fun i it e) -> (Fun i it $ applyFuns e)
  (Tup i l) -> Tup i $ map applyFuns l
  (Rel i l) -> Rel i $ map applyFuns l
  (If i pe te ee) -> If i (applyFuns pe) (applyFuns te) (applyFuns ee)
  (Let i it be ie) -> Let i it (applyFuns be) (applyFuns ie)
  other -> other

-- |isLambdaApp expr. Returns true iff the expression if an
-- |application of a lambda term.
isLambdaApp :: Expr -> Bool
isLambdaApp (App _ (Fun _ _ _) _) = True
isLambdaApp _ = False

-- |encapFunVarsM parentExpr expr. Returns expr where all occurances of vars with function
-- |types that are not immediately applied (direct children of App exprs) and encapsulated
-- |in simple lambda terms e.g. (\x -> v x)
encapFunVarsM :: Monad m => Expr -> Expr -> StateT (IM.IntMap TyScheme) (IdxMonad m) Expr
encapFunVarsM parent expr = do
  let rec = encapFunVarsM expr
  case expr of
    -- recursive cases
    (App i fe ae) -> do 
      fe' <- rec fe
      ae' <- rec ae
      return $ App i fe' ae'
    (Fun i it e) -> do
      e' <- rec e
      return (Fun i it e')
    (Tup i l) -> do
      l' <- mapM rec l
      return $ Tup i l'
    (Rel i l) -> do
      l' <- mapM rec l
      return $ Rel i l'
    (If i pe te ee) -> do
      pe' <- rec pe
      te' <- rec te
      ee' <- rec ee 
      return $ If i pe' te' ee'
    (Let i it be ie) -> do
      be' <- rec be
      ie' <- rec ie
      return $ Let i it be' ie'
    -- base cases
    (Var i funVid vname) | not $ isAppExpr parent -> do -- is not being applied/or an app argument  
      -- check its type
      tyScheme@(Scheme tvars ty) <- gets (lookupIntOrError ("Preprocess:encapFunVars: can't get type for expr " ++ (show expr)) i)
      case stripTermLabels ty of
        -- has fun type
        (Term FunTok [inTy, outTy]) | length tvars == 0 -> do
          -- encapsulate in new lambda term
          varVid <- lift $ newidST vids
          varEid <- lift $ newidST eids
          let varName = ("v" ++ (show varVid))
          let varExpr = Var varEid varVid varName
          appEid <- lift $ newidST eids
          let appExpr = App appEid expr varExpr
          patEid <- lift $ newidST eids
          let patExpr = IdxLeaf patEid varVid varName
          lamEid <- lift $ newidST eids
          let lamExpr = Fun lamEid patExpr appExpr
          -- add types for term
          let types' = IM.fromList [
                 (varEid, Scheme [] inTy),
                 (appEid, Scheme [] outTy),
                 (patEid, Scheme [] inTy),
                 (lamEid, tyScheme) 
               ]
          modify (\types -> IM.union types types')
          -- return this
          return lamExpr
        -- scheme still has vars
        (Term FunTok _) -> error $ "Preprocess:encapFunVarsM: fun var is a type scheme, not a type!\n" ++ (show tyScheme)
        -- has other type
        _ -> return expr
    -- lits
    other -> return other

-- |encapFunVarsM types expr. Returns expr where all occurances of vars with function
-- |types that are not immediately applied (direct children of App exprs) and encapsulated
-- |in simple lambda terms e.g. (\x -> v x)
encapFunVars :: Monad m => [(Idx, TyScheme)] -> Expr -> IdxMonad m (Expr, [(Idx, TyScheme)])
encapFunVars types expr = do
  (expr', types') <- runStateT (encapFunVarsM expr expr) (IM.fromList types)
  return (expr', IM.toList types')

-- |convertIfs expr. Traverses AST converting all "if" expressions to 
-- |function applications of ifFun.
convertIfs :: Monad m => [(String, Idx)] -> Expr -> IdxMonad m Expr
convertIfs varIds expr = case expr of
    -- convert if
    (If i pe te ee) -> do
      -- apply to children
      pe' <- recur pe
      te' <- recur te
      ee' <- recur ee
      -- make ifFun app
      let v1 = fromMaybe (error $ "Front:Preprocess:convertIfs: ifFun's vid is missing from var ids.") (lookup "ifFun" varIds)
      es@[e1,e2,e3,e4,e5,e6,e7] <- mapM (\_ -> newidST eids) [1..7]
      let ifFun = (Var e1 v1 "ifFun")
      let thenF = (Fun e2 (IdxNub e3) te')
      let elseF = (Fun e4 (IdxNub e5) ee')
      let argTup = (Tup e6 [pe', thenF, elseF])
      let ifApp = (App e7 ifFun argTup) 
      return $ trace ("converted if " ++ (show expr) ++ "\nto\n" ++ (show ifApp) ++ " with vid " ++ (show v1) ++ " and " ++ (show es) ++ "\n\n") $ ifApp
    -- other cases
    (Let i it be ie) -> do
      ie' <- recur ie
      be' <- recur be
      return (Let i it be' ie')
    (Tup i l) -> do
      l' <- mapM recur l
      case l' of
        [] -> error $ "Preprocess:convertIfs:empty tuple!"
        [v] -> return v
        _ -> return (Tup i l')  
    (Rel i l) -> do
      l' <- mapM recur l
      return (Rel i l') 
    (Fun i it exp) -> do
      exp' <- recur exp
      return (Fun i it exp')
    (App i fe ae) -> do
      fe' <- recur fe
      ae' <- recur ae
      return (App i fe' ae')
    other -> return other
  where recur = convertIfs varIds

