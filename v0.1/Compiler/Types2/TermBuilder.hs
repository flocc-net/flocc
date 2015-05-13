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
module Compiler.Types2.TermBuilder (buildTermsForExpr, performConstraintAnalysis, scm, tup, fun, vara, varb, varc, vard, vare, varf, varg, varh, vari, varj, vark, varl, initTermEnvInState, ExpLbl(..), FuncTerm, FuncEnv, FuncConstr, FuncScheme,
  Substs, composeSubsts, nullSubsts, applySubstsToTerm, applySubstsToEnv, applySubstsToConstrs,
  InferenceMonad, InferenceFunction, inferTerms, inferNewTerms, runTermInferencer, runNewTermInferencer,
  inferTermsFoldF, inferEqTermsFoldF, addAConstraint,
  buildForIdxTree) where

-- Helper functions for building term environments and constraint lists in various term languages
-- for expr trees
-- ------------------------ 

import Compiler.Front.Indices (Idx, IdxSet)
import Compiler.Types2.TermLanguage
import Compiler.Front.ExprTree hiding (Var)
import qualified Compiler.Front.ExprTree as ExprTree (Expr(Var))
import Compiler.Front.Common

import Control.Monad.State.Strict ( lift, StateT, runStateT, get, modify )
import Data.Foldable (foldlM)
import Data.List (nub, isPrefixOf)
import Debug.Trace (trace)

trace' = if debug then trace else \_ -> id

-- |Trace function for debugging build function when vars are encountered
trcVarTermBuilding :: (Show a, Show b) => (a,b) -> c -> c
--trcVarTermBuilding = tracerEx3 "Building var term: " (\(n,t) -> (show n) ++ ": " ++ (show t))
trcVarTermBuilding _ = id 

-- |Trace function displaying new envs when entering scopes
trcScopeBuilding :: (Show a) => [a] -> b -> b
--trcScopeBuilding = tracerEx3 "Building new scope vars: \n    " (\l -> delimList "\n    " $ map show l)
trcScopeBuilding _ = id

-- |Trace function displaying schemes in varEnv at each var use, and the resulting 
-- |instantiations
trcSchemeInstantiation :: Show t => Idx -> FuncScheme t -> FuncTerm t -> a -> a
--trcSchemeInstantiation varId scheme term = trace ("SchemeInst: V" ++ (show varId) ++
--  ": " ++ (showFunctionScheme scheme) ++ " => " ++ (showFunctionTerm term) ++ "\n")
trcSchemeInstantiation _ _ _ = id

-- |Trace function displaying result of build function
{-trcBuildResult :: (Show t, Show c) => (Expr,TermEnv t,c) -> d -> d
trcBuildResult = tracerEx3 "Build result: " (\(exp,env,cl) -> 
  "\n\n Expression: " ++ (show exp) ++ 
  "\n\n Environment: " ++ (show env) ++
  "\n\n Constraints: " ++ (show cl) ++ 
  "\n\n Expr with terms: " ++ (showExprTree env showTermFromEnv 0 exp)) -}
trcBuildResult _ = id

data ExpLbl =
    ProdLbl Idx
  | IfLbl Idx
  --  NonNull
--   VarLbl Idx
--   ConsLbl Idx
--   FunLbl Idx
  deriving (Eq, Ord, Show, Read)

{-instance Show ExpLbl where
  show (ProdLbl i) = "p" ++ (show i)
  show (IfLbl i) = "if" ++ (show i)-}

instance ShowP ExpLbl where
  showP (ProdLbl i) = "p" ++ (show i)
  showP (IfLbl i) = "if" ++ (show i)

type FuncTerm t = Term ExpLbl (FunctionToken t)
type FuncEnv t = TermEnv ExpLbl (FunctionToken t)
type FuncConstr t = Constr (FuncTerm t)
type FuncScheme t = Scheme ExpLbl (FunctionToken t)

getVid :: Show t => FuncTerm t -> Idx
getVid (Var i) = i
getVid (LVar _ i) = i
getVid expr    = error $ (show expr) ++ " is not a Var term, scm only takes Vars"

scm :: Show t => [FuncTerm t] -> FuncTerm t -> FuncScheme t
scm vlist term = Scheme (nub $ map getVid vlist) term

tup :: [FuncTerm t] -> FuncTerm t
tup l = Term TupTok l

fun :: FuncTerm t -> FuncTerm t -> FuncTerm t
fun a b = Term FunTok [a, b]

vara :: FuncTerm t
vara = (Var 0)

varb :: FuncTerm t
varb = (Var 1)

varc :: FuncTerm t
varc = (Var 2)

vard :: FuncTerm t
vard = (Var 3)

vare :: FuncTerm t
vare = (Var 4)

varf :: FuncTerm t
varf = (Var 5)

varg :: FuncTerm t
varg = (Var 6)

varh :: FuncTerm t
varh = (Var 7)

vari :: FuncTerm t
vari = (Var 8)

varj :: FuncTerm t
varj = (Var 9)

vark :: FuncTerm t
vark = (Var 10)

varl :: FuncTerm t
varl = (Var 11)

-- |Initialize the current level of the TermEnvStack using this IdxTree pattern
initTermEnvInState :: Monad a => Term l t -> IdxTree -> StateT (TermEnvStack l t) a ()
initTermEnvInState term it = case it of
  (IdxNub i) -> do 
    return ()
  (IdxLeaf i vi s) -> do
    addTermToStackInState term vi
    return ()
  (IdxTup i l) -> do
    mapM (initTermEnvInState term) l
    return ()

buildForIdxTree :: Monad a => IdxTree -> StateT (FuncEnv t) (StateT IdxSet a) (FuncEnv t, FuncTerm t)
buildForIdxTree it = case it of
  (IdxNub i) -> do
    v <- lift $ newTermVarFromState
    let v' = {-labelTerm (ProdLbl i)-} v
    bindTermInState (Scheme [] v') i
    return (emptyTermEnv, v')
  (IdxLeaf i vi s) -> do
    v <- lift $ newTermVarFromState
    let v' = {-labelTerm (ProdLbl i)-} v
    bindTermInState (Scheme [] v') i
    return (addTermToEnv emptyTermEnv (Scheme [] v') vi, v')
  (IdxTup i l) -> do
    l' <- mapM buildForIdxTree l
    if length l == 1 || length l' == 1 then error $ "buildForIdxTree: idxtup with only 1 element! " ++ (show it) else return ()
    let (venvl, tl) = unzip l'
    let term = {-labelTerm (ProdLbl i) $-} tup tl
    v <- bindTermInState (Scheme [] term) i
    return (concatTermEnvs venvl, term)

-- |Instead of creating new vars for the identifiers, here we decompose the
-- |term given, assigning its components to the various leaves of the IdxTree
buildForLetIdxTree :: (Monad m, Show t, ShowP t) => 
  FuncEnv t ->
  IdxTree ->
  FuncTerm t ->
  StateT (FuncEnv t) (StateT IdxSet m) (FuncEnv t)
buildForLetIdxTree env it term = let scheme = generalizeTerm env (labelTerm (ProdLbl $ getIdxTreeId it) term) in
  case it of
  -- an underscore
  (IdxNub i) -> do
     term' <- bindTermInState scheme i
     return emptyTermEnv
  -- an identifier
  (IdxLeaf i vi s) -> do
     term' <- bindTermInState scheme i
     return (addTermToEnv emptyTermEnv term' vi)
  -- a tuple of identifiers
  (IdxTup i l) -> case term of
    (LTerm _ TupTok l') -> buildForLetIdxTree env it (Term TupTok l')
    (Term TupTok l') | length l == length l' -> do
      term' <- bindTermInState scheme i
      let ls = zip l l'
      envl <- mapM (\(id,tm) -> buildForLetIdxTree env id tm) ls
      return (concatTermEnvs envl)
    tm -> error $ "Error building scheme env for let expression. Idx tuple " ++ (showP it) ++
                  " does not match term " ++ (showP term)   

-- |Helper function for building term environments for expr trees. May be called from an 'overriding' function (with the overriding
-- |function passed as the third argument so that control can be passed back to it in the recursive case).
buildTermsForExpr :: (Show t, ShowP t, Eq t, Monad a) => 
  FuncEnv t -> 
  Expr -> 
  (FuncEnv t -> Expr -> StateT (FuncEnv t) (StateT (IdxSet) a) ([FuncConstr t], FuncTerm t)) 
    -> StateT (FuncEnv t) (StateT (IdxSet) a) ([FuncConstr t], FuncTerm t)
buildTermsForExpr varEnv exp bfun = case exp of
  (Lit i vl) -> do -- new term var
    v <- lift $ newTermVarFromState
    let v' = labelTerm (ProdLbl i) v
    bindTermInState (Scheme [] v') i
    return ([], v')
--  (ExprTree.Var i vi s) -> do -- fetch from env
--    declV <- case lookupTermMaybe varEnv vi of
--      (Just dv) -> if isFuncTerm dv -- POTENTIAL PROBLEM: there are circumstances where we can't tell if its a function term.
--         then do -- functions should be renamed per use
--           dv' <- lift $ renewTermVarIds dv
--           return dv' 
--         else return dv -- variables should not
--      Nothing -> error $ "var " ++ (show vi) ++ " " ++ s ++ 
--                         "is missing from the dependence term variable environment"
--    v <- bindTermInState declV i
--    return $ trcVarTermBuilding (s, declV) $ ([], v)
  (ExprTree.Var i vi s) -> case lookupTermMaybe varEnv vi of
    (Just scheme) -> do 
      term <- lift $ instantiateScheme scheme
      let term' = labelTerm (ProdLbl i) term
      bindTermInState (Scheme [] term') i
      return $ trcSchemeInstantiation vi scheme term' $ ([], term')
      --return $ trcVarTermBuilding (s, term) $ ([], term)
    Nothing -> error $ "Unbound variable var " ++ (show vi) ++ " " ++ s ++
                       " when building terms for expression."
  (Tup i l) -> do -- new tup term
    l' <- mapM (bfun varEnv) l
    let (cl,tl) = unzip l'
    let term = labelTerm (ProdLbl i) $ tup tl
    bindTermInState (Scheme [] term) i
    return (concat cl, term)
  (Rel i l) -> do -- new term var
    v <- lift $ newTermVarFromState
    let v' = labelTerm (ProdLbl i) v
    bindTermInState (Scheme [] v') i
    l' <- mapM (bfun varEnv) l
    let (cl,tl) = unzip l'
    return ((concat cl), v')
  (Fun i it b) -> do -- new fun term
    (newVarEnv, t1) <- buildForIdxTree it
    (cl, t2) <- trcScopeBuilding newVarEnv $ bfun (concatTermEnvs [varEnv, newVarEnv]) b -- TODO recognise new func bindings
    let term = (fun t1 t2)
    bindTermInState (Scheme [] term) i
    return (cl, term)
  (App i fe ve) -> do -- func application
    v <- lift $ newTermVarFromState
    let v' = labelTerm (ProdLbl i) v
    bindTermInState (Scheme [] v') i
    (c1,t1) <- bfun varEnv fe
    (c2,t2) <- bfun varEnv ve
    return ((t1 :=: fun t2 v'):(c1 ++ c2), v')
  (If i pe te ee) -> do -- new term var, propagate constraints, make then and else clause terms equal
    v <- lift $ newTermVarFromState
    let v' = labelTerm (ProdLbl i) v
    bindTermInState (Scheme [] v') i
    (c1,t1) <- bfun varEnv pe
    (c2,t2) <- bfun varEnv te
    (c3,t3) <- bfun varEnv ee
    return ((v :=: t2):(v :=: t3):(c1 ++ c2 ++ c3), v') -- TODO: distinction between tuple union and other union?
  (Let i it be ie) -> do -- returns term of "in" expr, and constrains binding term to bound term
    (c1,t1)   <- bfun varEnv be
    newVarEnv <- buildForLetIdxTree varEnv it t1
    (c2, t2)  <- trace' ((show t1) ++ "\n") $ trcScopeBuilding newVarEnv $ bfun (concatTermEnvs [varEnv, newVarEnv]) ie
    let t2' = labelTerm (ProdLbl i) t2
    bindTermInState (Scheme [] t2') i
    return (c1 ++ c2, t2')

-- |Takes a variable environment, term builder function and expression and returns either
-- |a unified term environment solution to the analysis, or a failing constraint.
performConstraintAnalysis :: (Monad a, Eq t, Show l, Show t, ShowP t) => 
  (TermEnv l t -> Expr -> StateT (TermEnv l t) (StateT (IdxSet) a) ([Constr (Term l t)], (Term l t)))  
  -> TermEnv l t 
  -> Expr 
  -> StateT (IdxSet) a (Either (TermEnv l t) (Constr (Term l t)))
performConstraintAnalysis buildF varEnv exp = do
  -- build constraints
  ((cl,term),expEnv) <- runStateT (buildF varEnv exp) emptyTermEnv
  -- unify and apply substitutions
  case trcBuildResult (exp, expEnv, cl) $ unifyConstraints cl emptyTermEnv of
    (Left subs) -> return (Left $ mapTermEnv (forAllSubs subInScheme subs) expEnv)
    (Right con) -> return (Right con)

-- Reprogramming to weave term reconstruction and unification together
-- such that terms are fully expanded before they are generalized

-- |A list of substitutions
type Substs t = [Subst t]

-- |Compose substitution lists such that s2 is applied first, then s1
composeSubsts :: Substs t -> Substs t -> Substs t
composeSubsts s1 s2 = s2 ++ s1

nullSubsts :: Substs t
nullSubsts = []

-- |Apply all substitutions to the term
applySubstsToTerm :: Eq t => Substs (Term l t) -> Term l t -> Term l t
applySubstsToTerm subs term = forAllSubs subInTerm subs term

-- |Apply all substitutions to the term/scheme environment
applySubstsToEnv :: (Eq t, Show t, Show l) => Substs (Term l t) -> TermEnv l t -> TermEnv l t
applySubstsToEnv subs env = mapTermEnv (forAllSubs subInScheme subs) env

-- |Apply all substitutions to the constraint list
applySubstsToConstrs :: Eq t => Substs (Term l t) -> [Constr (Term l t)] -> [Constr (Term l t)]
applySubstsToConstrs subs cl = map (\(a :=: b) -> (applySubstsToTerm subs a) 
                                              :=: (applySubstsToTerm subs b)) cl

-- |The state monad used by inference functions
type InferenceMonad t m = 
  StateT (FuncEnv t) (StateT (IdxSet) m) (Substs (FuncTerm t), FuncTerm t)

-- |The type of an inference function
type InferenceFunction t m =
  FuncEnv t -> 
  Expr ->  
  InferenceMonad t m

-- |The type that is accumulated with folding inferTypes over a list of expressions.
type InferenceFoldType t = (FuncEnv t, Substs (FuncTerm t), [FuncTerm t])  

-- |Binary operator to fold over a list of expressions.
-- |Note: Term list returned in reverse order, need to apply "reverse" to it.
inferTermsFoldF :: (Monad m, Show t, Eq t) =>
  InferenceFunction t m ->
  InferenceFoldType t ->
  Expr ->
  StateT (FuncEnv t) (StateT (IdxSet) m) (InferenceFoldType t)
inferTermsFoldF f (env, subs, termList) expr = do
  (s1, t1) <- f env expr
  return (applySubstsToEnv s1 env, 
          s1 `composeSubsts` subs,
          (t1:termList))

-- |Binary operator to fold over a list of expressions, with
-- |the added constraint that all terms in the list are equal.
-- |Note: Term list returned in reverse order, need to apply "reverse" to it.
inferEqTermsFoldF :: (Monad m, Show t, Eq t) => 
  InferenceFunction t m ->
  InferenceFoldType t -> 
  Expr ->
  StateT (FuncEnv t) (StateT (IdxSet) m) (InferenceFoldType t)
inferEqTermsFoldF f (env, subs, termList) expr = do
  (s1, t1) <- f env expr
  case termList of
    []     -> return (applySubstsToEnv s1 env, 
                      s1 `composeSubsts` subs,
                      (t1:termList))
    (t2:_) -> case unifyConstraints [t1 :=: t2] emptyTermEnv of
      (Left s2)       ->  do
         -- TODO potential problem - t1 has already been bound to its
         -- expression by f, however this was done before s2 was known or applied to it
         let t1' = applySubstsToTerm s2 t1
         let sl  = s2 `composeSubsts` s1
         return (applySubstsToEnv sl env, 
                 sl `composeSubsts` subs,
                 (t1':termList))
      (Right failCon) -> error $ "TermBuilder:inferEqTermsFoldF: Term inference failed in " ++
                                 "term list equality on " ++ (show failCon)

-- |Base function for all term inferencers
inferTerms :: (Monad m, Show t, ShowP t, Eq t) => 
  InferenceFunction t m -> -- the overiding function to pass control back to
  FuncEnv t ->             -- the var environment
  Expr ->                  -- the expression
  InferenceMonad t m       -- state containing a map from expr ids to terms, and idx set
inferTerms recur varEnv expr = case expr of
  -- instantiate the term of a bound variable
  (ExprTree.Var i vi s) -> case lookupTermMaybe varEnv vi of
    (Just scheme) -> do 
      term <- lift $ instantiateScheme scheme
      let term' = labelTerm (ProdLbl i) term
      bindTermInState (Scheme [] term') i
      return $ trcSchemeInstantiation vi scheme term' $ (nullSubsts, term')
    Nothing -> do
      -- condition added so that exVars created in EmbeddedFunctions
      -- (which are typically fun vars not yet expanded by unification)
      -- are supported.
      if vi < 0 && (isPrefixOf "exVar" s)
      then do 
        v <- lift $ newTermVarFromState
        let v' = labelTerm (ProdLbl i) v
        bindTermInState (Scheme [] v') i
        return (nullSubsts, v')
      else error $ "TermBuilder:inferTerms:1 Unbound variable var " ++ (show vi) ++ " " ++ s ++
                       " when inferring terms. (not an exVar)"
  -- create new term var for a literal
  (Lit i vl) -> do
    v <- lift $ newTermVarFromState
    let v' = labelTerm (ProdLbl i) v
    bindTermInState (Scheme [] v') i
    return (nullSubsts, v')
  -- function abstraction
  (Fun i it b) -> do
    (newVarEnv, tv) <- buildForIdxTree it
    (s1, t1) <- trcScopeBuilding newVarEnv $ recur (concatTermEnvs [varEnv, newVarEnv]) b
    let term = (fun (applySubstsToTerm s1 tv) t1)
    bindTermInState (Scheme [] term) i
    return (s1, term)
  -- function application
  (App i fe arge) -> do
    tv <- lift $ newTermVarFromState
    let tv' = labelTerm (ProdLbl i) tv
    bindTermInState (Scheme [] tv') i
    (s1, t1) <- recur varEnv fe
    (s2, t2) <- recur (applySubstsToEnv s1 varEnv) arge
    let constr = (applySubstsToTerm s2 t1) :=: (fun t2 tv')
    case unifyConstraints [constr] emptyTermEnv of
      (Left s3) -> do
        let term = applySubstsToTerm s3 tv'
        bindTermInState (Scheme [] term) $ trace' (("App: " ++ (show fe) ++ " : " ++ (show constr) ++ "\n") ++ "Ret: " ++ (show term) ++ "\n") $ i
        return (s3 `composeSubsts` s2 `composeSubsts` s1, term)
      (Right failCon) -> error $ "TermBuilder:inferTerms:2 Term inference failed on " ++ (showP failCon) ++ "\nat\n" ++ (showP expr)
  -- let expression
  (Let i it be ie) -> do
    (s1, t1) <- recur varEnv be
    env' <- buildForLetIdxTree (applySubstsToEnv s1 varEnv) it t1
    let varEnv' = concatTermEnvs [varEnv, env']
    (s2, t2) <- recur (applySubstsToEnv s1 varEnv') ie
    let t2' = labelTerm (ProdLbl i) t2
    bindTermInState (Scheme [] t2') i
    return (s1 `composeSubsts` s2, t2')
  -- if expression
  (If i pe te ee) -> do
    (s1, t1) <- recur varEnv pe
    (s2, t2) <- recur (applySubstsToEnv s1 varEnv) te
    (s3, t3) <- recur (applySubstsToEnv (s2 `composeSubsts` s1) varEnv) ee
    -- TODO: confused about what subs need to be applied to what, when
    case unifyConstraints [t2 :=: t3] emptyTermEnv of
       (Left s4) -> do
         let term =  labelTerm (ProdLbl i) $ applySubstsToTerm s4 t3
         bindTermInState (Scheme [] term) i
         return (s4 `composeSubsts` s3 `composeSubsts` s2 `composeSubsts` s1,
                          term)
       Right failCon -> error $ "TermBuilder:inferTerms:3 Term inference failed on " ++ (show failCon) ++ " at " ++ (show expr)
  -- tuple expressions
  (Tup i l) -> do
    (_,sl,tl) <- foldlM (inferTermsFoldF recur) (varEnv, nullSubsts, []) l
    let term = labelTerm (ProdLbl i) $ tup $ reverse tl
    bindTermInState (Scheme [] term) i
    return (sl, term)
  -- relation expressions
  (Rel i l) -> do
    (_,sl,tl) <- foldlM (inferTermsFoldF recur) (varEnv, nullSubsts, []) l
    -- Note - FuncTerms don't have relation terms so here we just create a new
    --      term variable.
    --let term = rel $ reverse tl
    --bindTermInState (Scheme [] term) i
    v <- lift $ newTermVarFromState
    let v' = labelTerm (ProdLbl i) v
    bindTermInState (Scheme [] v') i
    return (sl, v')

-- |Term inferencer function where only terms who's terms
-- |do not already exist in the state are investigated.
inferNewTerms :: (Monad m, Show t, ShowP t, Eq t) => 
  InferenceFunction t m -> -- the overiding function to pass control back to
  FuncEnv t ->             -- the var environment
  Expr ->                  -- the expression
  InferenceMonad t m       -- state containing a map from expr ids to terms, and idx set
inferNewTerms recur varEnv expr = do
  let exprId = getExprId expr
  currentEnv <- trace' ("expr id: " ++ (show exprId) ++ "\n") $ get
  case lookup exprId currentEnv of
    -- already bound
    Just scheme -> do 
      term <- lift $ instantiateScheme scheme 
      return $ trace' ("existing term for " ++ (show exprId) ++ ": " ++ (show term) ++ "\n") $ (nullSubsts, term)
    -- not yet bound
    Nothing   -> recur varEnv expr

-- |Function that performs term inference using the inference function provided
runTermInferencer :: (Monad m, Show t, ShowP t, Eq t) =>
  InferenceFunction t m ->
  FuncEnv t ->
  Expr ->
  StateT IdxSet m (Either (FuncEnv t) (Constr (Term ExpLbl t)))
runTermInferencer func varEnv expr = do
  ((s,t),expEnv) <- runStateT (func varEnv expr) emptyTermEnv
  return (Left $ applySubstsToEnv s expEnv)

-- |Function that performs term inference using the inference function provided
runNewTermInferencer :: (Monad m, Show t, ShowP t,  Eq t) =>
  InferenceFunction t m ->
  FuncEnv t ->
  FuncEnv t ->
  Expr ->
  StateT IdxSet m (Either (FuncEnv t) (Constr (Term ExpLbl t)))
runNewTermInferencer func varEnv exprEnv1 expr = do
  ((s,t),expEnv2) <- runStateT (inferNewTerms func varEnv expr) exprEnv1
  return (Left $ applySubstsToEnv s expEnv2)

-- |addAConstraint takes three terms, and tries to unify the latter two
-- |and apply any substitutions to the first.
addAConstraint :: (Show t, ShowP t, Show l, Eq t) => Term l t -> Term l t -> Term l t -> Maybe (Term l t)
addAConstraint t a b = case unifyConstraints [a :=: b] emptyTermEnv of
  Left subs -> Just $ applySubstsToTerm subs t
  Right con -> Nothing 

