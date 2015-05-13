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

{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}

import Data.List (subsequences, permutations, partition, sortBy, find, isInfixOf)
import Data.Maybe (fromMaybe, fromJust, isJust, isNothing, catMaybes)
import Data.Char (toLower)
import qualified Data.Map.Strict as DM
import qualified Data.Set as DS

import Control.Monad.State.Strict (StateT, get, modify, lift, evalStateT)
import Data.Functor.Identity (runIdentity)
import Debug.Trace (trace)

trc = trace 

trc1 :: Show v => String -> v -> v
trc1 s v = trace (s ++ (show v)) v 

type Id = String

data Exp t =
    Var Id -- a meta var
  | Arg Id -- a concrete argument
  | Ext t  -- a reference to an external ast expression
  | Tup [Exp t] -- null values are tuples with an empty list
  | Fun (Exp t) (Exp t)
  | App (Exp t) (Exp t)
  deriving (Show, Eq)

isVar :: Exp t -> Bool
isVar (Var _) = True
isVar _ = False

isArg :: Exp t -> Bool
isArg (Arg _) = True
isArg _ = False

isApp :: Exp t -> Bool
isApp (App _ _) = True
isApp _ = False

isFun :: Exp t -> Bool
isFun (Fun _ _) = True
isFun _ = False

isNull :: Exp t -> Bool
isNull (Tup []) = True
isNull _ = False

{-class TaggedVal v t where
  getValTag :: v -> t

data ExpTag = PartFunTag | NoTag 

instance TaggedVal (Exp t) ExpTag where
  getValTag (Var vid) = if "pf" `isInfixOf` (map toLower vid) then PartFunTag else NoTag-}

-- |allTuples elems. Returns all flat tuples of the
-- |elements in elems. Doesn't consider different
-- |nested tuples. 
allTuples :: [Id] -> [Exp t]
allTuples l = map (Tup . (map Arg)) perms
  where subsets = subsequences l
        perms = concat $ map permutations subsets

allTuples2 :: Exp t -> [Id] -> [Exp t]
allTuples2 _ l = allTuples l

-- |foldExp1 proj merge exp. Applies proj to all leaves of exp
-- |(Vars, Args, and Exts) and joins them together using merge.
foldExp1 :: (Exp t -> a) -> (a -> a -> a) -> Exp t -> a
foldExp1 proj merge exp = case exp of
  Tup [] -> proj exp
  Tup l -> (foldl1 merge $ map (foldExp1 proj merge) l)
  Fun a b -> (foldExp1 proj merge a) `merge` (foldExp1 proj merge b)
  App a b -> (foldExp1 proj merge a) `merge` (foldExp1 proj merge b)
  leaf -> proj leaf

-- |foldExp2 proj merge exp. Applies proj to ALL NODES (including
-- |branches, not just leaves) of exp, and joins them together using merge.
foldExp2 :: (Exp t -> a) -> (a -> a -> a) -> Exp t -> a
foldExp2 proj merge exp = case exp of
  Tup [] -> proj exp
  Tup l -> (proj exp) `merge` (foldl1 merge $ map (foldExp2 proj merge) l)
  Fun a b -> (proj exp) `merge` (foldExp2 proj merge a) `merge` (foldExp2 proj merge b)
  App a b -> (proj exp) `merge` (foldExp2 proj merge a) `merge` (foldExp2 proj merge b)
  leaf -> proj leaf

isConcrete :: Show t => Exp t -> Bool
isConcrete exp = trc1 ("isConcrete " ++ (show exp) ++ " = ") $ not $ foldExp1 isVar (||) exp

isFunArgConcrete :: Show t => Exp t -> Bool
isFunArgConcrete exp = case exp of
  (Fun arg ran) -> isConcrete arg
  other -> error $ "isFunArgConcrete: not Fun exp: " ++ (show exp)

containsVar :: Id -> Exp t -> Bool
containsVar varId inExp = foldExp1 (\e -> if isVar e then let (Var v) = e in v == varId else False) (||) inExp

containsApp :: Exp t -> Bool
containsApp exp = foldExp2 isApp (||) exp

flattenExp :: Exp t -> [Exp t]
flattenExp = foldExp1 (\v -> if isNull v then [] else [v]) (++)

chooseMaybe :: Maybe a -> Maybe a -> Maybe a
chooseMaybe a b = case a of
  Just v -> a
  Nothing -> case b of 
    Just v -> b
    Nothing -> Nothing

getVarMaybe :: Exp t -> Maybe Id
getVarMaybe v = if isVar v then let (Var vid) = v in Just vid else Nothing

getArgMaybe :: Exp t -> Maybe Id
getArgMaybe v = if isArg v then let (Arg vid) = v in Just vid else Nothing

pickVar :: Exp t -> Maybe Id
pickVar exp = foldExp1 getVarMaybe chooseMaybe exp

class ContainsVars t where
  getVars :: t -> DS.Set Id
  getArgs :: t -> DS.Set Id

instance ContainsVars () where
  getVars _ = DS.empty
  getArgs _ = DS.empty

instance ContainsVars t => ContainsVars (Exp t) where
  getVars exp = foldExp1 (\v -> case v of 
                                  (Var vid) -> DS.singleton vid
                                  (Ext t) -> getVars t
                                  _ -> DS.empty
    ) DS.union exp
  getArgs exp = foldExp1 (\v -> case v of
                                  (Arg vid) -> DS.singleton vid
                                  (Ext t) -> getArgs t
                                  _ -> DS.empty 
    ) DS.union exp

getArgsWithDups :: Exp t -> [Id]
getArgsWithDups exp = foldExp2 (\v -> maybe [] (\x -> [x]) $ getArgMaybe v) (++) exp

countRepeatedArgs :: ContainsVars t => Exp t -> Int
countRepeatedArgs exp = case exp of
  Fun a b -> (length dupl) - (DS.size set)
    where dupl = getArgsWithDups b
          set = getArgs b
  other -> 0

sumRepeatedArgs :: ContainsVars t => Exp t -> Int
sumRepeatedArgs exp = foldExp2 countRepeatedArgs (+) exp

countNulls :: Exp t -> Int
countNulls exp = foldExp2 (\e -> if isNull e then 1 else 0) (+) exp

-- |filterExp pred exp. Flattens exp, and returns a (tuple) expression
-- |including all leaf expressions for which pred returned True.
filterExp :: (Exp t -> Bool) -> Exp t -> Exp t
filterExp pred exp = case expL' of
    [] -> Tup []
    [v] -> v
    l -> Tup l
  where expL = flattenExp exp
        expL' = filter pred expL

-- |getSubSet argSet exp. Flattens exp, and returns a (tuple) expression
-- |including all leaf expressions who's args are subsets of argSet.
getSubExp :: ContainsVars t => DS.Set Id -> Exp t -> Exp t
getSubExp argSet exp = filterExp (\e -> (getArgs e) `DS.isSubsetOf` argSet) exp  

type VarSet = DM.Map Id (DS.Set Id)

emptyVarSet = DM.empty

combineVarSets :: VarSet -> VarSet -> VarSet 
combineVarSets a b = DM.unionWith DS.intersection a b

getVarSets :: ContainsVars t => Exp t -> VarSet
getVarSets exp = case exp of
  -- from a function (for all meta vars on rhs, put set of concrete vars on lhs)
  Fun a b -> DM.fromList $ map (\v -> (v, args)) vars
    where args = getArgs a
          vars = DS.toList $ getVars b 
  -- recursion
  Tup [] -> emptyVarSet
  Tup l -> foldl1 combineVarSets $ map getVarSets l  
  App a b -> error $ "getVarSets: expression contains a function application!"
  other -> emptyVarSet

type Subs t = DM.Map Id (Exp t)

emptySubs = DM.empty

singletonSub vid exp = DM.singleton vid exp 

applySubToExp :: Id -> Exp t -> Exp t -> Exp t
applySubToExp vid exp inExp = case inExp of
  (Var v) | v == vid -> exp
  Tup l -> Tup $ map (applySubToExp vid exp) l
  Fun a b -> Fun (applySubToExp vid exp a) (applySubToExp vid exp b)
  App a b -> App (applySubToExp vid exp a) (applySubToExp vid exp b)  
  other -> other

addSub :: Show t => Id -> Exp t -> Subs t -> Subs t
addSub vid exp subs = trc ("addSub " ++ (show vid) ++ " " ++ (show exp) ++ "\n" ++ (show subs) ++ "\n=" ++ (show subs') ++ "\n\n") subs' 
  where subs' = DM.insert vid exp (DM.map (applySubToExp vid exp) subs)

applySubsToSubs :: Subs t -> Subs t -> Subs t
applySubsToSubs a b = DM.map (applySubsToExp a) b

-- |composeSubs a b sequentially composes a and b
-- |such that a is applied after b.
composeSubs :: Subs t -> Subs t -> Subs t
composeSubs a b = (applySubsToSubs a b) `DM.union` a

applySubsToId :: Subs t -> Id -> Exp t
applySubsToId subs vid = fromMaybe (Var vid) $ DM.lookup vid subs

applySubsToExp :: Subs t -> Exp t -> Exp t
applySubsToExp subs exp = case exp of
  Var vid -> applySubsToId subs vid
  Tup l -> Tup $ map (applySubsToExp subs) l
  Fun a b -> Fun (applySubsToExp subs a) (applySubsToExp subs b)
  App a b -> App (applySubsToExp subs a) (applySubsToExp subs b)
  other -> other

-- |foldSubs proj merge subs. Applies proj to all subs, and then 
-- |folds over these values using merge.
foldSubs :: (Id -> Exp t -> a) -> (a -> a -> a) -> a -> Subs t -> a
foldSubs proj _ v0 subs | DM.null subs = v0  
foldSubs proj merge v0 subs = foldl1 merge $ map (\(k,v) -> proj k v) $ DM.toList subs

-- |sumRepeatedArgsInSubs subs. Returns the number of repeated arguments
-- |in functions bound to meta vars in subs.
sumRepeatedArgsInSubs :: ContainsVars t => Subs t -> Int
sumRepeatedArgsInSubs subs = foldSubs (\_ -> \exp -> if isFun exp then sumRepeatedArgs exp else 0) (+) 0 subs

-- |countNullFunsInSubs vidSet subs. Returns the number of functions
-- |with null bodies in subs, which are bound to vars whose ids are
-- |members of vidSet.
{-countNullFunsInSubs :: DS.Set Id -> Subs t -> Int
countNullFunsInSubs vidSet subs = foldSubs (\vid -> \e -> 
  if DS.member vid vidSet
  then 
    if isFun e
    then 
      let (Fun a b) = e in 
      if isNull b then 1 else 0
    else 0
  else 0) (+) 0 subs-}
countNullFunsInSubs :: Subs t -> Int
countNullFunsInSubs subs = foldSubs (\vid -> \e -> 
  if isFun e
  then 
    let (Fun a b) = e in 
    if isNull b then 1 else 0
  else 0) (+) 0 subs

getVarsInSubs :: ContainsVars t => Subs t -> DS.Set Id
getVarsInSubs subs = foldSubs (\vid -> \exp -> DS.insert vid $ getVars exp) DS.union DS.empty subs

data Con l t = Con l (Exp t) (Exp t)
  deriving (Eq, Show)

pickVarFromCons :: [Con l t] -> Maybe Id
pickVarFromCons [] = Nothing
pickVarFromCons cl = foldl1 chooseMaybe $ concat $ map (\(Con l a b) -> [pickVar a, pickVar b]) cl

applySubToCon :: Id -> Exp t -> Con l t -> Con l t
applySubToCon vid exp (Con l a b) = Con l (applySubToExp vid exp a) (applySubToExp vid exp b)

applySubsToCon :: Subs t -> Con l t -> Con l t
applySubsToCon subs (Con l a b) = Con l (applySubsToExp subs a) (applySubsToExp subs b)

-- make constraints from a top level function constraint
-- (we leave any constraints between tuples that involves meta vars
--  abstract. i.e. we don't unify them using their shape, because 
--  different alignments are possible. However if both sides are concrete,
--  i.e. contain no meta vars, then we can unify [do we flatten or force an
--  exact match?], or if one side is a single meta var we can create a substitution.).

-- solve equations using standard unification and enumerating all
-- concrete values of vars

-- we need to distinguish between concrete params, and vars
-- so that we can enumerate all possible combinations of 
-- concrete params.

higherFunNames = ["fstfun", "sndfun", "lftfun", "rhtfun"]

-- |isHigherFun exp. Returns true if exp is a Var with a higher function name
-- |inside it.
isHigherFun :: Exp t -> Bool
isHigherFun (Var vid) = trc (vid ++ " is higher order? " ++ (show is) ++ "\n") $ is 
  where vid' = map toLower vid
        is = or $ map (\fn -> fn `isInfixOf` vid') higherFunNames
isHigherFun _ = False

-- |getHigherFun exp. Returns the higher order function named in the Var exp given.
getHigherFun :: ContainsVars t => Exp t -> (Exp t -> (Exp t, Exp t))
getHigherFun (Var vid) = case vid of
    _ | "fstfun" `isInfixOf` vidl -> 
      (\(Fun inFun@(Fun (Tup [a, b]) exp) gamma) -> (gamma, (Fun a (getSubExp (getArgs a) exp))))
    _ | "sndfun" `isInfixOf` vidl -> 
      (\(Fun inFun@(Fun (Tup [a, b]) exp) gamma) -> (gamma, (Fun b (getSubExp (getArgs b) exp))))
    _ | "lftfun" `isInfixOf` vidl -> 
      (\(Fun inFun@(Fun (Tup [Tup [a,b], Tup [c,d]]) exp) gamma) 
        -> (gamma, (Fun (Tup [a,c]) (getSubExp (getArgs a `DS.union` getArgs c) exp))))
    _ | "rhtfun" `isInfixOf` vidl -> 
      (\(Fun inFun@(Fun (Tup [Tup [a,b], Tup [c,d]]) exp) gamma) 
        -> (gamma, (Fun (Tup [b,d]) (getSubExp (getArgs b `DS.union` getArgs d) exp))))
  where vidl = map toLower vid

type SolverM m = StateT Int m

runSolver :: Monad m => SolverM m r -> m r
runSolver task = evalStateT task 0

newId :: Monad m => SolverM m Id
newId = do
  num <- get
  modify (+1)
  return $ show num 

freshVarsM :: (Show t, Monad m) => Exp t -> StateT (Subs t) (SolverM m) (Exp t)
freshVarsM exp = case exp of
  Var v1 -> do
    -- see if it's in the current map
    subs <- get
    let (Var v2) = applySubsToId subs v1
    -- if it hasn't been replaced, then make a new one
    if v1 == v2 
    then do
      v3 <- lift $ newId
      modify (\subs -> addSub v1 (Var v3) subs)
      return (Var v3)
    else return (Var v2) 
  Tup l -> mapM freshVarsM l >>= (return . Tup)
  Fun a b -> do
    a' <- freshVarsM a
    b' <- freshVarsM b
    return $ Fun a' b'
  App a b -> do
    a' <- freshVarsM a
    b' <- freshVarsM b
    return $ App a' b'
  other -> return other

freshVars :: (Show t, Monad m) => Exp t -> SolverM m (Exp t)
freshVars exp = evalStateT (freshVarsM exp) emptySubs

buildCons :: (Show l, Show t, Monad m) => l -> Exp t -> SolverM m (Exp t, [Con l t])
buildCons lbl exp = case trc ("buildCons " ++ (show lbl) ++ " " ++ (show exp) ++ "\n") $ exp of
  -- apply to children
  Tup l -> do
    x <- mapM (buildCons lbl) l
    let (l', cl) = unzip x`
    return $ (Tup l', concat cl)
  -- make constraints between fun (with new vars) and "arg -> newVar" 
  App f v -> do
    (f', cl1) <- buildCons lbl f
    (v', cl2) <- buildCons lbl v
    ret <- newId
    f'' <- if isVar f' then return f' else freshVars f'
    let cl3 = [Con lbl f'' (Fun v' (Var ret))]
    return (Var ret, cl1 ++ cl2 ++ cl3)
  -- fun do nothing
  Fun a b -> do
    (b', cl1) <- buildCons lbl b
    return (Fun a b', cl1)
  -- others, do nothing
  other -> return (other, [])

-- |solve cons. Solves a list of constraints cons, and either returns 
-- |substitutions, and any remaining constraints which contain meta vars
-- |or nothing if a constraint failed. The final subs should be applied 
-- |to any residual constraints when this returns. 
-- |This function needs to be applied 
-- |repeatedly to residual constaints until none of them change. 
solve :: (ContainsVars t, Show t, Show l, Eq t, Monad m) => [Con l t] -> SolverM m (Either ([Con l t], Subs t) (Con l t))
solve cons@(con@(Con _ e1 e2):r) = case trc ("solve " ++ ({-take 150 $-} show cons) ++ " ...\n" ++ (show $ flattenExp e1) ++ "\n" ++ (show $ flattenExp e2)) $ con of
  -- identical expressions
  (Con _ e1 e2) | e1 == e2 -> solve r
  -- expressions that are equal when flattened
  (Con _ e1 e2) | (flattenExp e1) == (flattenExp e2) -> solve r
  -- expressions with only concretes must be equal when flattened
  (Con lbl e1 e2) | isConcrete e1 && isConcrete e2 -> if (flattenExp e1) /= (flattenExp e2)
    then return $ Right con -- no solution here!
    else solve r
  -- try and apply any higher order functions
  (Con l (Var v1) e2) | trc1 "hf case 1: " $ isHigherFun e1 && isFunArgConcrete e2 -> do
    let (a,b) = (getHigherFun e1) e2
    solve ((trc ("app hf:\n" ++ (show a) ++ "\n=" ++ (show b) ++ "\n\n") $ Con l a b):r)
  (Con l e1 (Var v2)) | trc1 "hf case 2: " $ isHigherFun e2 && isFunArgConcrete e1 -> do
    let (a,b) = (getHigherFun e2) e1
    solve ((trc ("app hf:\n" ++ (show a) ++ "\n=" ++ (show b) ++ "\n\n") $ Con l a b):r)
  -- replace vars with exps
  (Con _ (Var v1) e2) | not $ isHigherFun e1 -> if containsVar v1 e2
    then error $ "circular constraint: var " ++ (show v1) ++ " in " ++ (show e2) 
    else do 
      let r' = map (applySubToCon v1 e2) r
      rec <- solve $ trc ((show v1) ++ " |-> " ++ (show e2) ++ "\n  = " ++ (show r') ++ "\n") r'
      case rec of
        Left (conl', subs) -> do
          let subs' = composeSubs subs $ singletonSub v1 e2
          return $ Left (conl', subs')
        Right _ -> return $ Right con
  (Con _ e1 (Var v2)) | not $ isHigherFun e2 -> if containsVar v2 e1
    then error $ "circular constraint: var " ++ (show v2) ++ " in " ++ (show e1) 
    else do 
      let r' = map (applySubToCon v2 e1) r
      rec <- solve $ trc ((show v2) ++ " |-> " ++ (show e1) ++ "\n  = " ++ (show r') ++ "\n") r'
      case rec of
        Left (conl', subs) -> do 
          let subs' = composeSubs subs $ singletonSub v2 e1 
          return $ Left (conl', subs')
        Right _ -> return $ Right con
  -- if exp contains fun apps, break these down
  (Con lbl e1 e2) | containsApp e1 -> do
    (e1', cl1) <- buildCons lbl e1
    solve $ r ++ cl1 ++ [Con lbl e1' e2]
  (Con lbl e1 e2) | containsApp e2 -> do
    (e2', cl2) <- buildCons lbl e2
    solve $ r ++ cl2 ++ [Con lbl e1 e2']
  -- constraint that contains one or more meta vars
  -- and no fun apps, return this to be solved by 
  -- enumerating all possible concrete values of the meta vars.
  rem -> do
    -- solve the rest
    rec <- solve r
    case rec of
      Left (conl', subs) -> do
        -- return residual 
        return $ Left (rem:conl', subs)
      Right _ -> return $ Right con
solve [] = return $ Left ([], emptySubs)

-- |iterSolve cons. Calls solve with cons and any residual constraints, until the 
-- |residual constraints do not change.
iterSolve :: (ContainsVars t, Show t, Show l, Eq t, Eq l, Monad m) => [Con l t] -> SolverM m (Either ([Con l t], Subs t) (Con l t))
iterSolve cl1 = do
  -- solve as many as we can
  rec <- solve cl1
  case trc "itersolve\n" $ rec of
    -- if one failed
    Right v -> return $ Right v
    -- if all pass, and no residual
    Left ([], subs1) -> return $ Left ([], subs1)
    -- if all constraints pass, and we have residual
    Left (cl2, subs1) -> do 
      -- apply subs to residual
      let cl3 = map (applySubsToCon subs1) cl2
      -- if these are the same as the original, we've reached a steady state so return
      if cl1 == cl3 
      then return $ Left (cl3, subs1)
      -- if they differ call recursively
      else do
        rec2 <- iterSolve $ trc ("cons changed:\n" ++ (show cl1) ++ "\n!=\n" ++ (show cl3) ++ "\n\n") $ cl3
        case rec2 of
          -- if a constraint failed
          Right v -> return $ Right v
          -- if all pass
          Left (cl4, subs2) -> do
            let subs3 = composeSubs subs2 subs1 -- compose subs, and return them
            return $ Left (cl4, subs3)


-- partition constraints
partitionCons :: (ContainsVars t, Show l, Show t) => [Con l t] -> [[Con l t]]
partitionCons l = trc ("partitionCons " ++ (show l) ++ "\n  => " ++ (show ll) ++ "\n\n") ll 
  where -- get sets of meta vars
        l' = map (\(con@(Con _ a b)) -> ((getVars a) `DS.union` (getVars b), con)) l
        -- partition 
        ll = map snd $ setPartition l'

-- |partition list. Partitions the elements in the list into a list
-- |of lists, where lists are merged if there is a non-empty intersection 
-- |(i.e. at least one element shared) between the associated sets.
setPartition :: Ord b => [(DS.Set b, a)] -> [(DS.Set b, [a])]
setPartition [] = []
setPartition [(hs,hd)] = [(hs, [hd])]
setPartition ((hs,hd):tl) = (merged:disL) -- append the merged to the disjoint
  where -- call recursively
        rec = setPartition tl
        -- find lists that have a non-empty intersection with the current list
        (disL, mergeL) = partition (\(as,al) -> DS.null $ as `DS.intersection` hs) rec
        -- merge them 
        merged = foldl1 (\(as,al) -> \(bs,bl) -> (as `DS.union` bs, al ++ bl)) ((hs, [hd]):mergeL)


isRight :: Either a b -> Bool
isRight (Left _) = False
isRight (Right _) = True

isLeft :: Either a b -> Bool
isLeft (Left _) = True
isLeft (Right _) = False

fromLeft :: Either a b -> a
fromLeft (Left a) = a

-- |enumVarVars conl subs0. For the list of constraints conl, picks a meta var, and branches trying to
-- |solve the constraints for all values of the var. Then returns the solution with the least 
-- |number of repeated args (concrete vars) in it's functions.
-- |Note: subs0 are passed down so that enumVarVals can examine it to work out sets of concrete
-- |vars (args) that possible meta var tuples can be drawn from.
enumVarVals :: forall t l m . (ContainsVars t, Show t, Show l, Eq t, Eq l, Monad m) => Subs t -> [Con l t] -> SolverM m (Either (Subs t) (Con l t))
enumVarVals subs0 [] = return $ Left emptySubs
enumVarVals subs0 conl = do
  -- get sets of all possible concrete vars for each meta var
  let srcSets1 = foldl1 combineVarSets $ concat $ map (\(Con lbl a b) -> [getVarSets a, getVarSets b]) $ trc1 "enumVarVals: " $ conl
  let srcSets2 = foldSubs (\_ -> \exp -> getVarSets exp) combineVarSets emptySubs subs0
  let srcSets = srcSets1 `combineVarSets` srcSets2
  -- pick a meta var from the constraints
  let vid = fromMaybe (error "no vars in constraints!") $ pickVarFromCons conl
  -- get all possible tuples of concrete vars for the meta var
  let argVars = fromMaybe DS.empty (DM.lookup vid srcSets)
  let tuples = (allTuples $ DS.toList argVars) :: [Exp t]
  -- branch, enumerating all it's possible values
  sols <- mapM (\tup -> solveAll (addSub vid tup subs0) $ map (applySubToCon vid tup) conl) $ 
    trc ("enumVarVals " ++ (show vid) ++ " of " ++ (show (tuples :: [Exp t])) ++ "\n  in " ++ (show conl) ++ "\n\n") tuples
  let tupsAndSols = zip tuples sols
  let sols' = map (\(t, Left s) -> (t, s)) $ filter (isLeft . snd) tupsAndSols
  case find (isRight . snd) tupsAndSols of
    -- no solutions found
    Just (_, Right c) -> return $ Right c
    -- one or more solutions found
    _ -> do
      -- count the number of repeated args in function bodies in subs
      let numRepArgs = map (sumRepeatedArgsInSubs . snd) sols'
      let maxNRA = maximum numRepArgs
      let maxNRA' = if maxNRA == 0 then 1 else maxNRA
      -- count number of "tagged" (partition functions) that return null, that this causes
      let partFunSubs = DM.filterWithKey (\vid -> \exp -> "pf" `isInfixOf` (map toLower vid)) subs0
      let solPartFuns = map (\(t, s) -> applySubsToSubs (s `composeSubs` (singletonSub vid t) `composeSubs` subs0) $ trc ("sol " ++ (show vid) ++ " = " ++ (show t) ++ "\n  => " ++ (show $ composeSubs s subs0) ++ "\n\n") partFunSubs) $ sols'
      let numNullPartFuns = map countNullFunsInSubs solPartFuns
      let solutions = zip3 numRepArgs numNullPartFuns $ trc ("enumVarVals part funs:\n" ++ (concat $ map ((++"\n") . (concat . (map ((++ "\n") . show)) . DM.toList)) solPartFuns) ++ (show numNullPartFuns) ++ "\n\n") sols'
      -- pick the solution with the least number of partition functions with null bodies
      -- and then the least of repeated args in function bodies
      let solutions' = map (\(nr1,nn1,s1) -> (s1, (nn1*maxNRA')+nr1)) solutions
      let ((solTup, solSubs),_) = head {-$ last-} $ sortBy (\(s1,n1) -> \(s2,n2) -> compare n1 n2) $ trc ("enumVarVals solutions:\n" ++ (concat $ map ((++"\n").show) solutions')) solutions'
      -- add the (meta var |-> solution tuple) sub to solSubs
      let subs = composeSubs solSubs $ singletonSub vid $ trc 
                    ("enumVarVals chose " ++ (show vid) ++ " = " ++ (show (solTup :: Exp t)) ++ "\n  of " ++ (show (sols' :: [(Exp t, Subs t)])) ++ 
                                                           "\n  => " ++ (show solSubs) ++ "\n\n") solTup
      -- return
      return $ Left subs 

-- |areDisj setL. Returns True iff all the sets in setL are disjoint.
areDisj :: Ord a => [DS.Set a] -> Bool
areDisj [] = True
areDisj [v] = True
areDisj setL = isJust $ foldl1 (\a -> \(Just bs) -> 
    -- if is just (all disjoint so far)
    if isJust a 
    then 
      -- if intersection is null, then ok, return union
      let as = fromJust a in
      if DS.null $ as `DS.intersection` bs 
      then Just $ as `DS.union` bs
      -- if intersection is non-null, they aren't disjoint, so return Nothing (failure)
      else Nothing 
    -- pass on Nothing (failure) if a is nothing
    else Nothing) justSetL
  where justSetL = map Just setL

-- |solveAll conl. Tries to solve the constraints conl, returning a solution if one exists.
-- |Note: Preprocesses constraints, partitions any residual constraints into disjoint lists,
-- |tries to solve each of these lists by enumerating all possible values for the meta vars,
-- |and then unions the solution substitutions from them all, and returns them.
-- |Note: subs0 are passed down so that enumVarVals can examine it to work out sets of concrete
-- |vars (args) that possible meta var tuples can be drawn from.
solveAll :: (ContainsVars t, Show l, Show t, Eq l, Eq t, Monad m) => Subs t -> [Con l t] -> SolverM m (Either (Subs t) (Con l t))
solveAll subs0 [] = return $ Left emptySubs
solveAll subs0 conl = do
  -- preprocess conl with iterSolve
  res <- iterSolve $ trc ("solveAll " ++ (show conl) ++ "\n") conl
  case res of
    -- no solutions found
    Right v -> return $ Right v
    -- a solution was found and returned, with no residual constraints
    Left ([], subs) -> return $ Left subs
    -- a solution was found with residual constraints
    Left (resConl, subs) -> do
      -- partition any residual constraints
      let partConl = partitionCons resConl
      -- for each disjoint set of constraints, enum all meta var values
      let subs1 = composeSubs subs subs0
      disjRes <- mapM (enumVarVals subs1) partConl
      -- check that all disjoint sets of constraints were solved
      case find isRight disjRes of
        -- one set of constraints failed
        Just (Right v) -> return $ Right v
        -- all sets of constraints succeeded
        Nothing -> do
          let resSubs = map fromLeft disjRes
          -- check the subs are disjoint (they should be!)
          let varSets = map getVarsInSubs resSubs
          case areDisj varSets of
            False -> error $ "FunEq:solveAll:subs from disjoint constraints are not disjoint!\n" ++ (show varSets) ++ "\n" ++ (show resSubs)
            True -> do
              -- compose the solutions to those disjoint sets
              let result = if resSubs == [] then emptySubs else foldl1 composeSubs resSubs
              return $ Left $ trc ("solveAll result => " ++ (show result) ++ "\n\n") result

solveTests :: [([Con Int ()], Maybe [(Con Int (), Subs ())])]
solveTests = [
  --([Con 1 (Tup [Arg "x", Arg "y", Arg "z"]) (Tup [Tup [Arg "x", Arg "y"], Arg "z"])], Nothing),
  ([Con 1 (Tup [Arg "x", App (Var "A") (Arg "y")]) (Arg "x")], Nothing)
  --([Con 1 (App (Var "B") (Tup [Arg "x", Arg "y"])) (Tup [Arg "y", Arg "x"])], Nothing),
  --([Con 1 (Tup [App (Var "A") (Tup [Arg "x", Arg "y"]), Arg "y"]) (Tup [Arg "x", App (Var "B") (Tup [Arg "y", Arg "x"])])], Nothing)
  ]

partConsTests :: [Con Int ()]
partConsTests = [
  Con 1 (Var "A") (Var "B"),
  Con 2 (Var "C") (Var "B"),
  Con 3 (Var "D") (Var "E"),
  Con 4 (Var "F") (Var "J"),
  Con 5 (Tup [Var "H", Var "I"]) (Var "E"),
  Con 6 (Var "J") (Arg "x"),
  Con 7 (Var "C") (Arg "y")
  ]

enumValsTests :: [[Con Int ()]]
enumValsTests = [
  [Con 1 (Fun (Tup [Arg "x", Arg "y"]) (Var "A")) (Fun (Tup [Arg "x", Arg "y"]) (Var "B"))]
  ]

{-solveAllTests :: [[Con Int ()]]
solveAllTests = [
  [Con 1 (Var "pfA") (Var "A"), 
   Con 2 (Var "pfB") (Var "B"),
   Con 3 (Tup [App (Var "A") (Tup [Arg "x", Arg "y"]), Arg "x"]) (Tup [Arg "x", App (Var "B") (Tup [Arg "y", Arg "x"])])]
  ]-}

solveAllTests :: [[Con Int ()]]
solveAllTests = 
  [[--Con 1 (Var "pfA") (Var "A"), 
   --Con 2 (Var "pfB") (Var "B"),
   Con 1 (Var "F") (Fun (Tup [Tup [Arg "a", Arg "b"], Tup [Arg "c", Arg "d"]]) (Tup [Arg "a", Arg "b"])),
   Con 2 (App (App (Var "lftFun") (Var "F")) (Arg "x")) (App (Var "F'") (Arg "x"))
  ]]

-- TODO fix problems
-- 1) returns error
-- 2) iterSolve when cons dont change but change order etc
-- 3) should solve break down functions e.g. [a -> b = c -> d] ==> [a = b, c = d]?

main :: IO ()
main = do
  putStr "fun equality test suite\n"
  putStr "------------------------------\n"

  {-putStr "solve tests:\n"
  --putStr $ show $ flattenExp ((Tup [Tup [Arg "x", Arg "y"], Arg "z"]) :: Exp Id)
  putStr "\n\n"
  res1 <- runSolver $ mapM (\(inp,outp) -> iterSolve inp) solveTests 
  mapM (\((inp,out1),out2) -> putStr $ (show inp) ++ "\n" ++ (show out1) ++ "\n" ++ (show out2) ++ "\n\n") $ zip solveTests res1

  putStr "partition constraints tests:\n"
  let partCons = partitionCons partConsTests
  putStr $ concat $ map ((++"\n").show) partConsTests
  putStr "  =>\n"
  putStr $ concat $ map ((++"\n").show) partCons
  putStr "\n\n"

  putStr "areDisj tests:\n"
  let sets1 = [DS.fromList [1,2], DS.fromList [3,4], DS.fromList [5,6]]
  putStr $ show sets1
  putStr $ "\n  => " ++ (show $ areDisj sets1) ++ "\n"
  let sets2 = sets1 ++ [DS.fromList [7,8,2]]
  putStr $ show sets2
  putStr $ "\n  => " ++ (show $ areDisj sets2) ++ "\n\n"

  --putStr "enumVarVals tests:\n"
  --res2 <- runSolver $ mapM (enumVarVals emptySubs) enumValsTests
  --mapM (\(tst,res) -> putStr $ "result: " ++ (show tst) ++ "\n  =>  " ++ (show res) ++ "\n\n") $ zip enumValsTests res2-}

  putStr "solveAll tests:\n"
  res3 <- runSolver $ mapM (solveAll emptySubs) solveAllTests
  mapM (\(tst,res) -> putStr $ "result: " ++ (show tst) ++ "\n  =>  " ++ (show res) ++ "\n\n") $ zip solveAllTests res3

  -- TODO check that the solution choosing system with looking at Null part funs
  -- and number of repeated args is working? Maybe count repeated args only on part funs?
  -- it's not working. enumVarVals solutions all appear to be 0

  -- improve solution selection, by giving enumVarVals
  -- an insentive to choose partition functions that don't
  -- have null bodies (or choosing functions that have the max
  -- number of distinct args, rather than least duplicates???)

  -- link this to term language/embedded functions

  -- use proper type inference to fully expand the args of functions before
  -- starting to solve them (what if not possible !?)

  -- make constraint solver, so we know which expressions
  -- made the constraint break

  -- then make function that iterates 
  -- trying to constraint solve, inserting
  -- redists until the whole thing passes.

  -- then code generate from these for triangle enum.

  -- then we write a couple of greedy searches
  -- vs an explicit search

  -- (later we utilize performance feedback to guide search)

  return ()


