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
module Compiler.Types.Solver where

import Compiler.Front.Indices (IdxMonad)
import Compiler.Front.Common (Mappable(..), FunctorM(..), listIdx, listGet)

import qualified Compiler.Types.TypeInfo as TI
import Compiler.Types.Substitutions
import Compiler.Types.TermLanguage (Term(..), FunctionToken(Tok, TupTok), Constr((:=:)), getVarIdsInTerm)
import Compiler.Types.TypeAssignment (TyToken(Ty))
import Compiler.Types.EmbeddedFunctions (applyDimGens)
import Compiler.Types.FillGaps (possibleSubs)

import qualified Data.IntMap.Strict as IM
import qualified Data.Map.Strict as M
import Control.Monad.State.Strict (StateT, gets, modify, lift, runStateT, execStateT)
import Debug.Trace (trace)
import qualified Data.List as L
import qualified Data.Set as S
import Data.Set (Set)
import Data.Maybe (fromJust, isJust)

debugOn = True

type Tm = Term (FunctionToken TyToken)
type TmEnv = IM.IntMap Tm

mapEnv :: (Tm -> Tm) -> TmEnv -> TmEnv
mapEnv f env = fmap f env

mapEnvM :: Monad m => (Tm -> m Tm) -> TmEnv -> m TmEnv
mapEnvM f env = do
  let l = IM.toAscList env
  l' <- mapM (\(i,t) -> do t' <- f t; return (i, t')) l
  return $ IM.fromAscList l'

applySubsToTm :: SubstMap Tm -> Tm -> Tm
applySubsToTm subs val = case val of
  (Term t l) -> applySubsts subs $ Term t (map (applySubsToTm subs) l)
  other -> applySubsts subs other

type Con = Constr Tm 
type Cons = [Con]
emptyCons = []

instance Functor Constr where
  fmap f (a :=: b) = (f a) :=: (f b)

mapCons f l = fmap (fmap f) l

instance FunctorM Constr where
  fmapM f (a :=: b) = do
    a' <- f a
    b' <- f b
    return (a' :=: b')

mapMCons f l = fmapM (fmapM f) l 

type Subs = SubstMap Tm
emptySubs = emptySubstMap
singletonSub k v = M.singleton k v 

data Choice = 
    TyChoice
  | FunChoice 
type Choices = [Choice]
noChoices=[]

-- |Returns the number of non Term terms at the
-- |leaves of this expression.
countLeavesInTm :: Tm -> Int
countLeavesInTm t = case t of 
  (Term t l) -> sum $ map countLeavesInTm l
  other -> 1

-- |For all FFun terms, checks that all the Vars in each id tree
-- |are distinct.
checkVarsInEq :: Tm -> Bool
checkVarsInEq (Term (Tok (Ty "FFun")) [idT, expT]) = if length vars < cnt 
    then error ("checkVarsInEq: False: " ++ (show idT)) {-False-} 
    else (if length vars > cnt 
          then error ("checkVarsInEq: " ++ (show idT)) 
          else True)
  where vars = getVarIdsInTerm idT
        cnt = countLeavesInTm idT
checkVarsInEq (Term t l) = and $ map checkVarsInEq l
checkVarsInEq other = True

-- |For all terms in the env, checks that the Vars in each FFun's 
-- |id tree, are all distinct.
checkFunVarsInEq :: TmEnv -> Bool
checkFunVarsInEq env = and $ map checkVarsInEq $ IM.elems env

{-
-- Old version 2: needed to create inequality constraints at beginning, and then
-- check them at the end. Simpler to do version 3, just check that vars in FFun
-- id trees are all distinct.

-- |Constraint that represents in equality of all pairs
-- |of terms drawn from a set.
data InEqCon = InEq (Set Tm)
  deriving (Eq, Show, Ord)

-- |Searches all sub terms for FFuns, returning an InEqCon for each set of 
-- |argument vars.
buildInEqCons :: Tm -> Set InEqCon
buildInEqCons term = case term of
  (Term (Tok (Ty "FFun")) [idT, expT]) -> (S.singleton $ InEq $ S.fromList $ map Var $ getVarIdsInTerm idT) `S.union` (buildInEqCons expT)
  (Term t l) -> S.unions $ map buildInEqCons l
  other -> S.empty

-- |Searches all terms, returning an InEqCon for each set
-- |of argument vars in FFun terms.
buildInEqConsFromEnv :: TmEnv -> Set InEqCon
buildInEqConsFromEnv env = s
  where l = IM.elems env
        s = S.unions $ map buildInEqCons l

-- |Applies substituions to an inequality constraint, returning a new 
-- |constraint if all pairs of vars remain unequal, and Nothing if
-- |any of the members become the same (i.e. the size of the var set reduces).
applySubsToInEqCon :: SubstMap Tm -> InEqCon -> Maybe (InEqCon)
applySubsToInEqCon subs (InEq l) = if S.size l' < S.size l then Nothing else Just $ InEq l'
  where l' = S.map (applySubsToTm subs) l

-- |Applies substitutions to all inequality constraints, returning the new constraints
-- |if they all still hold, and Nothing if one of them is now infringed (i.e. if
-- |two unequal variables are now the same).
applySubsToInEqCons :: SubstMap Tm -> Set InEqCon -> Maybe (Set InEqCon)
applySubsToInEqCons subs l = if S.member Nothing l' then Nothing else Just $ S.map fromJust l'
  where l' = S.map (applySubsToInEqCon subs) l-}

{-
-- Old version 1: that checks constraints by comparing all pairings.
-- Not as efficient as updating the set of vars, and seeing if it's size
-- has reduced (e.g. two elements have become equal, above). 

-- |Constraint that represents in equality of all pairs
-- |of terms drawn from a set.
data InEqCon = InEq [Tm]
  deriving (Eq, Show, Ord)

-- |Searches all sub terms for FFuns, returning an InEqCon for each set of 
-- |argument vars.
buildInEqCons :: Tm -> Set InEqCon
buildInEqCons term = case term of
  (Term (Tok (Ty "FFun")) [idT, expT]) -> (S.singleton $ InEq $ map Var $ getVarIdsInTerm idT) `S.union` (buildInEqCons expT)
  (Term t l) -> S.unions $ map buildInEqCons l
  other -> S.empty

-- |Searches all terms, returning an InEqCon for each set
-- |of argument vars in FFun terms.
buildInEqConsFromEnv :: TmEnv -> Set InEqCon
buildInEqConsFromEnv env = s
  where l = IM.elems env
        s = S.unions $ map buildInEqCons l

-- |Returns all pairs drawn from a set.
pairs :: [a] -> [(a,a)]
pairs (v1:r) = (map (\v2 -> (v1,v2)) r) ++ (pairs r)
pairs [] = []

-- |Returns true iff none of the 
checkInEqCon :: InEqCon -> Bool
checkInEqCon (InEq l) = and $ map (\(v1,v2) -> v1 /= v2) cons 
  where cons = pairs l
        
-- |Applies subst
applySubsToInEqCon :: SubstMap Tm -> InEqCon -> InEqCon
applySubsToInEqCon subs (InEq l) = InEq $ S.map (applySubsToTm subs) l

applySubsToInEqCons :: SubstMap Tm -> Set InEqCon -> Set InEqCon
applySubsToInEqCons subs l = S.map (applySubsToInEqCon subs) l
-}

-- |applyDimGensInEnv env. Applies all dim generators in the env, and 
-- |returns any constraints that they create.
applyDimGensInEnv :: Monad m => TmEnv -> IdxMonad m (TmEnv, Cons, Subs)
applyDimGensInEnv env = do
  (env', (cl', subs)) <- runStateT (mapEnvM (\t -> do (t',cl,subs) <- lift $ applyDimGens t; modify (\(c,s) -> (c++cl,s++subs)); return t') env) ([],[])
  let subs' = fromDisjointList subs
  let env'' = mapEnv (applySubsToTm subs') env' -- apply subs to env (so any changes are made across whole env)
  return (env'', cl', subs')

-- |Encapsulates a term and overrides Eq so that two encapsulated terms
-- |are equal iff they unify.
{-data EqTm = BijEqTm Tm
  deriving Show

instance Eq BijEqTm where
  (BijEqTm t) == (BijEqTm t') = case t == t' of
    True -> trace ("\neq: " ++ (show t) ++ " == " ++ (show t') ++ "\n") $ True
    False -> case bijTm [] [t :=: t'] of
      Left subs  -> trace ("\n\nunifies: " ++ (show t) ++ " == " ++ (show t') ++ "\n" ++ (show subs) ++ "\n") $ True
      Right _ -> trace ("\n\nfails: " ++ (show t) ++ " == " ++ (show t') ++ "\n") $ False

fromBijEqTm :: BijEqTm -> Tm
fromBijEqTm (BijEqTm t) = t-}

-- |Extends a bijective relation with a new mapping, as long as
-- |neither the element from the domain, or the one from the range
-- |exists in either the dom or range already. 
extendBij :: [(Tm,Tm)] -> Tm -> Tm -> Maybe [(Tm,Tm)]
extendBij rel a b = case (lookup a rel, lookup b invRel) of
    -- if this exact one exists, leave as it is
    (Just b', Just a') | b' == b && a' == a -> Just rel 
    -- if a is not in dom, and b is not in range so add
    (Nothing, Nothing) -> Just $ (a,b):rel 
    -- otherwise fail
    _ -> Nothing
  where (dom,ran) = unzip rel
        invRel = zip ran dom

-- TODO is it safe to add a condition that passes a constraint if they are
-- syntactically equivalent? (no probs not, what if a mapping for one the terms already exists.).

-- |Tries to find a bijection between two terms, and returns 
-- |the constraint that failed if it can't
bijTm :: [(Tm,Tm)] -> [Con] -> Either [(Tm,Tm)] Con
bijTm rel (h:r) = case h of
  (Var a :=: b) -> case extendBij rel (Var a) b of
    Just rel' -> bijTm rel' r
    Nothing   -> Right h
  (a :=: Var b) -> case extendBij rel a (Var b) of
    Just rel' -> bijTm rel' r
    Nothing   -> Right h
  (Term t l :=: Term t' l') | t == t' && length l == length l' -> bijTm rel (r ++ (map (\(a,b) -> a :=: b) $ zip l l'))
  other -> Right h
bijTm rel [] = Left rel 

-- |Compares two terms and returns True if it can find a bijection between them
-- |otherwise fails.
bijTmEq :: Tm -> Tm -> Bool
bijTmEq a b = case bijTm [] [a :=: b] of
  Left _  -> True
  Right _ -> False

{-removeDuplicates :: Eq a => [a] -> [a] -> [a]
removeDuplicates res (h:r) = if elem h res then removeDuplicates res r else removeDuplicates (h:res) r
removeDuplicates res [] = res-}

-- |fillGapsInEnv termEnv. Searches the terms in the env, looking for gaps,
-- |finds possible values for each one, groups by term var id, and returns 
-- |a map from term var ids to possible lists of values. 
fillGapsInEnv :: Monad m => TmEnv -> IdxMonad m (IM.IntMap [Tm])
fillGapsInEnv env = do
  -- get possible subs from all terms in the env
  let env' = IM.toAscList env 
  maps <- mapM (\(k,t) -> do l <- possibleSubs t; return l) env'
  -- union all possibilities for each term var together (where we use 'unifySimple' for equality)
  let m = IM.unionsWith (L.unionBy bijTmEq) maps 
  return m

-- |processCons constrs. Applies term simplification (expanding 
-- |embedded functions, and dim generators) to the terms in
-- |constrs, returning new constraints, with any new ones added
-- |and the substitutions that were performed by the simplification.
processCons :: Monad m => Cons -> IdxMonad m (Cons, Subs)
processCons cons = do
  -- simplify terms
  res <- mapMCons applyDimGens cons
  -- extract simplified constraints, new constrs and substitutions from result 
  let cons' = map (\((t1,_,_) :=: (t2,_,_)) -> t1 :=: t2) res
  let newCons = concat $ map (\((_,c1,_) :=: (_,c2,_)) -> c1 ++ c2) res 
  let subsLst = concat $ map (\((_,_,s1) :=: (_,_,s2)) -> s1 ++ s2) res 
  let subs = fromDisjointList subsLst
  return (cons' ++ newCons, subs)

-- |For terms a, b returns True iff a occurs somewhere in b
occursInTm :: Eq t => (Term t) -> (Term t) -> Bool
occursInTm a b | a == b = True
occursInTm a (Term t l) = or $ map (occursInTm a) l
occursInTm _ _          = False

isVar :: Tm -> Bool
isVar (Var _) = True
isVar _ = False

-- |unifyPartFuns (funTerm1, funTerm2). Tries to unify two
-- |embedded partition functions, to return substitutions
-- |that replace the two input functions, with a new common
-- |function which subsumes them both.
unifyPartFuns :: Con -> Maybe Subs
--unifyPartFuns con = error $ "unifyPartFuns called: " ++ (show con)
unifyPartFuns con@(a :=: b) = case con of
  -- pattern match two embedded functions
  -- and find bijection between arg tuples
  ((Term (Tok (Ty "FFun")) [aItT, aExpT]) :=:
   (Term (Tok (Ty "FFun")) [bItT, bExpT])) -> 
    case bijTm [] [aItT :=: bItT] of
      -- replace both funs with "least common function"
      Left bij -> {-error $ "unify funs: " ++ (show con) ++ "\n" ++ (show resFun) --} Just $ fromDisjointList [(a, resFun), (b, resFun)]
        where -- check to see if 
              -- convert bij to subs
              bij' = map (\(a,b) -> if isVar a then (a, b) else (b, a)) bij
              subs = fromDisjointList bij'
              -- apply to exps
              aExpT' = applySubsToTm subs aExpT
              bExpT' = applySubsToTm subs bExpT
              -- get vars from each
              vids1 = getVarIdsInTerm aExpT'
              vids2 = getVarIdsInTerm bExpT'
              -- get intersection of both
              vids3 = L.nub $ L.intersect vids1 vids2
              -- make function
              aItT' = applySubsToTm subs aItT
              resTup = case vids3 of
                         []  -> (Term (Tok (Ty "VNull")) [])
                         [v] -> Var v
                         l   -> Term TupTok $ map Var vids3
              resFun = (Term (Tok (Ty "FFun")) [aItT', resTup])
      -- error
      Right err -> error $ "can't unify partition functions " ++ (show con)
  -- can't be unified yet
  other -> iterUnify [con] --Nothing --error $ "Types:Solver:unifyPartFuns: invalid constraint: "++ (show con)

-- |getVarIdListInTerm term. Returns the var ids that appear in 
-- |term in the order they occur in term (depth first traversal)
-- |with duplicates.
getVarIdListInTerm :: Show t => Term t -> [Int]
getVarIdListInTerm term = case term of
  (Term tok l) -> concat $ map getVarIdListInTerm l
  (Var idx) -> [idx]
  other -> error $ "Types:Solver:getVarIdListInTerm: invalid term " ++ (show other)

-- |unifyLayoutFuns (funTerm1, funTerm2). Tries to unify two
-- |embedded partition functions, to return substitutions
-- |that replace the two input functions, with a new common
-- |function which subsumes them both.
unifyLayoutFuns :: Con -> Maybe Subs
unifyLayoutFuns con@(a :=: b) = case con of
  -- pattern match two embedded functions
  -- and find bijection between arg tuples
  ((Term (Tok (Ty "FFun")) [aItT, aExpT]) :=:
   (Term (Tok (Ty "FFun")) [bItT, bExpT])) -> 
    case bijTm [] [aItT :=: bItT] of
      -- replace both funs with "least common function"
      Left bij -> case vids3 of
          Just l  -> Just $ fromDisjointList [(a, resFun), (b, resFun)]
            where -- make function
                  aItT' = applySubsToTm subs aItT
                  resTup = case vids3 of
                             Just []  -> (Term (Tok (Ty "VNull")) [])
                             Just [v] -> Var v
                             Just l   -> Term TupTok $ map Var l
                  resFun = (Term (Tok (Ty "FFun")) [aItT', resTup])
          Nothing -> Nothing
        where -- check to see if 
              -- convert bij to subs
              bij' = map (\(a,b) -> if isVar a then (a, b) else (b, a)) bij
              subs = fromDisjointList bij'
              -- apply to exps
              aExpT' = applySubsToTm subs aExpT
              bExpT' = applySubsToTm subs bExpT
              -- get vars from each
              vids1 = getVarIdListInTerm aExpT'
              vids2 = getVarIdListInTerm bExpT'
              -- see if one is a prefix of the other
              vids3 = (if L.isPrefixOf vids1 vids2
                       then Just vids2
                       else if L.isPrefixOf vids2 vids1 
                       then Just vids1
                       else Nothing)
      -- error
      Right err -> error $ "can't unify layout functions " ++ (show con)
  -- can't be unified yet
  other -> iterUnify [con] --Nothing

-- |iterUnify cons. Tries to unify all constraints in cons.
iterUnify :: Cons -> Maybe Subs
iterUnify [] = Just emptySubstMap
iterUnify (c:l) = case unify c of
  Just (Left subs)  -> case iterUnify (mapCons (applySubsToTm subs) l) of
    Nothing    -> Nothing
    Just subs2 -> Just $ composeSubsts subs2 subs
  Just (Right cons) -> iterUnify (cons ++ l)
  Nothing -> Nothing

-- TODO
-- NEED TO RE-CODE UNIFY TO RETURN A PAIR OF SUBS
-- AND CONS. RETURNING WHICHEVER CONS DID UNIFY, AND 
-- ANY THAT DIDN'T. OTHERWISE MIGHT NOT MAKE PROGRESS
-- IF ONE PART OF A TERM NEEDS TO BE UNIFIED BEFORE
-- ANOTHER. (e.g. multiple co-depedent functions in a term)

-- |unify con. Tries to unify a constraint, returning 
-- |Just Left substitutions or Just Right constraints if succeeded
-- |and created a new subsitution or constraints, and Nothing
-- |if it failed.
unify :: Con -> Maybe (Either Subs Cons)
--unify c = error $ "unify called " ++ (show c)
unify c = case c of
  (Var a :=: Var a') | a == a' -> Just $ Left emptySubs
  (s :=: x@(Var i)) -> if debugOn && (occursInTm x s) 
    then error $ "Solver:unify: circular constraint " ++ (show c)
    else Just $ Left $ singletonSub x s
  (x@(Var i) :=: t) -> if debugOn && (occursInTm x t)
    then error $ "Solver:unify: circular constraint " ++ (show c)
    else Just $ Left $ singletonSub x t
  -- Types that contain embedded functions
  -- Note: as don't apply intermediate subs, assumes
  -- Vars used in functions, and other parts are disjoint.
  ((Term (Tok (Ty n1)) l1) :=: (Term (Tok (Ty n2)) l2)) | n1 == n2 && TI.funs n1 /= [] -> {-error $ "bla: " ++ (show c)-}
      -- if all unified return substs
      if pfunsUnify && lfunsUnify && isJust otherRes
      then Just $ Left $ foldl composeSubsts emptySubstMap $ (map fromJust lfunRes) ++ (map fromJust pfunRes) ++ [fromJust otherRes]
      -- else return nothing
      else Nothing
    where -- try and unify partition functions
          pfunLocs = TI.partFuns n1
          pfunCons = map (\idx -> (listGet "Solver:unify:1" l1 idx) :=: (listGet "Solver:unify:2" l2 idx)) pfunLocs
          pfunRes = map unifyPartFuns pfunCons
          pfunsUnify = all isJust pfunRes
          -- try and unify layout functions
          lfunLocs = TI.layFuns n1
          lfunCons = map (\idx -> (listGet "Solver:unify:3" l1 idx) :=: (listGet "Solver:unify:4" l2 idx)) lfunLocs
          lfunRes = map unifyLayoutFuns lfunCons
          lfunsUnify = all isJust pfunRes
          -- try and unify other parts of type term
          otherLocs = [0..((length l1)-1)] L.\\ (pfunLocs ++ lfunLocs)
          otherCons = map (\idx -> (l1 `listIdx` idx) :=: (l2 `listIdx` idx)) otherLocs
          otherRes = iterUnify otherCons
  -- This method should never unify functions, should always be caught be case above.
  ((Term (Tok (Ty "FFun")) _) :=: (Term (Tok (Ty "FFun")) _)) -> 
     error $ "Solver:unify: unify should never be used to unify functions!\n" ++ (show c)
     --fmap Left (unifyPartFuns c)
  -- back to normal:
  (Term t l :=: Term t' l') | t == t' && length l == length l' -> 
    Just $ Right $ map (\(a,b) -> a :=: b) $ zip l l'
  other -> Nothing

unify2 :: Con -> Maybe (Subs, Cons)
unify2 c = case c of
  (Var a :=: Var a') | a == a' -> Just $ (emptySubs, [])
  (s :=: x@(Var i)) -> if debugOn && (occursInTm x s) 
    then error $ "Solver:unify: circular constraint " ++ (show c)
    else Just $ (singletonSub x s, [])
  (x@(Var i) :=: t) -> if debugOn && (occursInTm x t)
    then error $ "Solver:unify: circular constraint " ++ (show c)
    else Just $ (singletonSub x t, [])
  -- Types that contain embedded functions
  -- Note: as don't apply intermediate subs, assumes
  -- Vars used in functions, and other parts are disjoint.
  ((Term (Tok (Ty n1)) l1) :=: (Term (Tok (Ty n2)) l2)) | n1 == n2 && TI.funs n1 /= [] -> 
      -- if functions unified return substs
      if pfunsUnify && lfunsUnify
      then Just ((foldl composeSubsts emptySubstMap $ (map fromJust lfunRes) ++ (map fromJust pfunRes)), otherCons)
      -- else return nothing
      else Nothing
    where -- try and unify partition functions
          pfunLocs = TI.partFuns n1
          pfunCons = map (\idx -> (listGet "Solver:unify2:1" l1 idx) :=: (listGet "Solver:unify2:2" l2 idx)) pfunLocs
          pfunRes = map unifyPartFuns pfunCons
          pfunsUnify = all isJust pfunRes
          -- try and unify layout functions
          lfunLocs = TI.layFuns n1
          lfunCons = map (\idx -> (listGet "Solver:unify2:3" l1 idx) :=: (listGet "Solver:unify2:4" l2 idx)) lfunLocs
          lfunRes = map unifyLayoutFuns lfunCons
          lfunsUnify = all isJust lfunRes
          -- try and unify other parts of type term
          otherLocs = [0..((length l1)-1)] L.\\ (pfunLocs ++ lfunLocs)
          otherCons = map (\idx -> (listGet "Solver:unify2:5" l1 idx) :=: (listGet "Solver:unify2:6" l2 idx)) otherLocs
  -- This method should never unify functions, should always be caught be case above.
  ((Term (Tok (Ty "FFun")) _) :=: (Term (Tok (Ty "FFun")) _)) -> 
     error $ "Solver:unify: unify should never be used to unify functions!\n" ++ (show c)
  -- back to normal:
  (Term t l :=: Term t' l') | t == t' && length l == length l' -> 
    Just $ (emptySubstMap, map (\(a,b) -> a :=: b) $ zip l l')
  other -> Nothing

{-unifySimple :: Subs -> [Con] -> Either Subs Con
unifySimple subs (h:r) = case unify h of
  -- made a new subst
  Just (Left subs')     -> unifySimple (subs' `composeSubsts` subs) $ mapCons (applySubsToTm subs') r
  -- expanded to more constrs
  Just (Right moreCons) -> unifySimple subs (r ++ moreCons)
  -- fail
  Nothing -> Right h
unifySimple subs [] = Left subs-}

-- |State carried by unifyConsM.
data UnifyState = UnifyState {
    usNewCons :: Cons,     -- new constraints (to be unified)
    usFailedCons :: Cons,  -- failed constraints (don't unify)
    usSubs :: Subs         -- substitutions
  } deriving (Show)

-- |unifyConsM constrs. Tries to unify the constraints, applying any substitutions
-- |that have been made to latter constraints before unifying them. Any that don't
-- |unify and any new constraints and the substitutions are returned in the state monad.
unifyConsM :: Monad m => Cons -> StateT UnifyState (IdxMonad m) ()
unifyConsM (h:r) = do
  subs0 <- gets usSubs
  let h' = fmap (applySubsToTm subs0) h
  case unify h' of
    Nothing           -> modify (\s -> s { usFailedCons=h:(usFailedCons s) }) >> unifyConsM r 
    Just (Left subs)  -> modify (\s -> s { usSubs=subs `composeSubsts` (usSubs s) }) >> unifyConsM r
    Just (Right cons) -> modify (\s -> s { usNewCons=(usNewCons s) ++ cons}) >> unifyConsM r
unifyConsM [] = return ()

-- |unifyCons constrs subs. Unifies all constrs that will unify, applying
-- |new substitutions to subs. Returns any constraints that won't unify, 
-- |the final set of substitutions, and the number of the original constraints
-- |that unified (not counting children of the initial constraints).
unifyCons :: Monad m => Cons -> Subs -> IdxMonad m (Cons, Subs, Int)
unifyCons cl subs = do
  -- unify as many of the current constraints as possible
  res <- execStateT (unifyConsM cl) $ UnifyState { usNewCons=emptyCons, usFailedCons=emptyCons, usSubs=subs }
  -- count how many of the original constraints unified
  let count = (length cl) - (length $ usFailedCons res) -- num of constrs that unified
  -- if some new constraints were created, then unify those too...
  let newcons = usNewCons res
  if length newcons > 0 
  then do
    -- unify new constraints
    let subs' = usSubs res
    let newcons' = mapCons (applySubsToTm subs') newcons 
    (failedCons, finalSubs, _) <- unifyCons newcons' subs'
    -- apply final subs to existing failed constrs, and concat with recursive failed constrs
    let allFailedCons = (mapCons (applySubsToTm finalSubs) (usFailedCons res)) ++ failedCons
    -- return failed constrs, final subs, and the num of constrs that unified for this call
    return (allFailedCons, finalSubs, count)
  else do
    let finalSubs = usSubs res
    -- apply final subs to existing failed constrs
    let failedcons = mapCons (applySubsToTm finalSubs) $ usFailedCons res
    return (failedcons, finalSubs, count) 

-- TODO add fill gaps to choose
--      add choose to solve
-- (if we apply fill gaps later, we have no guarantee
--  that the subs suggested satisfy the inequality constraints,
--  and the simplification constraints)

-- TODO Extend choose to choose combinator implementations, not just fill gaps
choose :: Monad m => TmEnv -> Cons -> IdxMonad m [(Choice, Subs)]
choose env cons = do
  gapFillers <- fillGapsInEnv env
  case IM.toList gapFillers of
    [] -> return []
    ((vid, vals):r) -> do
      let subs = map (\v -> M.singleton (Var vid) v) vals
      let choices = map (\sub -> (TyChoice, sub)) subs
      return choices

-- |enumerateChoices env subs cons choices. Runs solve for each of the choices.
enumerateChoices :: Monad m => TmEnv -> Subs -> Cons -> [(Choice, Subs)] -> IdxMonad m [(Choices, Subs, TmEnv)]
enumerateChoices env subs cons choicesAndSubs = do
 -- solve for each of the possible choices
 let (choices, choiceSubs) = unzip choicesAndSubs
 sols <- mapM (\s -> solve env (s `composeSubsts` subs) (mapCons (applySubsToTm s) cons)) choiceSubs
 -- combine solutions into one list, and return it
 let sols' = concat $ map (\(ch1,sub1) -> map (\(ch2,sub2,env2) -> (ch1:ch2,sub2,env2)) sub1) $ zip choices sols
 return sols'  

-- |solve termEnv substs constrs. Solves the constraints by iteratively 
-- |unifying those that will unify, simplifying terms in the constraints, and 
-- |simplifying terms in the environment. All substitutions are accumulated in
-- |substs. When this returns these substs should be applied once more to the
-- |resulting termEnv to get the final terms. When unsolvable constraints exist
-- |a 'choice' is made which should make some more constraints solvable. If 
-- |at any point constraints remain and no more choices can be made, there
-- |is no solution and an error is thrown.
solve :: Monad m => TmEnv -> Subs -> Cons -> IdxMonad m [(Choices, Subs, TmEnv)] 
solve env subs cl = do
  -- simplify terms in constraints, and record simplifications in subs'
  (cl', subs') <- processCons $ trace ("Solver:solve: " ++ (show cl) ++ "\n\n") $ cl
  -- check if there are any constraints left
  if length cl' <= 0 
  then do
    -- if no constraints left
    -- simplify env, and if generates constrs, solve them:
    -- -------------------------------------------------
    -- apply subs to term environment
    let subs'' = subs' `composeSubsts` subs
    let env' = mapEnv (applySubsToTm subs'') env
    -- simplify term env
    (env'', envCons, envSubs) <- applyDimGensInEnv env'
    let subs''' = envSubs `composeSubsts` subs''
    -- if created more constraints
    if length envCons > 0 
    -- then solve them
    then solve env'' subs''' (trace ("Solver:solve: simplification of term env created new constraints: \n" ++ (show envCons) ++ "\n\n") envCons)
    -- else return
    else do
      -- apply final subs to env
      let finalEnv = mapEnv (applySubsToTm subs''') env''
      -- finally check inequality constraints i.e. Check function vars in arg tuples differ from each other
      if checkFunVarsInEq finalEnv 
      -- if inequalities hold then return
      then do
        choicesAndSubs <- choose finalEnv []
        if length choicesAndSubs > 0 
        then enumerateChoices finalEnv subs''' [] choicesAndSubs
        -- no more choices to be made, so finished
        else return [(noChoices, subs''', finalEnv)] -- *** WHERE SOLUTION RETURNS ***
      -- if they don't then this isn't a solution
      else return []
  else do
    -- unify any constraints that can be, returning:
    -- -------------------------------------------------
    --   nextCons: constraints that wouldn't unify
    --   allSubs : initial substs extended with any substs returned due to constrs
    --   numUnified: number of initial constraints that unified 
    (nextCons, allSubs, numUnified) <- unifyCons cl' (subs' `composeSubsts` subs)
    -- if none were unified, make a new choice
    if numUnified <= 0 
    then do
      -- apply subs to term environment
      let newEnv = mapEnv (applySubsToTm allSubs) env
      -- get a list of possible choices that could be made next
      choicesAndSubs <- choose newEnv nextCons
      -- if there are some choices possible
      if length choicesAndSubs > 0
      -- solve for each of the possible choices
      then enumerateChoices newEnv allSubs nextCons choicesAndSubs
      -- if no choices possible then die because cannot solve the constraints
      else error $ "Solver: solve failed: residual constraints, but no more choices possible:\n" ++ (show nextCons)
    -- if some were unified, simplify and unify again
    else do
      solve env allSubs (trace ("Solver:solve: some constraints were unified, iterating...\n") nextCons)

{-
-- OLD version: doesn't simplify env and solve constraints created by it.
solve :: Monad m => TmEnv -> Subs -> Cons -> IdxMonad m [(Choices, Subs, TmEnv)] 
solve env subs cl = do
  -- simplify terms in constraints, and record simplifications in subs'
  (cl', subs') <- processCons cl
  -- check if there are any constraints left
  if length cl' <= 0 
  then do
    -- no constraints left
    return [(noChoices, (subs' `composeSubsts` subs), env)]
  else do
    -- unify any constraints that can be, returning:
    --   nextCons: constraints that wouldn't unify
    --   allSubs : initial substs extended with any substs returned due to constrs
    --   numUnified: number of initial constraints that unified 
    (nextCons, allSubs, numUnified) <- unifyCons cl' (subs' `composeSubsts` subs)
    -- if none were unified, make a new choice
    if numUnified <= 0 
    then do
      -- apply subs to term environment
      let newEnv = mapEnv (applySubsToTm allSubs) env
      -- get a list of possible choices that could be made next
      choicesAndSubs <- choose newEnv nextCons
      -- if there are some choices possible
      if length choicesAndSubs > 0
      then do
        -- solve for each of the possible choices
        let (choices, choiceSubs) = unzip choicesAndSubs
        sols <- mapM (\s -> solve newEnv (s `composeSubsts` allSubs) (mapCons (applySubsToTm s) nextCons)) choiceSubs
        -- combine solutions into one list, and return it
        let sols' = concat $ map (\(ch1,sub1) -> map (\(ch2,sub2,env2) -> (ch1:ch2,sub2,env2)) sub1) $ zip choices sols
        return sols'
      -- if no choices possible then die because cannot solve the constraints
      else error $ "Solver: solve failed: residual constraints, but no more choices possible:\n" ++ (show nextCons)
    -- if some were unified, simplify and unify again
    else do
      solve env allSubs nextCons-}

