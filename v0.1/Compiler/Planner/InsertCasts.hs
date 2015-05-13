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
module Compiler.Planner.InsertCasts where

import Compiler.Front.Common (eids, ShowP(..), debug, putStrE, readFileForce, pairUp)
import Compiler.Front.Indices (Idx, IdxMonad, newidST, setMinIndices)
import qualified Compiler.Front.ExprTree as E

import Compiler.Types2.Variables (VarsIn(..))
import Compiler.Types2.TermLanguage
import Compiler.Types2.TypeAssignment
import Compiler.Types2.DepTypeAssignment (unify, assignDepTypes3)
import Compiler.Types2.TermBuilder (ExpLbl(..), fun, tup)
import Compiler.Types2.FillGaps (getRedundantDims )
import Compiler.Types2.EmbeddedFunctions (showEmbeddedFuns)

import Data.List (nub, intercalate, zip4, sortBy, intersect)
import qualified Data.Map.Strict as DM
import qualified Data.IntMap.Strict as IM
import Control.Monad (foldM)
import Control.Monad.State.Strict (StateT, runStateT, evalStateT, lift, get, gets, modify)
import Data.Functor.Identity (runIdentity)
import Data.Maybe (fromMaybe, fromJust)
import Debug.Trace (trace)
import Control.Monad.Catch
import Data.Time.Clock

type FunTys = IM.IntMap TySchemeEx
type FunIds = DM.Map String Idx
type Cost = Int
type CastId = ([String], [Idx] {- vid -}, Cost)
type Casts = IM.IntMap [Idx]
type CastInfo = IM.IntMap CastId
type CastNames = [([String], Int)]
type Sol = (E.Expr, TyEnv, Cost)
type Option = (E.Expr, Cost)

getCastCost :: CastId -> Cost
getCastCost (_,_,c) = c

sumCosts :: [Cost] -> Cost
sumCosts l = sum l

-- |Node: head of lists are applied first
castNames1 :: CastNames
castNames1 = [
 (["readVMap"], 1), (["saveVMap"], 5),  (["sortVMap"], 100), (["readHMap"], 1),
 (["mirrVMap"], 200), 
 (["saveVMap", "mirrVMap"], 205), -- added to compete with repartVMap4 (because it's Stm -> Vec)  
 (["sieveSMap"], 10), 
 (["sieveSMap", "saveVMap"], 15), -- added to compete with repartVMap4 (becuase it's Stm -> Vec)
 (["repartVMap4"], 500)
  --(["cast"], 0)
  ]

--castFuns :: [(String, Int)]

nextInt :: Int -> Int -> Maybe Int
nextInt mx i = if i == mx then Nothing else Just $ i+1

nextIntLst :: Int -> [Int] -> Maybe [Int]
nextIntLst mx [i] = case nextInt mx i of
  Just i' -> Just [i']
  Nothing -> Just [0,0]
nextIntLst mx (h:r) = case nextInt mx h of
  Just h' -> Just (h':r)
  Nothing -> case nextIntLst mx r of
    Just r' | length r' == mx -> Nothing
    Just r' -> Just $ 0:r'
    Nothing -> Nothing

nextIntLstMb :: Int -> Maybe [Int] -> Maybe [Int]
nextIntLstMb mx mb = case mb of
  Just l -> nextIntLst mx l
  Nothing -> Nothing

castIdxs :: [Maybe [Int]]
castIdxs = iterate (nextIntLstMb ((length castNames1)-1)) $ Just [0]  

filterDups :: [Maybe [Int]] -> [Maybe [Int]] 
filterDups l = filter (\mb -> maybe True (\l -> l == (nub l)) mb) l

takeUntil :: (a -> Bool) -> [a] -> [a]
takeUntil f [] = []
takeUntil f (h:r) = if f h then [] else h:(takeUntil f r) 

isLeft :: Either a b -> Bool
isLeft (Left _) = True
isLeft _ = False

isRight :: Either a b -> Bool
isRight (Right _) = True
isRight _ = False

-- |filterCastsByDom castList domTy. Returns all casts whose domain type 
-- |unifies with the type given, and whose range type doesn't unify with 
-- |the type given. i.e. returns a value that doesn't match the given type
-- |from a value that does.
filterCastsByDom :: Monad m => [(Int, TyTerm)] -> TyTerm -> IdxMonad m [Int]
filterCastsByDom funTys domTy = do
  -- try and unify cast fun types with the exp to cast
  ranTy <- newTermVarFromState
  shouldPass <- mapM (\(cid,vty) -> unify [fun domTy ranTy :=: vty]) funTys
  shouldFail <- mapM (\(p,(cid,vty)) -> case p of
    Left (_,subs) -> do
      let con = domTy :=: ranTy --fun ranTy domTy :=: vty
      let con' = applyVarSubstsToConstr subs con
      unify [con']
    Right _ -> do
      return (error "should never eval this, as p is not left, so isLeft p should fail...") ) $ zip shouldPass funTys
  -- use results to filter cast functions
  let zResults = zip (zip shouldPass shouldFail) funTys
  return $ map (\(_,(cid,_)) -> cid) $ filter (\((p,f),_) -> isLeft p {-&& isRight f-}) {- trace (
       "filterCastsByDom\n              " ++ (show domTy) ++ "\n" ++
       (concat $ map (\((p,f),t) -> (if isLeft p then "DOM MATCHES /, " ++ (if isRight f then "DOM != RAN /, " else "DOM == RAN X, ") else "DOM DOESN'T X, ") ++ 
                                    (if isLeft p {-&& isRight f-} then "YES: " else "NO:  " ) ++ (show t) ++ "\n") zResults)
    ) -} zResults

-- |filterCastsByRan castList ranTy. Returns all casts whose range type 
-- |unifies with the type given, and whose domain type doesn't domain type
-- |doesn't unify with the type given. i.e. returns a value that matches the
-- |given type, from a value that doesn't.
filterCastsByRan :: Monad m => [(Int, TyTerm)] -> TyTerm -> IdxMonad m [Int]
filterCastsByRan funTys ranTy = do
  -- try and unify cast fun types with the exp to cast
  domTy <- newTermVarFromState
  shouldPass <- mapM (\(cid,vty) -> unify [fun domTy ranTy :=: vty]) funTys
  --shouldFail <- mapM (\(cid,vty) -> unify [fun ranTy domTy :=: vty]) funTys
  shouldFail <- mapM (\(p,(cid,vty)) -> case p of
    Left (_,subs) -> do
      let con = domTy :=: ranTy --fun ranTy domTy :=: vty
      let con' = applyVarSubstsToConstr subs con
      unify [con']
    Right _ -> do
      return (error "should never eval this, as p is not left, so isLeft p should fail...") ) $ zip shouldPass funTys
  -- use results to filter cast functions
  let zResults = zip (zip shouldPass shouldFail) funTys
  return $ map (\(_,(cid,_)) -> cid) $ filter (\((p,f),_) -> isLeft p {-&& isRight f-}) $ {-trace (
       "filterCastsByRan\n              " ++ (show ranTy) ++ "\n" ++
       (concat $ map (\((p,f),t) -> (if isLeft p {-&& isRight f-} then "YES: " else "NO:  " ) ++ (show t) ++ "\n") zResults)
    )-} zResults

-- |Returns functions types for the casts, by getting the types of the individual
-- |cast functions in the cast chains, and unifying the intermediate types to
-- |get the types for the whole cast chains.
getCastTypes :: Monad m => FunTys -> CastInfo -> IdxMonad m (IM.IntMap TyTerm)
getCastTypes funTys castInfo = do
  -- get cast ids
  let l = map (\(cid,(nams,vids,cost)) -> (cid, vids)) $ IM.toList castInfo
  -- get and freshen types
  let l2 = map (\(cid,vids) -> (cid, map (\vid -> fromMaybe (error "InsertCasts:getCastTypes:cast fun not in fun types!") (IM.lookup vid funTys)) vids)) l
  l3 <- mapM (\(cid,tyscms) -> do tys <- mapM instantiateSchemeEx2 tyscms ; return (cid, tys)) l2
  -- get overall type for sequential chains of cast functions e.g. a ; b ; c => a2 = b1, b2 = c1
  l4 <- mapM (\(cid, tys) -> do
    -- get dom and ran tys
    let (Term FunTok [domTy,_]) = head tys
    let (Term FunTok [_,ranTy]) = last tys
    -- unify types in between
    let constrs = pairUp (\(Term FunTok [_, ranTy]) -> \(Term FunTok [domTy, _]) -> ranTy :=: domTy) tys
    res <- unify constrs
    -- apply subs to dom and ran tys
    case res of
      Left (_,subs) -> do
        let [domTy', ranTy'] = map (applyVarSubsts subs) [domTy, ranTy]
        return $ (cid, Term FunTok [domTy', ranTy'])  
      Right _ -> error $ "Planner:InsertCasts:getCastTypes: types for cast " ++ (show cid) ++ " don't unify!\n" ++ (showP tys) 
    ) l3
  return $ IM.fromList l4

-- |applyCasts casts expr. If there are casts for expr in casts
-- |returns expr, with the correct chain of cast fun apps, otherwise
-- |returns expr.
applyCasts :: Monad m => CastInfo -> Casts -> E.Expr -> IdxMonad m E.Expr
applyCasts castInfo casts expr = do
  -- get expr id
  let eid = E.getExprId expr
  case trace ("applyCasts " ++ (show eid) ++ " " ++ (show $ IM.lookup eid casts) ++ "\n") $ IM.lookup eid casts of
    -- if no casts return expr
    Just [] -> return expr
    Nothing -> return expr
    -- create cast fun apps
    Just cl -> do
      -- create cast apps (for each cast)
      apps <- foldM (\e -> \castId -> do
                       let (nams,vids,_) = fromMaybe (error $ "InsertCasts:appCasts:unknown cast" ++ (show castId) ++ "\n" ++ (show castInfo) ++ "\n") $ IM.lookup castId castInfo ;
                       -- for each fun app in this cast (each cast is a chain of fun apps)
                       foldM (\e' -> \(vid,nam) -> do 
                         [i1,i2] <- mapM (\_ -> newidST eids) [0..1]; 
                         return (E.App i1 (E.Var i2 vid nam) e')) e $ zip vids nams) expr cl
      -- return 
      return apps

applyCastsM :: Monad m => CastInfo -> Casts -> () -> E.Expr -> IdxMonad m E.Expr
applyCastsM castInfo casts msg expr = do
  -- apply recursively to children first
  expr' <- if E.isLeafExpr expr 
           then return expr -- base case
           else E.visitExprTree (applyCastsM castInfo casts) (\_ -> \it -> return (it, msg)) msg expr -- rec case
  -- apply casts here
  expr'' <- applyCasts castInfo casts expr'
  return expr''

-- |applyCasts casts expr. Returns expr with casts inserted
-- |as function applications.
--applyCastsToExpr :: Monad m => CastInfo -> Casts -> E.Expr -> IdxMonad m E.Expr
--applyCastsToExpr castInfo casts expr = 
--  (E.visitExprTree (\_ -> \e -> applyCastsToExpr castInfo casts e) (\_ -> \it -> return (it, ())) () expr) 
--     >>= applyCasts castInfo casts --expr

applyCastsToExpr :: Monad m => CastInfo -> Casts -> E.Expr -> IdxMonad m E.Expr
applyCastsToExpr castInfo casts expr = applyCastsM castInfo casts () expr

-- |applyCast expr expId castId. Checks if the current expr's id matches
-- |expId, and if it does returns expr nested in a function application
-- |that calles the castId cast function.
applyCast :: Monad m => Idx -> Int -> E.Expr -> StateT Idx (InsertCastM m) E.Expr
applyCast expId castId expr = do
  -- apply recursively to children first
  expr' <- if E.isLeafExpr expr 
           then return expr -- base case
           else E.visitExprTree (\_ -> \e -> applyCast expId castId e) (\_ -> \it -> return (it, ())) () expr -- rec case
  -- if this expr id matches
  case E.getExprId expr' == expId of
    -- if expr is the one searched for 
    True -> do
      -- get the cast name and vid
      castInfo <- lift $ gets icCastInfo
      let (nams,vids,_) = fromMaybe (error $ "InsertCasts:applyCast:cast " ++ (show castId) ++ " not in cast info!") $ IM.lookup castId castInfo
      -- create the function apps
      expr'' <- foldM (\e -> \(vid,nam) -> do
        [i1,i2] <- lift $ lift $ mapM (\_ -> newidST eids) [0..1]
        return (E.App i1 (E.Var i2 vid nam) e)) expr' $ zip vids nams
      -- add expr id of this cast's top (last) fun app to state
      curNeid <- get
      if curNeid /= (-1) 
      then error $ "InsertCasts:applyCast: two exprs in ast with exp id " ++ (show expId) ++ ":\n" ++ (show expr') 
      else return ()
      modify (\_ -> E.getExprId expr'')
      -- return
      return expr''
    -- any other expr
    False -> return expr'

-- |applyCasts casts expr. Returns expr with casts inserted
-- |as function applications.
applyCastToExpr :: (Monad m, MonadCatch m) => E.Expr -> Idx -> Int -> InsertCastM m (E.Expr, Idx)
applyCastToExpr expr1 expId castId = do
  expr <- if debug then lift $ E.checkExpIdsUnique2 "before apply cast to expr" expr1 else return expr1
  let action = runStateT ({-E.visitExprTree (\_ -> \e -> applyCast expId castId e) (\_ -> \it -> return (it, ())) () expr 
                               >>=-} applyCast expId castId expr) (-1)
  (expr', neid) <- catch action (\e -> error $ "InsertCasts:applyCastToExpr: error " ++ (show (e :: SomeException)) ++ "\n" ++ (E.showExprTreeWithIds expr))
  if (neid == (-1)) -- check cast was applied to an expression
  then error $ "InsertCasts:applyCastToExpr:expr " ++ (show expId) ++ " not found in\n" ++ (E.showExprTreeWithIds expr) ++ "\n"
  else return ()
  expr'' <- if debug then lift $ E.checkExpIdsUnique2 "after apply cast to expr" expr' else return expr'
  return (expr'', neid)

exprIdFromLabel :: ExpLbl -> Idx
exprIdFromLabel (ProdLbl i) = i

getExprsToCast :: TyConstr -> [Idx]
getExprsToCast (a :=: b) = nub $ (map exprIdFromLabel $ getLabels a) ++ (map exprIdFromLabel $ getLabels b)

-- |lookupExpTy tyEnv expId. Returns the type of expId in tyEnv,
-- |with term vars renewed. If tyEnv doesn't include expId returns 
-- |a new term var.
lookupExpTy :: Monad m => TyEnv -> Idx -> IdxMonad m TyTerm
lookupExpTy tyEnv expId = case lookup expId tyEnv of
  Just (Scheme _ ty) -> do
    -- freshen var ids
    --ty' <- renewTermVarIds ty
    return ty
  Nothing -> do
    -- make new type var
    vr <- newTermVarFromState
    return vr

data ICState = ICState {
  icFunTys :: FunTys,
  icFunIds :: FunIds,
  icCastInfo :: CastInfo,
  icCastTys :: IM.IntMap TyTerm,
  icCurrentCost :: Cost,
  icTotalCost :: Cost,
  icSolCount :: Int,
  icLowestCost :: Cost,
  icDepth :: Int,
  icStartTime :: UTCTime,
  icDebugMsg :: String,
  icOptions :: [Option],
  icCount :: Int
}

-- |icCurrentAvgCost st. Returns the average cost of all currently found solutions.
icAvgCost :: ICState -> Float
icAvgCost st = (fromIntegral $ icTotalCost st) / (fromIntegral $ icSolCount st)

icSummary :: ICState -> String
icSummary st = "Sol count: " ++ (show $ icSolCount st) ++ "\nAvg cost: " ++ (show $ icAvgCost st) ++ "\nMin cost: " ++ (show $ icLowestCost st) ++ "\n"

type InsertCastM m = StateT ICState (IdxMonad m) 

-- |CastCandidate. (CCand ast curExprIds usedCastIds cost exprId castId)
-- |ast is current AST to apply this cast to. curExprIds are the ids of the
-- |expressions involved in fixing the current constraint (basically the expr
-- |ids of the originally broken expression, and all the cast fun apps applied to it).
-- |usedCastIds is a list of the cast ids that have already been used to try and
-- |mend the current constraint. Cost is the current cost of this candidate
-- |(including the cost of the current cast "castId" that has yet to be applied to ast).
-- |exprId is the expression the cast fun app should be applied to, and castId is 
-- |the id of the cast to apply to it.
-- |Note: ast, curExprIds, and usedCastIds haven't had exprId and castId applied
-- |to them yet. Only cost includes the cost of castId.
data CastCandidate = CCand E.Expr [Idx] [Idx] Idx Int Cost
  deriving (Show, Eq)

instance ShowP CastCandidate where
  showP (CCand ast curExprIds usedCastIds cost exprId castId) = "CCand _ " ++ (show curExprIds) ++ " " ++ (show usedCastIds) ++ " " ++
    (show cost) ++ " " ++ (show exprId) ++ " " ++ (show castId)

maxICSols2 = 3 -- max number of solutions (at each stage, and end)
maxICTime2 = 60.0 -- max time for search in seconds

-- |tryCandidate return codes.
-- |1) type checks (is a solution) and so doesn't return
-- |more candidates, 2) doesn't type check but mends current constraint and
-- |so returns candidates to mend this next constraint, 3) doesn't type check
-- |and doesn't mend current constraint but returns more candidates to try,
-- |and 4) doesn't mend current constraints and no more candidates to try 
-- |i.e. cast insertion fails.
data CandidateResult = 
   CompleteSol Sol -- 1 -- "complete solutions" are full solutions that completely type check
 | PartialSol Cost [CastCandidate] -- 2 -- "partial solutions" and candidates that mend the currently broken constraint
 | MoreCandidates [CastCandidate] -- 3 more candidates to try and fix the current constraint
 | CompleteFail -- 4 -- no more candidates available to try, can't be fixed
  deriving (Show)

sortNextCands :: [(Cost, [CastCandidate])] -> [CastCandidate]
--sortNextCands partialSols = concat $ map snd $ sortBy (\(c1,_) -> \(c2,_) -> compare c1 c2) partialSols
sortNextCands partialSols = sortBy (\(CCand _ _ _ _ _ c1) -> \(CCand _ _ _ _ _ c2) -> compare c1 c2) $ concat $ map snd partialSols

-- |insertCasts3 curCands numPartialSols nextCands sols. Tries to insert casts in
-- |a breadth first order, so that shorter chains of fun apps are tried before longer
-- |ones. Tries all the candidates in curCands until there are either enough partial solutions
-- |(numPartialSols >= maxICSols2) to start processing nextCands, or enough complete solutions
-- |(length sols >= maxICSols2) to return. It is safe to not explore all options (i.e. 
-- |throw away curCands when we have enough partial solutions, because we know that shorter
-- |solutions will be visited before longer ones (? is this true?). Sorting partial solutions
-- |in order of ascending cost should ensure that the cheapest solution is always returned found first.
-- | (Aim: to find shortest chains of redists to fix constraints before longer ones)
-- |Problem: looking for shortest sequence of redists can lead to non-optimal solution
-- |e.g. might use an expensive repartVMap rather than a mirrVMap.saveVMap.
insertCasts3 :: [CastCandidate] -> [(Cost, [CastCandidate])] -> [Sol] -> InsertCastM IO [Sol]
insertCasts3 [] [] sols = return sols -- finished
insertCasts3 [] nextCands sols = insertCasts3 (sortNextCands nextCands) [] sols -- when exaustively searched current constr, try fixing the next
insertCasts3 _  nextCands sols | length nextCands >= maxICSols2 = insertCasts3 (sortNextCands nextCands) [] sols -- when have >= 5 partial sols, start on next constr
insertCasts3 _ _ sols | length sols >= maxICSols2 = return sols -- when we have >= 5 sols, return them
 -- TODO put in limit on size of nextCands so when we have enough partial solutions we start
 -- to deal with the next constraint
 -- TODO same with number of solutions 
 -- TODO remove duplicates from nextCands before visiting them?
insertCasts3 (cand:rest) nextCands sols = do
  --lift $ lift $ putStrE $ "insertCasts3 " ++ (showP cand) ++ "\n"
  -- check whether to end here
  t0 <- gets icStartTime 
  t1 <- lift $ lift $ getCurrentTime
  let curDur = realToFrac $ diffUTCTime t1 t0
  if curDur > maxICTime2 then return sols
  -- see if ast type checks, and create new
  -- candidates if it doesnt
  else do
    res <- tryCandidate cand
    case res of
      -- this candidate is a complete solution
      (CompleteSol sol) -> (modify (\st -> st { icSolCount=(icSolCount st)+1 } )) >> (insertCasts3 rest nextCands (sols ++ [sol]))
      -- this candidate fixes the current constraint, and gives candidates for the next constraint
      (PartialSol _ []) -> error $ "InsertCasts:insertCasts3: invalid candidate result: " ++ (show res)  
      (PartialSol cost nextCands') -> insertCasts3 rest (nextCands ++ [(cost, nextCands')]) sols
      -- the current candidate doesn't fix the current constraint, but gives more options
      (MoreCandidates []) -> error $ "InsertCasts:insertCasts3: invalid candidate result: " ++ (show res)  
      (MoreCandidates moreCands) -> insertCasts3 (rest ++ moreCands) nextCands sols
      -- the current candidate can't be made to type check
      CompleteFail -> insertCasts3 rest nextCands sols

-- |tryCandidate candidate. Evaluates this candidate, to see if it is
-- |a solution, or if it needs more casts to be applied to it.
tryCandidate :: CastCandidate -> InsertCastM IO CandidateResult
tryCandidate (CCand ast curExprIds usedCastIds cost exprId castId) = do
  modify (\st -> st {  icCount=(icCount st)+1 })
  -- apply the cast (exprId and castId), if one is given (-1 means no cast)
  (ast', neid) <- if exprId /= -1 then applyCastToExpr ast exprId castId else return (ast,-1)
  let curExprIds' = if exprId /= -1 then neid:curExprIds else curExprIds
  let usedCastIds' = if exprId /= -1 then castId:usedCastIds else usedCastIds
  -- try and assign types
  tyEnv <- gets icFunTys
  res <- lift $ assignDepTypes3 tyEnv ast'
  -- switch on result of type check
  case res of
    -- candidate type checked so is a solution
    Left tys -> do
      let sol = (ast', tys, cost)
      if checkSolution sol -- check solution is valid
      then return $ CompleteSol sol
      else return CompleteFail
    -- type check failed, still more constraints to fix
    Right (con, newTyEnv) -> do
      -- get exprs to try applying casts to
      let conExprIds = getExprsToCast con
      -- see if this is the same expr, or starting to work on
      -- a new one.
      let overlapIds = conExprIds `intersect` curExprIds'
      case overlapIds of
        -- ids disjoint so starting on a new constraint
        [] -> do
          let curExprIds'' = conExprIds
          let usedCastIds'' = []
          cands <- getNextCandidates ast' con newTyEnv curExprIds'' usedCastIds'' conExprIds cost
          if cands == [] then return CompleteFail else return $ PartialSol cost cands
        -- ids overlap, still working on the same constraint
        _  -> do
          let curExprIds'' = curExprIds'
          let usedCastIds'' = usedCastIds'
          cands <- getNextCandidates ast' con newTyEnv curExprIds'' usedCastIds'' conExprIds cost
          if cands == [] then return CompleteFail else return $ MoreCandidates cands

-- p1058,p901,p901,p1087,p1087,p1145,p1145,p1107,p1107,p1054,p877,p894,p894,p1063,p1063
{-Made insertCasts3 discard solutions with no part dims, but now non solutions found for mandelbrot set. This is because:

repartVMap4 result :: DMap Stm k v of1 pf1 d m -> DMap Vec k v FNull pf2 d ()
and crossVMap11 arg 2 :: DMap Vec i w of2 FNull () d
Makes d = ()

Which is then propagated through:
crossVMaps11 output :: DMap Stm (k,i) (v,w) (FDup (FSeq of1 FLft) (FSeq of2 FRht)) (FSeq pf1 FLft) d ()
mapped over by mapSMap1 :: ... -> DMap Stm i w of pf d m
and repartVMap4 :: DMap Stm k v of1 pf1 d m -> DMap Vec k v FNull pf2 d ()

So repartVMap4 is causing the problem? should be :: d m -> d m-}

-- |checkSolution sol. Returns true if this solution is valid.
-- |Currently checks if solution's types use any partition dimensions, and if
-- |not, returns invalid, thus filtering out solutions that mirror everything.
checkSolution :: Sol -> Bool
checkSolution sol@(ast, tys, cost) = (if partDims /= [] then id else trace $ "checkSolution: discarding: " ++ (showP ast) ++ "\n" ++ (show dims) ++ "\n" ++ (showExprWithTypes tys ast) ++ "\n" ++ (E.showExprTreeWithIds ast) ++ "\n\n") (partDims /= [])
  where dims@(redDims, mirrDims, partDims) = getRedundantDims $ map (\(k, Scheme [] t) -> t) tys

-- |Generates candidate solutions that might mend the current constraint, to be tried by tryCandidate.
getNextCandidates :: E.Expr -> TyConstr -> TyEnv -> [Idx] -> [Idx] -> [Idx] -> Cost -> InsertCastM IO [CastCandidate]
getNextCandidates ast con tyEnv curExprIds usedCastIds conExprIds cost = do
  -- lookup the types of the exprs that caused the broken constraint (if they exist)
  let exprsToFix = [maximum conExprIds] -- (only try apply redists to expr with highest id i.e. the last expr created)
  --let exprsToFix = if usedCastIds == [] then nub conExprIds else nub $ conExprIds `intersect` curExprIds -- to start with try casting all exprs that break a constr, and then just the ones that break a constraint in the current chain (i.e. we branch to start with, and then just stick with the current branch to the end)
  exTys <- lift $ mapM (lookupExpTy tyEnv) exprsToFix
  -- for each get a list of casts that unify with the 
  -- dom type/ran ty (must compare with both, because we
  -- don't know if exTys are the producer/dom type or
  -- the consumer/range type.)
  castTys <- gets icCastTys
  posCasts1 <- lift $ mapM (filterCastsByDom $ IM.toList castTys) exTys
  posCasts2 <- lift $ mapM (filterCastsByRan $ IM.toList castTys) exTys
  let posL = concat $ map (\(eid,ety,c1,c2) -> map (\c -> (eid,c)) $ nub $ c1 ++ c2) $ zip4 conExprIds exTys posCasts1 posCasts2
  -- remove casts that have already been considered, in the current chain
  let posL' = filter (\(eid,c) -> not $ elem c usedCastIds) posL
  -- make candidates from this list
  castInfo <- gets icCastInfo
  let castCostF = \c -> getCastCost $ fromMaybe (error "InsertCasts:getNextCandidates: cast not in info!") $ IM.lookup c castInfo
  let cands = map (\(eid,cid) -> (CCand ast curExprIds usedCastIds (cost + (castCostF cid)) eid cid)) posL'
  return cands

maxICDepth = 500 -- max search depth
maxICSols = 30 -- max number of solutions (returns when found these)
maxICTime = 180.0 --60.0 {-30.0-} --6000.0 --5.0 -- max time for search

-- |insertCast ast castL exprId. insertCast tries to make ast's types
-- |unify by inserting cast function applications at expressions that
-- |break constraints. It tries to work on one expression (exprId) at a 
-- |time, until it nolonger causes a constraint failure. castL lists
-- |the current cast function var ids that have been applied to the current
-- |expr, so that the same cast fun isn't applied twice to a given expression.
-- |exprId starts by refering to the expr that broke the constraint, and then
-- |later to the highest cast func app applied to that expr. 
insertCast :: {-(Monad m, MonadCatch m) =>-} E.Expr -> [Idx] -> [Idx] -> InsertCastM IO [Sol]
insertCast ast castL exprIdChain = do
  -- check depth, num solutions, cost of this partial solution
  depth <- gets icDepth ; 
  numSols <- gets icSolCount ;
  t0 <- gets icStartTime 
  t1 <- lift $ lift $ getCurrentTime
  let curDur = realToFrac $ diffUTCTime t1 t0
  {-minCost <- gets icLowestCost -- TODO use for branch and bound
  curCost <- gets icCurrentCost ; avgCost <- gets icAvgCost ; -}
  if (depth > maxICDepth) || (numSols > maxICSols) || (curDur > maxICTime) {- OR ((fromIntegral curCost) > ((fromIntegral minCost) + (avgCost / 10))) -}
  then do
    --error $ "final:\n" ++ (show ast) ++ "\n" ++ (show castL) ++ "\n" ++ (show exprIdChain) ++ "\n"
    -- add to debug message
    tyEnv <- gets icFunTys
    summary <- gets icSummary
    res <- lift $ assignDepTypes3 tyEnv $ 
             trace ("insertCast " ++ ({-show-} E.showExprTreeWithIds ast) ++ "\n" ++ 
                     "castL: " ++ (show castL) ++ "\n" ++ "expIds: " ++ (show exprIdChain) ++ "\n" ++
                     summary) $ ast    
    let msg = "final: depth=" ++ (show depth) ++ ";numSols=" ++ (show numSols) ++ ";curDur=" ++ (show curDur) ++ 
              "\n" ++ (showP ast) ++ "\n" ++ (show castL) ++ "\n" ++ (show exprIdChain) ++ "\n"
              ++ (E.showExprTreeWithIds ast) ++ "\n" ++ (showP res)
    modify (\st -> st { icDebugMsg=(icDebugMsg st)++msg })
    return []
  else do
    -- apply current casts
    --ast' <- applyCastsToExpr castInfo casts ast
    -- try and assign types
    tyEnv <- gets icFunTys
    summary <- gets icSummary
    res <- lift $ assignDepTypes3 tyEnv $ 
             trace ("insertCast " ++ ({-show-} E.showExprTreeWithIds ast) ++ "\n" ++ 
                     "castL: " ++ (show castL) ++ "\n" ++ "expIds: " ++ (show exprIdChain) ++ "\n" ++
                     summary) $ ast
    case res of
      -- if passed, then return
      Left tys -> do 
        cost <- gets icCurrentCost
        -- don't allow solutions that only mirror, and don't partition
        let (redDims, mirrDims, partDims) = getRedundantDims $ map (\(k, Scheme [] t) -> t) tys
        let cost' = cost -- if length partDims == 0 then (cost*2) + 1000 else cost
        if (length partDims == 0)
        then do
          modify (\st -> st { icDebugMsg=(icDebugMsg st)++"\nignoring sol with no part dims\n" })
          return [] -- don't allow these solutions
        else do 
          -- update counts and lowest cost
          modify (\st -> st { 
            icTotalCost = (icTotalCost st) + cost',
            icSolCount = (icSolCount st) + 1,
            icLowestCost = min (icLowestCost st) cost' } )
          -- return solution
          return [(ast, tys, cost')]
      -- if failed, try inserting casts
      Right (con, newTyEnv) -> do
        -- get exprs to try applying casts to
        let exIds = getExprsToCast $ trace ("failed con: " ++ (show con) ++ "\n") $ con
        -- stay working on the same expr, unless that has now been solved
        -- (when weve solved one expr, and move onto next, wipe castL)
        let overlapEids = trace ("broken exp ids: " ++ (show exIds) ++ "\n" ++ "chain exp ids: " ++ (show exprIdChain) ++ "\n") $ exIds `intersect` exprIdChain
        --let exIds' = if {-elem exprId exIds-} overlapEids /= []  then [exprId] else exIds
        --let castL' = if exIds' == [exprId] then castL else []
        let exIds' = if overlapEids /= [] then [maximum overlapEids] else exIds
        let castL' = if overlapEids /= [] then castL else []
        -- lookup the types of these exprs if they exist
        exTys <- lift $ mapM (lookupExpTy newTyEnv) exIds'
        -- for each get a list of casts that unify with the 
        -- dom type/ran ty (must compare with both, because we
        -- don't know if exTys are the producer/dom type or
        -- the consumer/range type.)
        castTys <- gets icCastTys
        posCasts1 <- lift $ mapM (filterCastsByDom $ IM.toList castTys) exTys
        posCasts2 <- lift $ mapM (filterCastsByRan $ IM.toList castTys) exTys
        let posL = concat $ map (\(eid,ety,c1,c2) -> map (\c -> (eid,c)) $ nub $ c1 ++ c2) $ zip4 exIds' exTys posCasts1 posCasts2
        -- remove casts that have already been considered
        let posL' = filter (\(eid,c) -> not $ elem c castL') $ trace ("Possibilities:\n" ++ (concat $ map ((++"\n").show) posL) ++ "\n") $ posL
        -- try applying these casts to the various expressions
        -- update current cost to be current cost of the ast (sum of cast costs)
        castInfo <- gets icCastInfo
        posAsts <- mapM (\(eid,c) -> do 
                           (ast', neid) <- applyCastToExpr ast eid c ;
                           let cost = getCastCost $ fromMaybe (error "InsertCasts:insertCast: cast not in info!") $ IM.lookup c castInfo ;
                           return (ast', eid, neid, c, cost)) posL' -- (new ast, eid of original exp being fixed, eid of cast app, vid of cast fun, cost of cast)
        modify (\st -> st { icDepth=(icDepth st)+1 })
        solL <- mapM (\(ast', oeid, neid, c, cost) -> do -- (ast, exp id of cast app, cast vid, cast cost)
                       modify (\st -> st {icCurrentCost = (icCurrentCost st)+cost});
                       res <- insertCast ast' (c:castL') (neid:oeid:exprIdChain); 
                       modify (\st -> st {icCurrentCost = (icCurrentCost st)-cost});
                       return res) posAsts
        modify (\st -> st { icDepth=(icDepth st)-1 })
        return $ concat solL        

        --error $ "\n" ++ (intercalate "\n\n" $ map show $ zip posL' posAsts)
        -- get types of these expressions
        --let exTys = map (\eid -> ) exIds
        -- for each expression, try casting it
        --solL <- mapM (\eid -> insertCasts tyEnv ast castInfo casts eid) exIds
        --return $ concat solL

-- |insertCast ast castL exprId. insertCast tries to make ast's types
-- |unify by inserting cast function applications at expressions that
-- |break constraints. It tries to work on one expression (exprId) at a 
-- |time, until it nolonger causes a constraint failure. castL lists
-- |the current cast function var ids that have been applied to the current
-- |expr, so that the same cast fun isn't applied twice to a given expression.
-- |exprId starts by refering to the expr that broke the constraint, and then
-- |later to the highest cast func app applied to that expr. 
insertCast2 :: {-(Monad m, MonadCatch m) =>-} E.Expr -> [Idx] -> [Idx] -> InsertCastM IO [Sol]
insertCast2 ast castL exprIdChain = do
  -- check depth, num solutions, cost of this partial solution
  depth <- gets icDepth ; 
  numSols <- gets icSolCount ;
  t0 <- gets icStartTime 
  t1 <- lift $ lift $ getCurrentTime
  let curDur = realToFrac $ diffUTCTime t1 t0
  options <- gets icOptions
  {-minCost <- gets icLowestCost -- TODO use for branch and bound
  curCost <- gets icCurrentCost ; avgCost <- gets icAvgCost ; -}
  if {-(length options >= 5) ||-} (depth > maxICDepth) || (numSols > maxICSols) || (curDur > maxICTime) 
      {-OR ((fromIntegral curCost) > ((fromIntegral minCost) + (avgCost / 10))) -}
  then do
    --error $ "final:\n" ++ (show ast) ++ "\n" ++ (show castL) ++ "\n" ++ (show exprIdChain) ++ "\n"
    -- add to debug message
    tyEnv <- gets icFunTys
    summary <- gets icSummary
    res <- lift $ assignDepTypes3 tyEnv $ 
             trace ("insertCast2 " ++ ({-show-} E.showExprTreeWithIds ast) ++ "\n" ++ 
                     "castL: " ++ (show castL) ++ "\n" ++ "expIds: " ++ (show exprIdChain) ++ "\n" ++
                     summary) $ ast    
    let msg = "final: depth=" ++ (show depth) ++ ";numSols=" ++ (show numSols) ++ ";curDur=" ++ (show curDur) ++ 
              "\n" ++ (showP ast) ++ "\n" ++ (show castL) ++ "\n" ++ (show exprIdChain) ++ "\n"
              ++ (E.showExprTreeWithIds ast) ++ "\n" ++ (showP res)
    modify (\st -> st { icDebugMsg=(icDebugMsg st)++msg })
    return []
  else do
    -- apply current casts
    --ast' <- applyCastsToExpr castInfo casts ast
    -- try and assign types
    tyEnv <- gets icFunTys
    summary <- gets icSummary
    res <- lift $ assignDepTypes3 tyEnv $ 
             trace ("insertCast2 " ++ ({-show-} E.showExprTreeWithIds ast) ++ "\n" ++ 
                     "castL: " ++ (show castL) ++ "\n" ++ "expIds: " ++ (show exprIdChain) ++ "\n" ++
                     summary) $ ast
    case res of
      -- if passed, then return
      Left tys -> do 
        cost <- gets icCurrentCost
        -- don't allow solutions that only mirror, and don't partition
        let (redDims, mirrDims, partDims) = getRedundantDims $ map (\(k, Scheme [] t) -> t) tys
        let cost' = cost -- if length partDims == 0 then (cost*2) + 1000 else cost
        if (length partDims == 0)
        then do
          modify (\st -> st { icDebugMsg=(icDebugMsg st)++"\nignoring sol with no part dims\n" })
          return [] -- don't allow these solutions
        else do 
          -- update counts and lowest cost
          modify (\st -> st { 
            icTotalCost = (icTotalCost st) + cost',
            icSolCount = (icSolCount st) + 1,
            icLowestCost = min (icLowestCost st) cost' } )
          -- return solution
          return [(ast, tys, cost')]
      -- if failed, try inserting casts
      Right (con, newTyEnv) -> do
        -- get exprs to try applying casts to
        let exIds = getExprsToCast $ trace ("failed con: " ++ (show con) ++ "\n") $ con
        -- if weve solved the current con/block (i.e. exIds /\ exprIdChain == {}) then add to options and return
        let overlapEids = trace ("broken exp ids: " ++ (show exIds) ++ "\n" ++ "chain exp ids: " ++ (show exprIdChain) ++ "\n") $ exIds `intersect` exprIdChain
        if overlapEids == [] -- if solved current block, now looking at new constraint
        then do
          -- add this partial solution to options, and return
          cost <- gets icCurrentCost
          modify (\st -> st { icOptions=(ast, cost):(icOptions st) })
          return []
        else do
          -- keep trying to solve current constraint
          let exIds' = [maximum overlapEids]
          let castL' = castL
          -- lookup the types of these exprs if they exist
          exTys <- lift $ mapM (lookupExpTy newTyEnv) exIds'
          -- for each get a list of casts that unify with the 
          -- dom type/ran ty (must compare with both, because we
          -- don't know if exTys are the producer/dom type or
          -- the consumer/range type.)
          castTys <- gets icCastTys
          posCasts1 <- lift $ mapM (filterCastsByDom $ IM.toList castTys) exTys
          posCasts2 <- lift $ mapM (filterCastsByRan $ IM.toList castTys) exTys
          let posL = concat $ map (\(eid,ety,c1,c2) -> map (\c -> (eid,c)) $ nub $ c1 ++ c2) $ zip4 exIds' exTys posCasts1 posCasts2
          -- remove casts that have already been considered
          let posL' = filter (\(eid,c) -> not $ elem c castL') $ trace ("Possibilities:\n" ++ (concat $ map ((++"\n").show) posL) ++ "\n") $ posL
          -- try applying these casts to the various expressions
          -- update current cost to be current cost of the ast (sum of cast costs)
          castInfo <- gets icCastInfo
          posAsts <- mapM (\(eid,c) -> do 
                             (ast', neid) <- applyCastToExpr ast eid c ;
                             let cost = getCastCost $ fromMaybe (error "InsertCasts:insertCast2: cast not in info!") $ IM.lookup c castInfo ;
                             return (ast', eid, neid, c, cost)) posL' -- (new ast, eid of original exp being fixed, eid of cast app, vid of cast fun, cost of cast)
          modify (\st -> st { icDepth=(icDepth st)+1 })
          solL <- mapM (\(ast', oeid, neid, c, cost) -> do -- (ast, exp id of cast app, cast vid, cast cost)
                         modify (\st -> st {icCurrentCost = (icCurrentCost st)+cost});
                         res <- insertCast2 ast' (c:castL') (neid:oeid:exprIdChain); 
                         modify (\st -> st {icCurrentCost = (icCurrentCost st)-cost});
                         return res) posAsts
          modify (\st -> st { icDepth=(icDepth st)-1 })
          return $ concat solL   

callInsertCasts2 :: Option -> InsertCastM IO ([Option], [Sol])
callInsertCasts2 (ast, cost) = do
  modify (\st -> st {icCurrentCost = cost, icOptions=[]});
  sols <- insertCast2 ast [] []
  options <- gets icOptions
  return (options, sols)

-- an option is just an ast that fixes a single constraint
-- we get several of such options for the current constraint
-- then we take the cheapest 5, and try fixing the next constraint
-- for each of those...

castLoop :: [Option] -> [Sol] -> InsertCastM IO [Sol]
castLoop [] sols = return sols
castLoop options sols = do
  lift $ lift $ putStr $ "castLoop " ++ (showP options) ++ " " ++ (showP sols) ++ "\n"
  -- check for termination condition
  t0 <- gets icStartTime 
  t1 <- lift $ lift $ getCurrentTime
  let curDur = realToFrac $ diffUTCTime t1 t0
  if (curDur > maxICTime) 
  then return sols
  else do
    -- call insert casts2 for each option
    results <- mapM callInsertCasts2 options
    -- concat sols and options  
    let (options2, sols2) = unzip results
    let sols3 = sols ++ (concat sols2) 
    -- if enough solutions then return
    if length sols3 >= maxICSols
    then return sols3
    else do
      -- else keep searching
      -- sort options by cost ascending
      let options3 = sortBy (\(_,c1) -> \(_,c2) -> compare c1 c2) $ concat options2
      let options4 = take 5 options3
      castLoop options4 sols3

runCastLoop :: E.Expr -> InsertCastM IO [Sol]
runCastLoop ast = castLoop [(ast, 0)] []

-- (E.Expr, TyConstr, TyEnv, Cost)

-- |insertCastBF ast castL exprId. Breadth first. insertCastBF tries to make ast's types
-- |unify by inserting cast function applications at expressions that
-- |break constraints. It tries to work on one expression (exprId) at a 
-- |time, until it nolonger causes a constraint failure. castL lists
-- |the current cast function var ids that have been applied to the current
-- |expr, so that the same cast fun isn't applied twice to a given expression.
-- |exprId starts by refering to the expr that broke the constraint, and then
-- |later to the highest cast func app applied to that expr. 
{-insertCastBF :: {-(Monad m, MonadCatch m) =>-} [[(E.Expr, [Idx], [Idx], Cost)]] -> [Sol] -> InsertCastM IO [Sol]
insertCastBF [] solsSoFar = return solsSoFar -- finished
insertCastBF ([]:restAll) solsSoFar = insertCastBF restAll solsSoFar -- proceed to next block
insertCastBF (((ast, castL, exprIdChain, cost):restBlk):restAll) solsSoFar = do
  -- check num solutions, cost of this partial solution
  numSols <- gets icSolCount ;
  t0 <- gets icStartTime 
  t1 <- lift $ lift $ getCurrentTime
  let curDur = realToFrac $ diffUTCTime t1 t0
  if (numSols > maxICSols) || (curDur > maxICTime) 
  then do
    -- add to debug message
    tyEnv <- gets icFunTys
    summary <- gets icSummary
    res <- lift $ assignDepTypes3 tyEnv $ 
             trace ("insertCastBF " ++ ({-show-} E.showExprTreeWithIds ast) ++ "\n" ++ 
                     "castL: " ++ (show castL) ++ "\n" ++ "expIds: " ++ (show exprIdChain) ++ "\n" ++
                     summary) $ ast    
    let msg = "final: numSols=" ++ (show numSols) ++ ";curDur=" ++ (show curDur) ++ 
              "\n" ++ (showP ast) ++ "\n" ++ (show castL) ++ "\n" ++ (show exprIdChain) ++ "\n"
              ++ (E.showExprTreeWithIds ast) ++ "\n" ++ (showP res)
    modify (\st -> st { icDebugMsg=(icDebugMsg st)++msg })
    return solsSoFar
  else do
    -- apply current casts
    --ast' <- applyCastsToExpr castInfo casts ast
    -- try and assign types
    tyEnv <- gets icFunTys
    summary <- gets icSummary
    res <- lift $ assignDepTypes3 tyEnv $ 
             trace ("insertCastBF " ++ ({-show-} E.showExprTreeWithIds ast) ++ "\n" ++ 
                     "castL: " ++ (show castL) ++ "\n" ++ "expIds: " ++ (show exprIdChain) ++ "\n" ++
                     summary) $ ast
    case res of
      -- if passed, then return
      Left tys -> do 
        -- don't allow solutions that only mirror, and don't partition
        let (redDims, mirrDims, partDims) = getRedundantDims $ map (\(k, Scheme [] t) -> t) tys
        if (length partDims == 0)
        then do
          modify (\st -> st { icDebugMsg=(icDebugMsg st)++"\nignoring sol with no part dims\n" })
          return [] -- don't allow these solutions
        else do 
          -- update counts and lowest cost
          modify (\st -> st { 
            icTotalCost = (icTotalCost st) + cost,
            icSolCount = (icSolCount st) + 1,
            icLowestCost = min (icLowestCost st) cost } )
          -- add solution to list
          insertCastBF rest ((ast, tys, cost):solsSoFar)
      -- if failed, try inserting casts
      Right (con, newTyEnv) -> do
        -- get exprs to try applying casts to
        let exIds = getExprsToCast $ trace ("failed con: " ++ (show con) ++ "\n") $ con
        -- stay working on the same expr, unless that has now been solved
        -- (when weve solved one expr, and move onto next, wipe castL)
        let overlapEids = trace ("broken exp ids: " ++ (show exIds) ++ "\n" ++ "chain exp ids: " ++ (show exprIdChain) ++ "\n") $ exIds `intersect` exprIdChain
        --let exIds' = if {-elem exprId exIds-} overlapEids /= []  then [exprId] else exIds
        --let castL' = if exIds' == [exprId] then castL else []
        let exIds' = if overlapEids /= [] then [maximum overlapEids] else exIds
        let castL' = if overlapEids /= [] then castL else []
        -- if current exp has been solved, then delete current block of options to try

        -- lookup the types of these exprs if they exist
        exTys <- lift $ mapM (lookupExpTy newTyEnv) exIds'
        -- for each get a list of casts that unify with the 
        -- dom type/ran ty (must compare with both, because we
        -- don't know if exTys are the producer/dom type or
        -- the consumer/range type.)
        castTys <- gets icCastTys
        posCasts1 <- lift $ mapM (filterCastsByDom $ IM.toList castTys) exTys
        posCasts2 <- lift $ mapM (filterCastsByRan $ IM.toList castTys) exTys
        let posL = concat $ map (\(eid,ety,c1,c2) -> map (\c -> (eid,c)) $ nub $ c1 ++ c2) $ zip4 exIds' exTys posCasts1 posCasts2
        -- remove casts that have already been considered
        let posL' = filter (\(eid,c) -> not $ elem c castL') $ trace ("Possibilities:\n" ++ (concat $ map ((++"\n").show) posL) ++ "\n") $ posL
        -- try applying these casts to the various expressions
        -- update current cost to be current cost of the ast (sum of cast costs)
        castInfo <- gets icCastInfo
        posAsts <- mapM (\(eid,c) -> do 
                           (ast', neid) <- applyCastToExpr ast eid c ;
                           let cost = getCastCost $ fromMaybe (error "InsertCasts:insertCastBF: cast not in info!") $ IM.lookup c castInfo ;
        -- (ast': new ast, eid: eid of original exp being fixed, neid: eid of cast app, c: vid of cast fun, cost: cost of cast)
                           return (ast', (c:castL), (neid:eid:exprIdChain), cost)) posL'
        insertCastBF (rest ++ posAsts) solsSoFar   

        --error $ "\n" ++ (intercalate "\n\n" $ map show $ zip posL' posAsts)
        -- get types of these expressions
        --let exTys = map (\eid -> ) exIds
        -- for each expression, try casting it
        --solL <- mapM (\eid -> insertCasts tyEnv ast castInfo casts eid) exIds
        --return $ concat solL-}

{-insertCasts :: Monad m => FunTys -> E.Expr -> CastInfo -> Casts -> Idx -> IdxMonad m [Sol]
insertCasts funTys ast castInfo casts expIdx = do
  -- get any current casts for expIdx
  -- and choose the next one
  let nxt = (case IM.lookup expIdx casts of
               Just cl -> nextIntLstMb ((length castNames)-1) $ Just cl
               Nothing -> Just [0])
  case nxt of
    -- if there is a next one, try it
    Just cl -> do
      -- add new cast
      let casts' = IM.insert expIdx cl casts
      -- try and infer types
      sols <- insertCast funTys ast castInfo casts'
      -- if returned some solutions
      case sols of
        -- no solutions, so try next
        [] -> insertCasts funTys ast castInfo casts' expIdx
        -- found some solutions, so return
        sols  -> return sols
    -- if there isn't return []
    Nothing -> return []-}

-- |findCasts funTys funIds ast. Searches for applications of cast 
-- |functions that make ast's types unify. Solutions are returned in
-- |order of ascending cost. Works by iteratively trying to infer types
-- |and trying to mend one constraint at a time by inserting cast functions
-- |and then re-type-checking.
findCasts1 :: {-(Monad m, MonadCatch m) =>-} CastNames -> FunTys -> FunIds -> E.Expr -> IdxMonad IO ([Sol], String)
findCasts1 castNames funTys funIds ast = do
  lift $ putStrE "entered findCasts1"
  --res <- unify [UniVar 1 :=: (Term (Tok (Ty "FFst")) [])]
  --error $ show res
  -- make cast info
  let castInfos = map (\(cid,(nams,cost)) -> let vids = map (\nam -> fromMaybe (error $ "cast " ++ nam ++ " not in fun ids!") (DM.lookup nam funIds)) nams in (cid, (nams, vids, cost))) $ zip [0..] castNames
  let castInfo = IM.fromList castInfos
  -- make null casts
  let casts = IM.empty
  -- create state state
  castTys <- getCastTypes funTys castInfo
  --error $ "Casts:\n" ++ (show castInfo)++ "\n\n" ++ (showP castTys)
  t0 <- lift $ getCurrentTime
  let st0 = ICState { icFunTys=funTys, icFunIds=funIds, 
    icCastInfo=castInfo ,
    icCastTys=castTys,
    icDepth = 0,
    icTotalCost=0,
    icSolCount=0,
    icCurrentCost=0,
    icLowestCost=maxBound,
    icStartTime=t0,
    icDebugMsg="",
    icOptions=[],
    icCount=0 }
  -- run search in monad 
  ----(sols,st1) <- runStateT (insertCast ast [] (-1)) st0
  ----(sols,st1) <- runStateT (runCastLoop ast) st0
  --(sols,st1) <- runStateT (insertCast ast [] [] {-insertCastBF [(ast, [], [], 0)] []-}) st0
 {- astSrc <- lift $ readFileForce "/home/taj105/Dropbox/Programming/haskell/flocc/Compiler/Tests/Casts/program5b.expr"
  let ast' = (read astSrc) :: E.Expr-}
  ast' <- E.renewExprIds ast 
  newMinEid <- E.maxExpId ast'
  setMinIndices (newMinEid+1)
  --ids <- get
  --lift $ putStrE $ "ids: " ++ (show ids) ++ "\n"  
  lift $ putStrE $ "inserting casts into:\n" ++ (showP ast') ++ "\n"
  --lift $ putStrE $ "AST:\n\n" ++ (show ast') ++ "\n\n"
  (sols,st1) <- runStateT (insertCasts3 [CCand ast' [] [] 0 (-1) (-1)] [] []) st0
  lift $ putStrE $ "findCasts1 finished after " ++ (show $ icCount st1) ++ " iterations with.\n"
  -- sort solutions 
  let sols' = sortBy (\(_,_,c1) -> \(_,_,c2) -> compare c1 c2) sols
  return (sols', icDebugMsg st1)

-- New Technique 19/06/2014
-- Get types of all casts, then search for chains of redist funs
-- that unify with those types.

-- |getCastFunEids exp. Returns a list of the expr ids of the (Var "cast") expressions in exp.
getCastFunEids :: E.Expr -> [Idx]
getCastFunEids exp = map E.getExprId $ E.filterExprs (\e -> E.isVarExpr e && (E.getVarExprName e) == "cast") exp

-- |getCastAppEids exp. Returns a list of expression ids for cast fun apps, where fst is app expr id, and snd is cast var expr id.
getCastAppEids :: E.Expr -> [(Idx, Idx)]
getCastAppEids exp = E.foldExpr (\e -> if E.isAppExpr e then (let (E.App aid f _) = e in if E.isVarExpr f && (E.getVarExprName f) == "cast" then [(aid, E.getExprId f)] else []) else []) (\_ -> []) (++) exp

-- |getExprTys tyEnv eids. Returns the types for all eids in tyEnv, throwing an error if an eid in eids is not in tyEnv.
getExprTys :: Monad m => IM.IntMap TyScheme -> [Idx] -> IdxMonad m [(Idx, TyTerm)]
getExprTys tyEnv eids = mapM (\eid -> do
  let tyScm = IM.lookup eid tyEnv
  case tyScm of
    Just (Scheme [] ty) -> return (eid, ty)
    other -> error $ "Planner:InsertCasts:getExprTys: type for cast exp " ++ (show eid) ++ " not in env: " ++ (showP tyEnv)) eids

-- |getCastsForTy ty cands sols. Searches all chains of candidates cands in a breadth first order, to 
-- |find a chain of casts who's type will unify with ty.
getCastsForTy :: TyTerm -> [CastId] -> [CastId] -> InsertCastM IO [CastId]
getCastsForTy ty [] [] = error $ "Planner:InsertCasts:getCastsForTy: can't find cast funs for ty " ++ (show ty) ++ "\n"
getCastsForTy ty [] sols = return sols -- stop when no candidates left
getCastsForTy ty _ sols | length sols >= 3 = getCastsForTy ty [] sols -- stop when found 3 solutions
getCastsForTy ty (hd@(nams,vids,cost):_) sols | length vids >= 5 = getCastsForTy ty [] sols -- stop when current cand has 5 functions chained together  
getCastsForTy ty@(Term FunTok [domTy, ranTy]) cands@(hd:tl) sols = do
  -- get type of candidate
  funTys <- gets icFunTys
  candTys <- lift $ getCastTypes funTys $ IM.singleton 0 hd
  let candTy@(Term FunTok [candDomTy, candRanTy]) = fromJust $ IM.lookup 0 candTys -- TODO remove IntMap here
  -- test if dom type of cand matches domTy
  test1 <- lift $ unify [domTy :=: candDomTy]
  case test1 of
    -- if does
    Left (_,subs) -> do
      -- test if cand type matches ty
      test2 <- lift $ unify [ty :=: candTy]
      case test2 of
        -- if success then add to sols
        Left _ -> getCastsForTy ty tl (hd:sols)
        -- if failure then add all chains starting with cand to cands
        Right _ -> do
          -- find all funs who's domTy unifies with the current cand's ranTy
          castTys <- gets icCastTys
          suffixIds <- lift $ filterCastsByDom (IM.toList castTys) candRanTy
          -- get costs and names
          let (curNames, curVids, curCost) = hd
          castInfo <- gets icCastInfo
          let castInfoF = \c -> fromMaybe (error "InsertCasts:getNextCandidates: cast not in info!") $ IM.lookup c castInfo
          let castInfos = map castInfoF suffixIds          
          let nextCands = map (\(nams,vids,cost) -> (curNames ++ nams, curVids ++ vids, curCost + cost)) castInfos
          let nextCandsAsc = sortBy (\(_,_,c1) -> \(_,_,c2) -> compare c1 c2) nextCands
          -- TODO filter out those with repeated vids?
          -- add these to cands list
          getCastsForTy ty (tl ++ nextCandsAsc) sols
    -- if doesn't
    Right _ -> do
      -- then discard this cand, and continue
      getCastsForTy ty tl sols

-- |All redist and relayout functions.
-- |Note: head of lists are applied first
castNames2 :: CastNames
castNames2 = [
 (["readVMap"], 1), (["saveVMap"], 5),  (["sortVMap"], 100), (["readHMap"], 1),
 (["mirrVMap"], 200), 
 (["sieveSMap"], 10), 
 (["repartVMap4"], 500) --, (["id"], 0)
  ]

--type Sol = (E.Expr, TyEnv, Cost)

-- TODO discard solutions that would lead to mirroring all inputs...
-- 8/jul14 STILL TODO!!!

-- |findCasts funTys funIds ast. Searches for applications of cast 
-- |functions that make ast's types unify. Solutions are returned in
-- |order of ascending cost. Works by identifying places that casts are
-- |needed by mending broken constraints by inserting "cast :: a -> b".
-- |Then gets the types inferred for these dummy casts, and searches for
-- |chains of redist functions with types x -> y that unify with them 
-- |(e.g. a -> b :=: x -> y unifies). Then replaces these dummy casts with 
-- |these chains of functions. 
findCasts2 :: Int -> FunTys -> FunIds -> E.Expr -> IdxMonad IO ([Sol], String)
findCasts2 20 _ _ _ = return ([], "findCasts reached maximum depth!") -- check depth
findCasts2 depth funTys funIds ast = do
  lift $ putStrE "entered findCasts"
  -- find places where casts are needed (inserts dummy cast functions with type a -> b)
  (sols1, msg1) <- findCasts1 [(["cast"], 1)] funTys funIds ast
  let sols2 = sortBy (\(_,_,c1) -> \(_,_,c2) -> compare c1 c2) sols1

  -- get eids and types of casts
  sols3 <- mapM (\(ast1, tys1, cost1) -> do
    let eids = getCastAppEids ast1
    castTys1 <- getExprTys (IM.fromList tys1) $ map snd eids
    let castTys2 = map (\(aeid, (feid, ty)) -> ((aeid, feid), ty)) $ zip (map fst eids) castTys1
    return (ast1, castTys2)) sols1

  -- make cast info
  let castInfos = map (\(cid,(nams,cost)) -> let vids = map (\nam -> fromMaybe (error $ "cast " ++ nam ++ " not in fun ids!") (DM.lookup nam funIds)) nams in (cid, (nams, vids, cost))) $ zip [0..] castNames2
  let casts0 = map snd castInfos
  let castInfo = IM.fromList castInfos

  -- create start state
  castTys <- getCastTypes funTys castInfo
  t0 <- lift $ getCurrentTime
  let st0 = ICState { icFunTys=funTys, icFunIds=funIds, 
    icCastInfo=castInfo,
    icCastTys=castTys,
    icDepth = 0,
    icTotalCost=0,
    icSolCount=0,
    icCurrentCost=0,
    icLowestCost=maxBound,
    icStartTime=t0,
    icDebugMsg="",
    icOptions=[],
    icCount=0 }

  -- find chains of funs that match each need castTy
  (sols4, st1) <- runStateT (mapM (\(ast1, castTys) -> do
    castSols <- mapM (\((aeid, feid), ty) -> do casts1 <- getCastsForTy ty casts0 [] ; return ((aeid,feid), ty, casts1)) castTys
    let castSols' = map (\((aeid, feid), ty, sols) -> trace ("cast" ++ (show (aeid, feid)) ++ ": " ++ (show $ percentTermConcrete ty) ++ " " ++ (showEmbeddedFuns $ stripTermLabelsRec ty) ++ "\n" ++ (show $ sortBy (\(_,_,c1) -> \(_,_,c2) -> compare c1 c2) sols) ++ "\n\n") $ ((aeid, feid), sortBy (\(_,_,c1) -> \(_,_,c2) -> compare c1 c2) sols)) castSols
    return (ast1, castSols')) sols3) st0

  -- replace dummy cast fun apps, with real chains of funs
  -- (by applying real funs to dummy casts, and then removing dummy casts)
  asts0 <- mapM (\(ast1, sols) -> do
    -- make casts map
    let casts = IM.fromList $ map (\((aeid, feid), (hd@(nams,vids,cost):tl)) -> (aeid, vids)) sols
    -- sum costs 
    let cost = sum $ map (\(eid, (hd@(nams,vids,cost):tl)) -> cost) sols
    -- apply these casts to ast1
    ast2 <- applyCastsToExpr castInfo casts ast1
    -- remove dummy casts
    let ast3 = E.removeFunApps (\(E.App _ fexp _) -> E.isVarExpr fexp && (E.getVarExprName fexp) == "cast") ast2
    lift $ putStr $ "\nBLA" ++ (E.showExprTreeWithIds ast2) ++ "\n\n" ++ "BLA2" ++ (show casts) ++ "\n\n"
    return (ast3, cost)) sols4

  -- RUN PFFB ON redistsTests1 pipe to foo, look at floccerrs. Inconsistant ids being used for casts (fun vids vs position in cast list)
  -- TODO 1) APPLY CASTS TO EXPR ABOVE IS NOT WORKING (try redistTest1, casts not injected into AST) - FIXED?
  -- TODO 2) INSERTING CASTs CAUSES "unknown cast".
  -- TODO 3) FILTER OUT SOLUTIONS THAT MIRROR EVERYTHING.

  -- only take 2 best asts
  let asts1 = take 2 asts0

  -- infer types for each complete ast
  sols <- mapM (\(ast', cost) -> do 
    res <- assignDepTypes3 funTys ast'
    case res of
      -- when succeeds, return
      Left tys -> return ([(ast', tys, cost)], "")
      -- when failed, try and had more casts to fix... 
      Right (con, parTys) ->  --findCasts2 (depth+1) funTys funIds ast'
        
                             error $ "Planner:InsertCasts:findCasts: solution doesn't type check:\n" ++ 
                                      (show con) ++ "\n" ++ (showExprWithTypes parTys ast') ++ "\n" ++ (E.showExprTreeWithIds ast')
    ) asts1 
  
  return (concat $ map fst sols, icDebugMsg st1 ++ (concat $ map snd sols))

findCasts :: FunTys -> FunIds -> E.Expr -> IdxMonad IO ([Sol], String)
findCasts = findCasts2 0
