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
module Compiler.Types2.FillGaps (possibleSubs, remRedundantDims, getRedundantDims, fillGapsInEnv) where

import Compiler.Front.Indices (Idx, IdxMonad, newidST) 
import Compiler.Front.Common (dtvids, listGet)
import Compiler.Front.ExprTree (Val(NullVal, I, B))

import qualified Compiler.Types2.TypeInfo as TI
import Compiler.Types2.TermLanguage
import Compiler.Types2.TypeAssignment
import Compiler.Types2.Variables
import Compiler.Types2.EmbeddedFunctions (getIdxTreeTy, getVarTreeTy, getSimpleFunTy)
import qualified Compiler.Types2.Substitutions as S

import Control.Monad.State.Strict (StateT, modify, lift, runStateT)
import Data.Functor.Identity (runIdentity)
import Data.List (subsequences, permutations, intercalate, unionBy)
import qualified Data.IntMap.Strict as IM
import qualified Data.Set as DS
import Data.Maybe (isJust, fromJust, fromMaybe)
import Debug.Trace (trace)

-- |namedTy takes a string and list of child types
-- |and returns the type term for it.
namedTy :: String -> [TyTerm] -> TyTerm
namedTy n l = Term (Tok (Ty n)) l

-- |tup termList. Makes a tuple term.
tup :: [TyTerm] -> TyTerm
tup l = Term TupTok l

fun :: TyTerm -> TyTerm -> TyTerm
fun v exp = namedTy "FFun" [v, exp]

app f a = namedTy "FApp" [f, a]

lit :: Val -> TyTerm
lit v = case v of
  NullVal -> namedTy "VNull" []
  I iv -> namedTy "VInt" [namedTy (show iv) []]
  B bv -> namedTy (if bv then "VTrue" else "VFalse") []
  other -> error $ "FillGaps:can't embed literal value " ++ (show v) ++ " in type term.\n"

ty :: String -> TyTerm
ty n = namedTy n []

tok :: String -> FunctionToken TyToken
tok n = Tok $ Ty n

-- |nestedTupleArity term. Counts the number of leaves of the tuple tree term.
nestedTupleArity :: TyTerm -> Int
nestedTupleArity (Term TupTok l) = sum $ map nestedTupleArity l
nestedTupleArity (LTerm _ TupTok l) = nestedTupleArity (Term TupTok l)
nestedTupleArity other = 1

-- |getRedundantDims types. Returns a list of dim vars that
-- |are only every used as mirror dims, never as part, and so 
-- |are redundant i.e. can be replaced with ().
getRedundantDims :: [TyTerm] -> ([TyTerm], [TyTerm], [TyTerm])
getRedundantDims types = (map Var $ DS.toList redVars, map Var $ DS.toList $ mirrVars `DS.difference` redVars, map Var $ DS.toList $ partVars)
  where -- get all mirror dim terms
        mirrTerms = concat $ map (\(n,idx) -> map (DS.toList . getSubTerms (tok n) idx) types) TI.mirrDimLocations
        mirrVars = DS.unions $ map (DS.fromList . getVarIdsInTerm) $ concat mirrTerms
        -- get all partition dim terms
        partTerms = concat $ map (\(n,idx) -> map (DS.toList . getSubTerms (tok n) idx) types) TI.partDimLocations
        partVars = DS.unions $ map (DS.fromList . getVarIdsInTerm) $ concat partTerms
        -- find mirror dims never used as partition dims
        redVars = mirrVars `DS.difference` partVars

-- |remRedundantDims types. Finds all redundant mirror dims in
-- |types and replaces then with Null.
remRedundantDims :: IM.IntMap TyTerm -> IM.IntMap TyTerm
remRedundantDims types = IM.map (runIdentity . S.applySubstsMap subs) types 
  where (redVars, mirrVars, partVars) = getRedundantDims $ IM.elems types
        subs = S.fromDisjointList $ map (\v -> (v, Term (Tok (Ty "Null")) [])) redVars

-- TODO put into unify function.

data FunKind =
    AllFuns -- all of options below (currently same as projandpermutefuns)
  | PermuteFuns -- all permutations of inputs
  | ProjAndPermuteFuns -- just projects and permutes subsets of inputs
  -- TODO options for DMap partition functions 

-- |possibleSubs term. Visits term looking for parts of the type that
-- |are still abstract (type variables) and return possible subsitutions
-- |that would make them concrete. If a term is already concrete returns [].
  -- TODO add DMap...
{-possibleSubs :: Monad m => TyTerm -> IdxMonad m (IM.IntMap [TyTerm])
possibleSubs term = case term of
  -- DArr
  (Term (Tok (Ty "DArr")) [mode, keyT, valT, layF, partF, partD, mirrD]) -> do
     -- output type: flat tuple of integers (permutations of inputs)
    lf <- possibleFuns PermuteFuns IM.empty keyT (Just $ tup $ replicate (nestedTupleArity keyT) intTy) layF
    -- output type: any (permutations of all subsets of inputs)
    pf <- possibleFuns ProjAndPermuteFuns IM.empty keyT Nothing partF
    case mode of
      Var i -> return $ IM.unionsWith (++) [lf, pf, IM.singleton i [ty "Arr", ty "Stm"]]
      _     -> return $ IM.unionWith (++) lf pf
  -- DMap 
  (Term (Tok (Ty "DMap")) [mode, keyT, valT, ordF, partF, partD, mirrD]) -> do
    -- output type: any (permutations of all subsets of inputs)
    {-pf <- possibleFuns ProjAndPermuteFuns IM.empty (tup [keyT, valT]) Nothing partF
    case mode of
      Var i -> return $ IM.unionsWith (++) [pf, IM.singleton i [ty "Stm", ty "Vec", ty "Tree", ty "Hash"]]
      _     -> return pf-} -- TODO FIX THIS SO DOESN'T GO ON FOREVER
    {-case mode of
      Var i -> return $ IM.singleton i [ty "Stm", ty "Vec", ty "Tree", ty "Hash"]
      _     -> return IM.empty-}
    return IM.empty
  -- visit all subterms
  (Term _ l) -> do
    l' <- mapM possibleSubs l
    return $ IM.unionsWith (++) l'
  -- other
  other -> return $ IM.empty-}

-- |fillGapsInEnv termEnv. Searches the terms in the env, looking for gaps,
-- |finds possible values for each one, groups by term var id, and returns 
-- |a map from term var ids to possible lists of values. 
fillGapsInEnv :: Monad m => IM.IntMap TyTerm -> IdxMonad m (IM.IntMap TyTerm)
fillGapsInEnv env = do
  -- get possible subs from all terms in the env
  let env' = IM.toAscList env 
  maps <- mapM (\(k,t) -> do l <- possibleSubs t; return l) env'
  -- union all possibilities for each term var together (where we use 'unifySimple' for equality)
  --let m = IM.unionsWith (L.unionBy bijTmEq) maps 
  let m = IM.unionsWith (++) maps
  -- check that only one possibility per var (at the moment just returning defaults, not multiple options)
  let resSubs = IM.mapMaybeWithKey (\k -> \subs -> if subs /= [] 
                                      then (if allEq subs 
                                            then Just $ head subs 
                                            else error $ "FillGaps:fillGapsInEnv: multiple defaults for same var " ++ (show k) ++ "!? " ++ (show subs))
                                      else Nothing) m
  return resSubs

-- |possibleSubs term. Visits term looking for parts of the type that
-- |are still abstract (type variables) and return possible subsitutions
-- |that would make them concrete. If a term is already concrete returns [].
possibleSubs :: Monad m => TyTerm -> IdxMonad m (IM.IntMap [TyTerm])
possibleSubs term = case stripTermLabels term of
  -- visit all subterms
  (Term tok l) -> do
    l' <- mapM possibleSubs l
    case tok of
      (Tok (Ty _)) -> do
        s <- possibleSubsInTy term
        return $ IM.unionsWith (++) (s:l')
      other -> do
        return $ IM.unionsWith (++) l'
  -- other
  other -> return $ IM.empty

allEq :: Eq a => [a] -> Bool
allEq [] = True
allEq [a] = True
allEq (h1:h2:r) = (h1 == h2) && (allEq (h2:r)) 

headL :: [a] -> [a]
headL [] = []
headL (h:r) = [h]

-- |possibleSubsInTy term. For this term return all possible substitutions
-- |that would make the term concrete. This includes filling in an omitted
-- |mode/partition function/layout function.
possibleSubsInTy :: Monad m => TyTerm -> IdxMonad m (IM.IntMap [TyTerm])
possibleSubsInTy term@(Term (Tok (Ty name)) l) = do
  -- check num ty params
  if TI.numParams name /= -1 && length l /= TI.numParams name
  then error $ "Types:FillGaps:possibleSubsInTy: incorrect num type params: " ++ (show term)
  else return ()
  -- check for vars with defaults
  let defSubs = map (\(idx,v) -> if isJust $ isVar v 
                                 then maybe IM.empty (\ty -> IM.singleton (fromJust $ isVar v) [ty]) $ TI.typeDefault name idx 
                                 else IM.empty) $ zip [0..] l
  -- possible subs
  let posSubs = IM.unionsWith (++) defSubs
  return $ posSubs

  -- check for modes
  {-let modeLocs = TI.typeModes name
  s1 <- mapM (\(idx,opts) -> return $ IM.singleton idx $ map (\n -> namedTy n []) opts) modeLocs
  let s1' = IM.unionsWith (++) s1
  -- get dom and range type for funs
  let dt = (case name of
              "DMap" -> tup [l !! 1, l !! 2]
              "DArr" -> l !! 1
              other -> error $ "Please extend Compiler/Types/FillGaps.hs:possibleSubsInTy to support " ++ other)
  let rt = (case name of 
              "DMap" -> Nothing
              "DArr" -> Just $ tup $ replicate (nestedTupleArity $ l !! 1) intTy
              other -> error $ "Please extend Compiler/Types/FillGaps.hs:possibleSubsInTy to support " ++ other)
  -- check for layout funs
  let layFunLocs = TI.layFuns name
  s2 <- mapM (\idx -> possibleFuns PermuteFuns IM.empty dt rt $ l !! idx) layFunLocs
  let s2' = IM.unionsWith (++) s2
  -- check for partition funs
  let partFunLocs = TI.partFuns name
  s3 <- mapM (\idx -> possibleFuns ProjAndPermuteFuns IM.empty dt rt $ l !! idx) partFunLocs
  let s3' = IM.unionsWith (++) s3
  -- union them-}
  -- TODO FIX: Currently causes infinite loop
  --return $ IM.empty
  --return $ IM.unionsWith (++) [s1',s2',s3']
possibleSubsInTy other = return IM.empty

-- |possibleFuns tyEnv domTy ranTy funTerm. Visits the funTerm and any funTerms nested inside the
-- |function's body, and returns possible values for any that are still just type vars. 
-- |This is not guaranteed to work (the nested functions bit) because we aren't guaranteed to
-- |know the types of the function's domains.
possibleFuns :: Monad m => FunKind -> IM.IntMap TyTerm -> TyTerm -> Maybe TyTerm -> TyTerm -> IdxMonad m (IM.IntMap [TyTerm])
possibleFuns funKind env domTy ranTy funT = case stripTermLabels funT of
  -- fun is just a var
  (Var vid) -> do
    funs <- funSpace funKind domTy ranTy
    return $ IM.singleton vid funs
  -- deal with boths
  (Term (Tok (Ty "FBoth")) l) -> do
    l' <- mapM (possibleFuns funKind env domTy ranTy) l
    return $ IM.unionsWith (++) l' 
  -- recursively visit function looking for fun apps
  -- the apply funs that are just type vars
  (Term (Tok (Ty "FFun")) [idT, expT]) -> do
    let env' = getIdxTreeTy ("FillGaps:possibleFuns:") (idT, domTy)
    funs <- possibleAppFuns (env' `IM.union` env) expT 
    return funs
  -- deal with function generators
  (Term (Tok (Ty "GFst")) [f]) -> case stripTermLabels domTy of
    (Term TupTok [v1,v2]) -> possibleFuns funKind env v1 Nothing f
    other -> error $ "FillGaps:possibleFuns: illegal GFst dom type. Must be a pair!\n" ++ (show domTy)
  (Term (Tok (Ty "GSnd")) [f]) -> case stripTermLabels domTy of
    (Term TupTok [v1,v2]) -> possibleFuns funKind env v2 Nothing f
    other -> error $ "FillGaps:possibleFuns: illegal GSnd dom type. Must be a pair!\n" ++ (show domTy)
  other -> error $ "FillGaps:possibleFuns: invalid funTerm: " ++ (show funT)

-- |possibleAppFuns tyEnv term. Visits subtrees in term, looking for FApp's whose 
-- |function's are just type vars, and (trys to) return possible function values for 
-- |those vars.
-- TODO change so uses proper type inference to get the input and output types of unknown
--   functions.
possibleAppFuns :: Monad m => IM.IntMap TyTerm -> TyTerm -> IdxMonad m (IM.IntMap [TyTerm])
possibleAppFuns env exp = case stripTermLabels exp of
  -- fun application
  (Term (Tok (Ty "FApp")) [funT, argT]) -> do
    let argTy = getVarTreeTy ("possibleAppFuns: " ++ (show exp)) env argT
    funs1 <- possibleFuns AllFuns env argTy Nothing funT
    case funT of
      (Term (Tok (Ty "FFun")) [idT, expT]) -> do
        let env' = getIdxTreeTy ("FillGaps:possibleAppFuns") (idT, argT)
        funs2 <- possibleAppFuns (env' `IM.union` env) argT
        return $ IM.unionWith (++) funs1 funs2
      other -> do
        funs2 <- possibleAppFuns env argT
        return $ IM.unionWith (++) funs1 funs2
  -- tuple
  (Term TupTok l) -> do
    l' <- mapM (possibleAppFuns env) l
    return $ IM.unionsWith (++) l'
  -- lits
  (Term (Tok (Ty n)) []) -> case n of
    "VNull" -> return IM.empty
    "VTrue" -> return IM.empty
    "VFalse" -> return IM.empty
    ('V':'i':'n':'t':_) -> return IM.empty
  -- var (ignore as if was fun var would have been caught in FApp)
  (Var i) -> return IM.empty
  other -> error $ "FillGaps:possibleAppFuns: invalid exp: " ++ (show exp)
    
-- |makeTup list. Takes a list and returns Null if it's
-- |empty, the only val if it has length 1, or a tuple otherwise. 
makeTup :: [TyTerm] -> TyTerm
makeTup [] = lit NullVal
makeTup [v] = v
makeTup l = tup l

-- |termToVarTree term. Takes a tree of tuples and 
-- |replaces all leaves with new type vars.
termToVarTree :: Monad m => TyTerm -> IdxMonad m TyTerm
termToVarTree term = case stripTermLabels term of
  (Term TupTok l) -> do
    l' <- mapM termToVarTree l
    return $ tup l'
  other -> do
    vid <- newidST dtvids
    return $ Var vid

-- |applyVarSubs exp terms1 terms2. Applies substitutions from
-- |terms1 to terms2 to exp.
applyVarSubs :: TyTerm -> [TyTerm] -> [TyTerm] -> TyTerm
applyVarSubs exp l1 l2 = applyVarSubsts subs exp
  where subL = map (\(Var vid,t2) -> (vid, t2)) $ zip (map stripTermLabels l1) l2
        subs = fromDisjointList subL

-- TODO uses getSimpleFunTy so only works for simple proj and permute funs.
-- |funHasCorrectType correctType domainType funTerm. Returns true if
-- |the type of funTerm is correctTy, given a domain type domainType.
funHasCorrectType :: TyTerm -> TyTerm -> TyTerm -> Bool
funHasCorrectType correctTy domTy funTerm = (correctTy == funTy) 
  where funTy = getSimpleFunTy ("FillGaps:funHasCorrectType: " ++ (show (correctTy, domTy, funTerm))) domTy funTerm

-- |funSpaceWithRanTy funKind domTy ranTy. Returns all functions that 
-- |funSpace yields, restricted to those where the range types (if specified)
-- |are what they should be.
funSpaceWithRanTy :: Monad m => FunKind -> TyTerm -> Maybe TyTerm -> IdxMonad m [TyTerm]
funSpaceWithRanTy funKind domTy ranTyMb = do
  funs <- funSpace funKind domTy ranTyMb
  case ranTyMb of
    -- funs with correct output type
    Just ranTy -> return $ filter (funHasCorrectType (Term FunTok [domTy, ranTy]) domTy) funs
    -- all funs
    Nothing    -> return funs

-- |funSpace domTy ranTy. Returns a list of all functions that project
-- |and permute subsets of the input tuple. This does not include
-- |repetitions of vars, or nested tuple expressions, just flat ones. 
funSpace :: Monad m => FunKind -> TyTerm -> Maybe TyTerm -> IdxMonad m [TyTerm]
funSpace funKind domTy ranTyMb = do
  -- make input vars for dom type
  idT <- termToVarTree domTy 
  -- get input vars
  let inVars = map Var $ getVarIdsInTerm idT
  case funKind of
    AllFuns -> do
      -- permute is a subset of proj and permute, so for now just
      -- same as proj and permute funs
      funSpace ProjAndPermuteFuns domTy ranTyMb
    ProjAndPermuteFuns -> do
      -- get all permutations of all subsets of those vars
      let exps = concat $ map (\seq -> permutations seq) $ subsequences inVars
      -- get all functions
      return $ map (\e -> namedTy "FFun" [idT, makeTup e]) exps
    -- TODO: Note broken for non DArr types. Need to filter out
    -- functions that break type safety (split inVars and outVars 
    -- into subsets one per type, and only consider permuntations of
    -- those.)
    PermuteFuns -> case ranTyMb of
      -- try all permutations of in -> out var substs, and 
      -- apply those to the output type (so has tuple structure 
      -- of the output type)
      Just ranTy -> do
        -- get all permutations of vars that fit the type given...
        expT <- termToVarTree ranTy
        let outVars = map Var $ getVarIdsInTerm expT
        let numOuts = length outVars -- TODO consider multiple uses of the same input var?
        let varLists = concat $ map permutations $ filter (\l -> length l == numOuts) $ subsequences inVars
        -- make and apply substitutions for each permutation found
        let exps = map (applyVarSubs expT outVars) varLists
        -- get all functions
        let funs = map (\e -> namedTy "FFun" [idT, e]) exps
        return funs
      -- all permutations of in vars in a flat tuple
      Nothing -> do
        let perms = permutations inVars 
        return $ map (\l -> namedTy "FFun" [idT, makeTup l]) perms
        

