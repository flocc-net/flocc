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
module Compiler.Types.EmbeddedFunctions (embedFun, fullySimplifyFun, fullySimplifyFuns, simplifyFunsInEnv, showEmbeddedFuns,
  applyDimGens, applyDimGensInEnv, getIdxTreeTy, getVarTreeTy, getSimpleFunTy, unembedFun) where

import Compiler.Front.Common (vids, eids, dtvids, listGet)
import Compiler.Front.Indices (Idx, IdxMonad, newidST)
import Compiler.Front.ExprTree hiding (Var)
import qualified Compiler.Front.ExprTree as E
import Compiler.Front.Preprocess

import qualified Compiler.Types.TypeInfo as TI
import Compiler.Types.TermLanguage
import Compiler.Types.TypeAssignment
import Compiler.Types.Variables

import Data.Maybe (catMaybes, isJust, fromJust, fromMaybe)
import Data.List (intercalate, isPrefixOf)
import Debug.Trace (trace)
import Control.Monad (filterM)
import Control.Monad.State.Strict (StateT, modify, lift, gets, runStateT, evalStateT)
import Data.Set (Set, member, (\\))
import qualified Data.Set (toList, fromList, null)
import qualified Data.IntMap.Strict as IM
import qualified Data.Map as DM

-- TODO use intmaps not lists
-- TODO fix fact that funSpace ranTy case breaks type safety for
--   function whose domain tuples contain more than 1 type.

getTyName :: TyTerm -> String
getTyName (Term (Tok (Ty n)) _) = n
getTyName t = error $ "EmbeddedFuns:getTyName: invalid type term " ++ (show t)

showEmbeddedFuns :: TyTerm -> String
showEmbeddedFuns (Term t l) = case t of
    TupTok -> "(" ++ (intercalate ", " $ map rec l) ++ ")"
    FunTok -> case l of 
      (a:b:[]) -> (rec a) ++ " -> " ++ (rec b)  
      other -> "showEmbeddedFuns:invalid fun term"
    Tok (Ty n) -> case (n,l) of
      ("VNull",_) -> "null"
      ("VTrue",_) -> "True"
      ("VFalse",_) -> "False"
      ("VInt",_) -> show $ ((read $ getTyName $ head l) :: Int)
      ("FId",_) -> "id"
      ("FFst",_) -> "fst"
      ("FSnd",_) -> "snd" 
      ("FSwap",_) -> "swap" 
      ("FNull",_) -> "nullF"
      ("FBoth", l) -> "(" ++ (intercalate " && " $ map rec l) ++ ")"
      ("FPair", a:b:[]) -> "(" ++ (rec a) ++ "x" ++ (rec b) ++ ")"
      ("FSeq", a:b:[]) -> "(" ++ (rec a) ++ " . " ++ (rec b) ++ ")"
      ("FFun", a:b:[]) -> "(\\" ++ (rec a) ++ " -> " ++ (rec b) ++ ")"
      ("FApp", [f,v]) -> "(" ++ (rec f) ++ " " ++ (rec v) ++ ")"
      other  -> "(" ++ n ++ " " ++ (intercalate " " $ map rec l) ++ ")"
  where rec = showEmbeddedFuns
showEmbeddedFuns (UniVar vid) = "iv" ++ (show vid)
showEmbeddedFuns (Var vid) = "v" ++ (show vid)
showEmbeddedFuns (Ref eid) = "r" ++ (show eid)

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
  other -> error $ "EmbeddedFunctions: can't embed literal value " ++ (show v) ++ " in type term.\n"

-- |getIdxTreeTy (idxTerm, ty). Returns an environment mapping var idxs to type terms.
getIdxTreeTy :: String -> (TyTerm, TyTerm) -> IM.IntMap TyTerm
getIdxTreeTy err pr@(idxT, ty) = case (idxT, ty) of
  (Term TupTok l1, Term TupTok l2) | length l1 == length l2 -> IM.unions $ map (getIdxTreeTy $ err ++ "\ngetIdxTreeTy:" ++ (show pr)) $ zip l1 l2
  (Var i, t) -> IM.singleton i t
  other -> error $ err ++ "\nEmbeddedFunctions:getIdxTreeTy: invalid pattern/type combination: " ++ (show idxT) ++ "\n" ++ (show ty)

-- |getVarTreeTy env term. Returns the type of term by looking up the types of vars in env, and 
-- |composing tuples of these together. NOTE: Will fail if more than just simple tuples of vars,
-- |e.g. if it includes a function application!
getVarTreeTy :: String -> IM.IntMap TyTerm -> TyTerm -> TyTerm
getVarTreeTy err env term = case term of
  (Var i) -> case IM.lookup i env of
    Just t  -> t
    Nothing -> error $ err ++ "\nEmbeddedFunctions:getVarTreeTy: type of var not in env!\n" ++ (show term) ++ "\n" ++ (show env)
  (Term TupTok l) -> tup l'
    where l' = map (getVarTreeTy (err ++ "\ngetVarTreeTy: " ++ (show term)) env) l
  (Term (Tok (Ty name)) []) -> case name of
    "VNull" -> nullTy
    "VTrue" -> boolTy
    "VFalse" -> boolTy
    ('V':'I':'n':'t':_) -> intTy
    other -> error $ err ++ "\nEmbeddedFunctions:getVarTreeTy: can't handle named term, only supports typing simple tuples of vars!\n" ++ (show term) ++ "\n" ++ (show env)
  other -> error $ err ++ "\nEmbeddedFunctions:getVarTreeTy: only supports typing simple tuples of vars!\n" ++ (show term) ++ "\n" ++ (show env)

-- TODO broken if involves function apps etc. Should change to
--      use proper type inference! 
-- |getSimpleFunTy domTy funTerm. Returns the type of funTerm given
-- |the domain type domTy, assuming funTerm is a simple tuple proj permute function.
getSimpleFunTy :: String -> TyTerm -> TyTerm -> TyTerm
getSimpleFunTy err domTy fn@(Term (Tok (Ty "FFun")) [idT, expT]) = (Term FunTok [domTy, expTy])
  where err' = (err ++ "\ngetSimpleFunTy:" ++ (show domTy) ++ " <-> " ++ (show fn))
        varTyEnv = getIdxTreeTy err' (idT, domTy)
        expTy = getVarTreeTy err' varTyEnv expT
getSimpleFunTy err domTy funTerm = error $ err ++ "\nEmbeddedFunctions:getSimpleFunTy: can only return type of FFun terms:\n" ++ (show funTerm)

simplifyFunsInEnv :: Monad m => TyEnv -> IdxMonad m (TyEnv, [(TyTerm, TyTerm)])
simplifyFunsInEnv env = do
  --res <- mapM (\(k, Scheme l t) -> do t' <- expandFunArgs t ; (t'', subs) <- simplifyFuns (propagateFBoths t'); return (k, Scheme l t'', subs)) env
  --res <- mapM (\(k, Scheme l t) -> do (t', subs) <- fullySimplifyFun (propagateFBoths t); return (k, Scheme l t', subs)) env
  res <- mapM (\(k, Scheme l t) -> do (t', subs) <- fullySimplifyFuns t; return (k, Scheme l t', subs)) env
  let (keys, schemes, subs) = unzip3 res
  return (zip keys schemes, concat subs)

-- |simplifyFuns t. Simplifies all sub terms that are embedded functions.
-- |Calls simplifyFun twice so that after built in functions are expanded, they are applied.
fullySimplifyFuns :: Monad m => TyTerm -> IdxMonad m (TyTerm, [(TyTerm, TyTerm)])
--simplifyFuns term = mapTermM (\t -> if isFunTerm t then simplifyFun t >>= simplifyFun else return t) term
fullySimplifyFuns term = case term of
  (Term t l) -> do
    res <- mapM fullySimplifyFuns l
    let (terms, subs1) = unzip res
    (term', subs2) <- fullySimplifyFun $ Term t terms
    (term'', subs3) <- fullySimplifyFun term'
    return (term'', (concat subs1) ++ subs2 ++ subs3)
  other -> simplifyFun other

-- |isFunTerm term. Returns true if the term is an embedded function.
isFunTerm :: TyTerm -> Bool
isFunTerm (Term (Tok (Ty n)) _) = elem n funTermNames
isFunTerm _ = False

funTermNames = ["FId", "FFst", "FSnd", "FLft", "FRht", "FSwap", "FNull", "FDup", "FPair", "FSeq", "FBoth", "FFun", "GFst", "GSnd", "GRem"] 

-- TODO add FLft and FRht (or express some other way...)
-- FLft = (FDup (FSeq FFst FFst) (FSeq FFst FSnd))
-- FRht = (FDup (FSeq FSnd FFst) (FSeq FSnd FSnd)) 

-- |combinations ll. Returns list of all combinations of elements 
-- |drawn from the sublists of ll.
combinations :: [[a]] -> [[a]]
combinations (hd:[]) = map (\x -> [x]) hd
combinations (hd:tl) = concat $ map (\h -> map (\t -> (h:t)) $ combinations tl) hd
combinations [] = []

-- |fromBoth term. If term is an FBoth returns list of it's children
-- |otherwise returns singleton list containing term.
fromFBoth :: TyTerm -> [TyTerm]
fromFBoth (Term (Tok (Ty "FBoth")) l) = l
fromFBoth other = [other]

-- |propagateFBoths term. Traverses term, propagating FBoths to the 
-- |root, by taking all combinations of fboth children at each node.
propagateFBoths :: TyTerm -> TyTerm
propagateFBoths term = case term of
  -- recursively propagate boths up to root
  (Term (Tok (Ty other)) l) ->     
    case clists of
      -- if 0/1 child, just return as is
      [] -> (Term (Tok (Ty other)) [])
      [child] -> (Term (Tok (Ty other)) child)
      -- if more than one combination create an FBoth
      clist -> Term (Tok (Ty "FBoth")) $ map (\c -> (Term (Tok (Ty other)) c)) $ clist
    where -- get child lists
          l' = map fromFBoth l
          -- get all combinations of children
          clists = combinations l'
  -- base case
  other -> other

-- |applyToFuns fun ty. Recusively applies f to every fun embedded in ty.
-- TODO change to use TypeInfo...
applyToFuns :: Monad m => (TyTerm -> m TyTerm) -> TyTerm -> m TyTerm
applyToFuns f term = case term of
{-  (Term (Tok (Ty "DMap")) [mode, keyT, valT, ordF, parF, parD, mirD]) -> do
    ordF' <- f ordF
    parF' <- f parF
    return $ namedTy "DMap" [mode, keyT, valT, ordF', parF', parD, mirD]
  (Term (Tok (Ty "DArr")) [mode, idxT, valT, layF, parF, parD, mirD]) -> do
    layF' <- f layF
    parF' <- f parF
    return $ namedTy "DMap" [mode, idxT, valT, layF', parF', parD, mirD]-}
  (Term (Tok (Ty name)) l) -> do
    -- check num ty params
    if TI.numParams name /= -1 && length l /= TI.numParams name
    then error $ "Types:EmbeddedFuns:applyToFuns: incorrect num type params: " ++ (show term)
    else return ()
    -- apply to children  
    l' <- mapM (applyToFuns f) l
    -- apply to all functions in this type
    fs <- mapM (\idx -> do f' <- f $ listGet "EmFuns:applyToFuns:1" l' idx ; return (idx,f')) $ TI.funs name
    -- replace old functions with new ones
    let l'' = map (\idx -> fromMaybe (listGet "EmFuns:applyToFuns:2" l' idx) (lookup idx fs)) [0..((length l)-1)]
    return $ namedTy name l''
  (Term tok l) -> mapM (applyToFuns f) l >>= (return . (Term tok))
  other -> return other

-- |fullySimplify term. Keeps simplifying until no changes are made.
fullySimplifyFun :: Monad m => TyTerm -> IdxMonad m (TyTerm, [(TyTerm, TyTerm)])
fullySimplifyFun term = do
  -- propage fboths
  term' <- applyToFuns (\t -> return $ propagateFBoths t) term
  -- expandFunArgs
  term'' <- applyToFuns expandFunArgs term'
  -- simplify
  (term''', subs) <- simplifyFun term''
  -- iterate?
  {-if (term /= term''') 
  then do
    (term'''', subs') <- fullySimplifyFun term'''
    return (term'''', subs ++ subs')
  else-} 
  return (term''', subs)

-- |simplifyFun term. Expands all built in functions, and 
-- |applies all expanded functions. Note! Must call twice - once
-- |to expand builtins, and the next to apply them.
-- |Remember: When adding new builtin functions and function
-- |generators to add them to the funTermNames list.
simplifyFun :: Monad m => TyTerm -> IdxMonad m (TyTerm, [(TyTerm, TyTerm)])
simplifyFun term = case term of
  -- built in functions:
  -- id
  (Term (Tok (Ty "FId")) []) -> do
    vid <- newidST dtvids
    let f' = fun (Var vid) (Var vid)
    return (f', [(term, f')])
  -- fst
  (Term (Tok (Ty "FFst")) []) -> do
    v1 <- newidST dtvids
    v2 <- newidST dtvids
    let f' = fun (tup [Var v1, Var v2]) (Var v1)
    return (f', [(term, f')])
  -- snd
  (Term (Tok (Ty "FSnd")) []) -> do
    v1 <- newidST dtvids
    v2 <- newidST dtvids
    let f' = fun (tup [Var v1, Var v2]) (Var v2)
    return (f', [(term, f')])
  -- lft
  (Term (Tok (Ty "FLft")) []) -> do
    [v1, v2, v3, v4] <- mapM (\_ -> (newidST dtvids) >>= (return.Var)) [0..3]
    let f' = fun (tup [tup [v1, v2], tup [v3, v4]]) (tup [v1, v3]) 
    return (f', [(term, f')])
  -- rht
  (Term (Tok (Ty "FRht")) []) -> do
    [v1, v2, v3, v4] <- mapM (\_ -> (newidST dtvids) >>= (return.Var)) [0..3]
    let f' = fun (tup [tup [v1, v2], tup [v3, v4]]) (tup [v2, v4]) 
    return (f', [(term, f')])
  -- swap
  (Term (Tok (Ty "FSwap")) []) -> do
    v1 <- newidST dtvids
    v2 <- newidST dtvids
    let f' = fun (tup [Var v1, Var v2]) (tup [Var v2, Var v1])
    return (f', [(term, f')])
  -- null
  (Term (Tok (Ty "FNull")) []) -> do
    vid <- newidST dtvids
    let f' = fun (Var vid) (lit NullVal)
    return (f', [(term, f')])
  -- pair
  (Term (Tok (Ty "FPair")) [f1, f2]) -> do
    v1 <- newidST dtvids
    v2 <- newidST dtvids
    let f' = fun (tup [Var v1, Var v2]) (tup [app f1 (Var v2), app f2 (Var v1)])
    return (f', [(term, f')])
  -- duplicate pair
  (Term (Tok (Ty "FDup")) [f1, f2]) -> do
    v <- newidST dtvids
    let f' = fun (Var v) (tup [app f1 (Var v), app f2 (Var v)])
    return (f', [(term, f')])
  -- seq
  (Term (Tok (Ty "FSeq")) [f1, f2]) -> do
    v1 <- newidST dtvidss
    let f' = fun (Var v1) (app f1 (app f2 (Var v1)))
    return (f', [(term, f')])
  -- both
  (Term (Tok (Ty "FBoth")) l) -> do
    l' <- mapM simplifyFun l
    let (ts, subs) = unzip l'
    return (Term (Tok (Ty "FBoth")) ts, concat subs)
  -- function generators:
  (Term (Tok (Ty "GFst")) [f]) -> case f of
    -- if is an abstraction that can be analysed
    (Term (Tok (Ty "FFun")) [idT@(Term TupTok [v1, v2]), expT]) -> do
      let expsToRemove = Data.Set.fromList $ map Var $ getVarIdsInTerm v2
      expT' <- filterTerm (predVarsNotIn expsToRemove) expT
      let f' = namedTy "FFun" [v1, expT']
      return (f', [(term, f')])
    -- can't run generator
    _ -> return (term, []) 
  (Term (Tok (Ty "GSnd")) [f]) -> case f of
    -- if is an abstraction that can be analysed
    (Term (Tok (Ty "FFun")) [idT@(Term TupTok [v1, v2]), expT]) -> do
      let expsToRemove = Data.Set.fromList $ map Var $ getVarIdsInTerm v1
      expT' <- filterTerm (predVarsNotIn expsToRemove) expT
      let f' = namedTy "FFun" [v2, expT']
      return (f', [(term, f')])
    -- can't run generator
    _ -> return (term, []) 
  (Term (Tok (Ty "GLft")) [f]) -> case f of
    -- if is an abstraction that can be analysed
    (Term (Tok (Ty "FFun")) [idT@(Term TupTok [Term TupTok [v1, v2], Term TupTok [v3, v4]]), expT]) -> do
      let expsToRemove = Data.Set.fromList $ map Var $ (getVarIdsInTerm v2) ++ (getVarIdsInTerm v4)
      expT' <- filterTerm (predVarsNotIn expsToRemove) expT
      let f' = namedTy "FFun" [Term TupTok [v1,v3], expT']
      return (f', [(term, f')])
    -- can't run generator
    _ -> return (term, []) 
  (Term (Tok (Ty "GRht")) [f]) -> case f of
    -- if is an abstraction that can be analysed
    (Term (Tok (Ty "FFun")) [idT@(Term TupTok [Term TupTok [v1, v2], Term TupTok [v3, v4]]), expT]) -> do
      let expsToRemove = Data.Set.fromList $ map Var $ (getVarIdsInTerm v1) ++ (getVarIdsInTerm v3)
      expT' <- filterTerm (predVarsNotIn expsToRemove) expT
      let f' = namedTy "FFun" [Term TupTok [v2,v4], expT']
      return (f', [(term, f')])
    -- can't run generator
    _ -> return (term, []) 
  (Term (Tok (Ty "GRem")) [f]) -> case f of
    -- if is an abstraction that can be analysed
    (Term (Tok (Ty "FFun")) [idT, expT]) -> do
      -- get all param vars
      let allVids = Data.Set.fromList $ getVarIdsInTerm idT
      -- get vars currently returned
      let curVids = Data.Set.fromList $ getVarIdsInTerm expT
      -- therefore list remaining/non-returned vars to 
      let remVids = allVids \\ curVids
      let expT' = case remVids of
                     l | Data.Set.null l -> lit NullVal
                     l  -> Term TupTok $ map Var $ Data.Set.toList remVids
      let f' = namedTy "FFun" [idT, expT']
      return (f', [(term, f')])
    -- can't run generator
    _ -> return (term, []) 
  -- recursive cases:  
  -- tuple
  (Term TupTok l) -> do
    l' <- mapM simplifyFun l
    let (terms, subs) = unzip l'
    return (tup terms, concat subs)
  -- fun abstraction
  (Term (Tok (Ty "FFun")) [itT, expT]) -> do
    (expT', subs) <- simplifyFun expT
    -- if it's a single application, 
    -- just replace with the function being applied
    case expT' of 
      -- a single application \bla -> (f bla) => f
      (Term (Tok (Ty "FApp")) [funT, argT]) | itT == argT -> return (funT, (term, funT):subs) 
      -- other funs
      other -> return (fun itT expT', subs)
  -- fun application 
  (Term (Tok (Ty "FApp")) [funT, argT]) -> do
    (funT', subs1) <- simplifyFun funT
    (argT', subs2) <- simplifyFun argT
    -- make new vars in ffun (make sure lambda vars are different
    --   because otherwise we may create unwanted constraints between
    --   different uses of id/fst/snd funs etc)
    -- try and apply function...
    case funT' of
       (Term (Tok (Ty "FFun")) [itT, expT]) -> case bindVars (itT, argT') of
         Just varEnv -> do 
           let f' = evalTerm varEnv expT
           return (f', (term,f'):(subs1 ++ subs2)) 
         Nothing -> return (app funT' argT', subs1 ++ subs2)
       other -> return (app funT' argT', subs1 ++ subs2)
  -- base cases
  other -> return (other, [])

-- TODO FIX RECURSIVE CASES ABOVE SO DONT HAVE TO CALL TWICE...
-- IS IT OK IF WE CALL simplifyFuns

-- |expandFunArgs type. Expands variables in functions embedded in types
-- |(FFun terms) that have tuple types to tuples of variables.
expandFunArgs :: Monad m => TyTerm -> IdxMonad m TyTerm
expandFunArgs term = case term of
  -- expand vars of tuple type to tuples of vars
  (Term (Tok (Ty "FFun")) [itT, expT]) -> do
    if getRefIdsInTerm term /= []
    then error $ "Types:EmbeddedFunctions:expandFunArgs: function contains Ref terms:\n" ++ (show term)
    else return ()
    funExprMb <- unembedFun IM.empty term
    case funExprMb of 
      -- if an opaque/arbitrary unknown function
      Nothing -> return term
      -- if a real function expr
      Just funExpr -> do
        -- infer types of term
        types <- assignTypes [] funExpr
        let types' = DM.fromList types
        -- expand vars to tuples of vars
        funExpr' <- expandTupVals types' DM.empty funExpr
        -- change back to embedded function  
        term' <- exprToTy [] funExpr'
        return term'
  -- recurivsley visit types
  (Term tok l) -> mapM expandFunArgs l >>= (return . (Term tok))
  -- base case
  other -> return other

{-expandFunArgs :: Monad m => TyTerm -> IdxMonad m TyTerm
expandFunArgs term = evalStateT (expandFunArgsM term) (IM.empty)

-- |expandFunArgsM term. Expands vars that should be tuples of vars into tuples of
-- |vars so that functions that be applied.
-- |TODO merge with simplifyFuns?
expandFunArgsM :: Monad m => TyTerm -> StateT (IM.IntMap TyTerm) (IdxMonad m) TyTerm
expandFunArgsM term = case term of
  -- recursive cases
  (Term (Tok (Ty "FApp")) [(Term (Tok (Ty "FFun")) [itT, expT]), argT]) -> do
    -- apply any changes already made
    itT' <- expandFunArgsM itT
    expT' <- expandFunArgsM expT
    argT' <- expandFunArgsM argT
    -- expand arg
    argT'' <- lift $ expandArgs (itT', argT')
    -- add to state, so higher lambdas will apply the changes
    let bindings = fromMaybe (error "EmbedFuns:expandFunArgs: bindVars (expandArgs ...) should always work!") $ bindVars (argT, argT'')
    modify (\m -> m `IM.union` (IM.fromList bindings))
    -- return
    return $ (Term (Tok (Ty "FApp")) [(Term (Tok (Ty "FFun")) [itT', expT']), argT'']) 
  (Term (Tok (Ty "FFun")) [itT, expT]) -> do
    -- expand children
    expT' <- expandFunArgsM expT
    -- apply any changes to idtree
    itT' <- expandFunArgsM itT
    -- return
    return (Term (Tok (Ty "FFun")) [itT', expT'])
  (Term t l) -> (mapM expandFunArgsM l) >>= (return.(Term t))
  -- bases
  (Var vid) -> do
    subs <- gets (IM.lookup vid)
    case subs of
      Just term' -> return term'
      Nothing    -> return term
  other -> return other

-- |expandArgs idTree valTree. Expands val so it's at least the same shape
-- |as idTree.
expandArgs :: Monad m => (TyTerm, TyTerm) -> IdxMonad m TyTerm
expandArgs (idT, expT) = case (idT, expT) of
  (Var _, _) -> return expT
  (Term TupTok l1, Term TupTok l2) | length l1 == length l2 -> (mapM expandArgs $ zip l1 l2) >>= (return.(Term TupTok))
  (Term TupTok l1, Var vid) -> do
    l2 <- mapM (\_ -> (newidST dtvids) >>= (return.Var)) l1
    l3 <- mapM expandArgs $ zip l1 l2
    return $ (Term TupTok l3)
  (Term TupTok _, _) -> error $ "EmbeddedFuns:expandArgs: can't expand args\n" ++ (show (idT, expT))
  other -> return expT-}

-- |bindVars (idTerm, tyTerm). Traverses var tree and arg tree, to produce 
-- | a list of bindings for var ids to terms. If the arg exp term isn't
-- |yet expanded into the number of required subexpressions, returns Nothing.
bindVars :: (TyTerm, TyTerm) -> Maybe [(Idx, TyTerm)]
bindVars (idT, argT) = case (idT, argT) of
  (Term TupTok l1, Term TupTok l2) | length l1 == length l2 -> r
    where l = catMaybes $ map bindVars $ zip l1 l2
          r = if length l == length l1 then Just $ concat l else Nothing
  (Term TupTok l1, Term TupTok l2) -> error $ "EmbeddedFunctions: in fun app pattern tree doesn't match arg tuple term:\n" ++ (show (idT, argT))
  (Var vid, t) -> Just [(vid, t)]
  other -> Nothing

-- |evalTerm varEnv term. Traverses whole term, replacing 
-- |all instances of vars bound in varEnv with the terms they
-- |are bound to. If a var isn't in the env, then the exp is 
-- |returned as is.
evalTerm :: [(Idx, TyTerm)] -> TyTerm -> TyTerm
evalTerm varEnv expTerm = case expTerm of
  (Term tok l) -> Term tok $ map (evalTerm varEnv) l  
  (Var vid) -> case lookup vid varEnv of
    Just val -> val
    Nothing  -> (Var vid)
  other -> other

andNotNull :: Monad m => (TyTerm -> m Bool) -> TyTerm -> m Bool
andNotNull pred term = case term of
  (Term (Tok (Ty "VNull")) _) -> return False
  other -> pred other

-- |filterTerm pred term. Returns another term that only contains
-- |the subterms for which the predicate holds. The function
-- |should be simplified before using this, to maximize it's 
-- |ability to return a body expression that can make
-- |a sensible subfunction. Note to implementors: When defining
-- |pred, allow all terms other than those that contain the 
-- |Vars you want to filter out.
filterTerm :: Monad m => (TyTerm -> m Bool) -> TyTerm -> m TyTerm
filterTerm pred term = case term of 
  -- tuple (filter out children
  --   for which pred doesn't hold) 
  (Term TupTok l) -> do
    l' <- mapM (filterTerm pred) l
    l'' <- filterM (andNotNull pred) l'
    case l'' of
      []  -> return $ namedTy "VNull" []
      [e] -> return e
      lst -> return $ tup lst
   -- fun app (if pred holds for all args
   --   then it does for the fun app, unless
   --   pred of the funapp fails).
  (Term (Tok (Ty "FApp")) [funT, argT]) -> do
    funOk <- pred funT
    argOk <- pred argT
    case funOk && argOk of 
      True  -> return term
      False -> return $ namedTy "VNull" []
   -- anything else
  other -> do
    ok <- pred other
    case ok of 
      True  -> return other
      False -> return $ namedTy "VNull" []

predVarsNotIn :: Monad m => Set TyTerm -> TyTerm -> m Bool
predVarsNotIn set term = return $ not $ Data.Set.member term set

-- |embedFun expr. Returns a type term that represents the 
-- |function, if possible.
embedFun :: Monad m => [(Idx, TyTerm)] -> Expr -> IdxMonad m TyTerm
embedFun varEnv (Fun eid it exp) = do
  -- remove all let expressions
  exp' <- propLets constTrueFun emptyExprEnv exp
  -- convert into a type term
  (itTerm, varEnv') <- trace ("Embedding: " ++ (show (Fun eid it exp')) ++ "\n\n") $ idxTreeToTy it
  expTerm <- exprToTy (varEnv' ++ varEnv) exp'
  return $ namedTy "FFun" [itTerm, expTerm]

idxTreeToTy :: Monad m => IdxTree -> IdxMonad m (TyTerm, [(Idx, TyTerm)])
idxTreeToTy it = case it of
  (IdxTup eid l) -> do
    l' <- mapM idxTreeToTy l
    let (terms, env) = unzip l'
    return (tup terms, concat env)
  (IdxNub _) -> do
    vid' <- newidST dtvids
    return (Var vid', [])
  (IdxLeaf eid vid n) -> do
    vid' <- newidST dtvids
    return (Var vid', [(vid, Var vid')])

-- |exprToTy varEnv expr. Tries to convert the function into a type
-- |term. Any parts that could not be converted are returned as Refs
-- |to the relevant expression ids. 
exprToTy :: Monad m => [(Idx, TyTerm)] -> Expr -> IdxMonad m TyTerm
exprToTy varEnv expr = case expr of
  -- var
  (E.Var eid vid n) | vid >= 0 -> case lookup vid varEnv of
    Just term -> return term
    Nothing   -> return $ Ref eid
  -- an external var 
  -- (created by tyToExpr for vars declared above the fun)
  (E.Var eid vid n) -> do
    if isPrefixOf "exVar" n 
    then return $ Var (-vid)
    else error $ "Types:EmbeddedFunctions:exprToTy: var with negative vid not exVar created by tyToExpr!" ++ (show expr)
  -- fun app
  (App eid fe ae) -> do
    funTerm <- exprToTy varEnv fe
    argTerm <- exprToTy varEnv ae
    return $ namedTy "FApp" [funTerm, argTerm]
  -- fun exp
  (Fun eid it exp) -> do
    term <- embedFun varEnv expr
    return term
  -- tup
  (Tup eid l) -> do
    l' <- mapM (exprToTy varEnv) l
    return $ tup l'
  -- convert literals
  (Lit _ v) -> return $ lit $ v    
  -- any other expression is just referenced
  other -> return $ Ref $ getExprId other

tyToIdxTree :: Monad m => TyTerm -> IdxMonad m (IdxTree, [(Idx, Idx)])
tyToIdxTree term = case term of
  -- makes a tuple idxtree
  (Term TupTok l) -> do
    l' <- mapM tyToIdxTree l
    let (trees, envs) = unzip l'
    eid <- newidST eids
    let exp = IdxTup eid trees
    return (exp, concat envs)
  -- makes a leaf
  (Var vid) -> do
    eid <- newidST eids
    vid' <- newidST vids
    let exp = IdxLeaf eid vid' ("v"++(show vid'))
    return (exp, [(vid, vid')])
  -- other...
  other -> error $ "EmbeddedFuns:tyToIdxTree: type term cannot be converted to IdxTree: \n" ++ (show term)

-- TODO extend to support FBoth

tyToExpr :: Monad m => [(Idx, Expr)] -> [(Idx, Idx)] -> TyTerm -> IdxMonad m (Maybe Expr)
tyToExpr expEnv varEnv term = case term of 
  -- literals
  (Term (Tok (Ty "VNull")) []) -> (newidST eids) >>= (\i -> return $ Just $ Lit i NullVal)
  (Term (Tok (Ty "VTrue")) []) -> (newidST eids) >>= (\i -> return $ Just $ Lit i (B True))
  (Term (Tok (Ty "VFalse")) []) -> (newidST eids) >>= (\i -> return $ Just $ Lit i (B False))
  (Term (Tok (Ty "VInt")) [Term (Tok (Ty v)) []]) -> (newidST eids) >>= (\i -> return $ Just $ Lit i (I (read v :: Int))) 
  -- tuple
  (Term TupTok l) -> do
    eid <- newidST eids
    l' <- mapM (tyToExpr expEnv varEnv) l
    let l'' = catMaybes l'
    if length l' == length l''
    then return $ Just $ Tup eid l''
    else return Nothing
  -- fun abstraction
  (Term (Tok (Ty "FFun")) [itT, expT]) -> do
    eid <- newidST eids
    (it, varEnv') <- tyToIdxTree itT
    exp <- tyToExpr expEnv (varEnv' ++ varEnv) expT
    if isJust exp 
    then return $ Just $ Fun eid it $ fromJust exp
    else return Nothing
  -- fun application 
  (Term (Tok (Ty "FApp")) [funT, argT]) -> do
    eid <- newidST eids
    fun <- tyToExpr expEnv varEnv funT
    arg <- tyToExpr expEnv varEnv argT
    if isJust fun && isJust arg
    then return $ Just $ App eid (fromJust fun) (fromJust arg)
    else return Nothing
  -- unknown function
  (UniVar vid) -> return Nothing
  -- get var
  (Var vid) -> case lookup vid varEnv of
    Just vid' -> do
      eid <- newidST eids
      return $ Just $ E.Var eid vid' ("v" ++ (show vid'))
    Nothing   -> do
      eid <- trace ("WARNING: EmbeddedFuns:tyToExpr: var " ++ (show vid) ++ " is not in varEnv!\n" ++ (show varEnv)) $ newidST eids
      return $ Just $ E.Var eid (-vid) ("exVar" ++ (show vid))
  -- get exp refs
  (Ref eid) -> case lookup eid expEnv of
    Just expr -> return $ Just expr
    Nothing   -> error $ "EmbeddedFuns:tyToExpr: ref refers to expression " ++ (show eid) ++ " that is not in expEnv!\n" ++ (show expEnv)
  -- other
  other -> error $ "EmbeddedFuns:tyToExpr: invalid ty term, can't convert to expr: \n" ++ (show term)

-- |unembedFun term. Returns a function expr for the type
-- |term, if this term if a function term.
unembedFun :: Monad m => IM.IntMap Expr -> TyTerm -> IdxMonad m (Maybe Expr)
unembedFun env term = do
  -- get exp id -> exp bindings
  let expEnv = IM.toList env
  -- convert from type to expr 
  case trace ("Unembedding: " ++ (show term) ++ " // " ++ (show env)) $ term of
    (UniVar vid) -> return Nothing
    (Ref eid) -> tyToExpr expEnv [] term >>= return
    (Term (Tok (Ty "FFun")) l) -> tyToExpr expEnv [] term >>= return
    (Term (Tok (Ty "FBoth")) (hd:r)) -> tyToExpr expEnv [] hd >>= return
    other -> error $ "Types:EmbeddedFunctions:unembedFun: Couldn't unembed expr from type: " ++ (show term)

dimGenNames = ["DFst", "DSnd"] 

-- |isFunTerm term. Returns true if the term is an embedded function.
isDimGen :: TyTerm -> Bool
isDimGen (Term (Tok (Ty n)) _) = elem n dimGenNames
isDimGen _ = False

dimGenToVisit = dimGenNames ++ TI.typesContainingFuns

dimGenShouldVisit :: TyTerm -> Bool
dimGenShouldVisit (Term (Tok (Ty n)) _) = elem n dimGenToVisit
dimGenShouldVisit _ = False 

-- |applyDimGensInEnv env. Applies all dim generators in the env, and 
-- |returns any constraints that they create.
applyDimGensInEnv :: Monad m => TyEnv -> IdxMonad m (TyEnv, [TyConstr], [(TyTerm, TyTerm)])
applyDimGensInEnv env = do
  (l', cl') <- runStateT (mapM (\(k, Scheme l t) -> do (t',cl,subs) <- lift $ applyDimGens t; modify (cl++) ; return (k, Scheme l t', subs)) env) []
  let (keys, schemes, subs) = unzip3 $ trace ("applyDimGensInEnv: created cons:\n" ++ (show cl') ++ "\n\n") $ l'
  return (zip keys schemes, cl', concat subs)

-- |applyDimGens term. Applies all the dim generators that can be applied
-- |in the current term, returning any new constraints created by the application.
applyDimGens :: Monad m => TyTerm -> IdxMonad m (TyTerm, [TyConstr], [(TyTerm, TyTerm)])
applyDimGens term = do
  -- simplify all functions embedded in the term
  (term', subs1) <- fullySimplifyFuns term
  -- apply recursively
  case if term /= term' then trace ("EmFuns:applyDimGens: simplified " ++ (show term) ++ " => " ++ (show term') ++ "\n") term' else term' of
    (Term t l) -> do
      res <- mapM applyDimGen l
      let (terms, constrs1, subs2) = unzip3 res
      let term' = Term t terms
      (term'', constrs2, subs3) <- applyDimGen term'
      return (term'', (concat constrs1) ++ constrs2, subs1 ++ (concat subs2) ++ subs3) 
    other -> applyDimGen other
  --((term'', subs2), cl) <- runStateT (mapTermM (\t -> if isDimGen t then applyDimGen t else return (t, [])) term') []
  -- concat results
  --return (term'', cl, subs1 ++ subs2)

-- |applyDimGen term. If term is a dim generator, or collection that contains dims
-- |then visits it, trying to simplify it, or its dim members. Returns
-- |simplifies term, any constraints produced, and any changes made as 
-- |substitutions.
applyDimGen :: Monad m => TyTerm -> IdxMonad m (TyTerm, [TyConstr], [(TyTerm, TyTerm)])
applyDimGen term = case dimGenShouldVisit term of
  True -> do
    ((term', subs), constrs) <- runStateT (applyDimGenM term) []
    let constrs' = removeRedundantConstrs constrs
    return (term', constrs', subs)
  False -> return (term, [], [])

removeRedundantConstrs :: [TyConstr] -> [TyConstr]
removeRedundantConstrs l = filter (\(a :=: b) -> a /= b) l

-- |quickUnify constrs. NOT PROPER UNIFICATION because succeeds whenever two 
-- |vars with differing vids are equated. So just checks if terms are the same 
-- |shape as each other. I.e the same tuple shape.
quickUnify :: [TyConstr] -> Bool
quickUnify (h:r) = case h of
  (a :=: b) | a == b -> quickUnify r
  (Var a :=: Var b) -> quickUnify r
  (Var a :=: Term t []) -> quickUnify r
  (Term t [] :=: Var b) -> quickUnify r
  (Term t l :=: Term t' l') | t == t' && (length l) == (length l') ->
    quickUnify $ (map (\(a,b) -> a :=: b) $ zip l l') ++ r
  other -> False
quickUnify [] = True

-- |applyDimGenM term. Applies the dim generator if possible, and adds any new
-- |new constraints to the state.
applyDimGenM :: Monad m => TyTerm -> StateT [TyConstr] (IdxMonad m) (TyTerm, [(TyTerm, TyTerm)])
applyDimGenM term@(Term (Tok (Ty n)) l) = case (n,l) of
  -- dimension generators:
  -- -----------------------
  ("DFst",[f,d]) -> case f of 
    -- get 
    -- TODO simplify before this?
    (Term (Tok (Ty "FFun")) [idT@(Term TupTok [v1, v2]), expT]) -> do
      -- create dim vars that match function's input tuple
      (dimExpT, subs) <- lift $ freshTerm expT
      -- try and apply function generator
      let funGen = namedTy "GFst" [f]
      (f', subs1) <- lift $ fullySimplifyFuns funGen
      --f' <- lift (simplifyFun funGen >>= simplifyFun) -- call twice to expand builtins and apply them
      case f' of 
        -- if function generator worked then 
        (Term (Tok (Ty "FFun")) [idT', expT']) -> do
          modify ((d :=: dimExpT):) -- make dim var constraint
          -- apply var -> dim subs to expression
          let dimExp = applyVarSubsts subs expT'
          -- check all parts of dim are dim vars 
          let dimVids = Data.Set.fromList $ map (\(_,Var vid) -> vid) $ IM.toList subs 
          case isValidDim dimVids dimExp of
            True  -> return (dimExp, (term, dimExp):subs1)
            False -> error $ "EmbeddedFuns:applyDimGenM: invalid dim tuple created!\n" ++ (show dimExp)
        -- can't apply it yet, as fun generator didn't return an expanded function
        other -> return (trace ("can't apply dim gen term as can't gen ffst: " ++ (show term)) $ term, [])
    -- can't apply it yet, as function is not expanded
    other -> return (trace ("can't apply dim gen term as fun not expanded: " ++ (show term)) $ term, []) 
  ("DSnd",[f,d]) -> case f of
    (Term (Tok (Ty "FFun")) [idT@(Term TupTok [v1, v2]), expT]) -> do
      -- create dim vars that match function's input tuple
      (dimExpT, subs) <- lift $ freshTerm expT
      -- try and apply function generator
      let funGen = namedTy "GSnd" [f]
      --f' <- lift (simplifyFun funGen >>= simplifyFun) -- call twice to expand builtins and apply them
      (f', subs1) <- lift $ fullySimplifyFuns funGen
      case f' of 
        -- if function generator worked then 
        (Term (Tok (Ty "FFun")) [idT', expT']) -> do
          modify ((d :=: dimExpT):) -- make dim var constraint
          -- apply var -> dim subs to expression
          let dimExp = applyVarSubsts subs expT'
          -- check all parts of dim are dim vars 
          let dimVids = Data.Set.fromList $ map (\(_, Var vid) -> vid) $ IM.toList subs 
          case isValidDim dimVids dimExp of
            True  -> return (dimExp, (term, dimExp):subs1)
            False -> error $ "EmbeddedFuns:applyDimGenM: invalid dim tuple created!\n" ++ (show dimExp)
        -- can't apply it yet, as fun generator didn't return an expanded function
        other -> return (trace ("can't apply dim gen term as can't gen fsnd: " ++ (show term)) $ term, [])
    -- can't apply it yet, as function is not expanded
    other -> return (trace ("can't apply dim gen term as fun not expanded: " ++ (show term)) $ term, [])
  -- expand dims to match result type of part fun:
  -- ----------------------------------------------
  -- TODO change to use inferEmbeddedFunType when implemented (which should 
  --  use proper type inference to work out the types)
  ("DArr", [mode, keyTy, valTy, layF, parF, parD, mirD]) -> case parF of
    (Term (Tok (Ty "FFun")) _) -> do
      -- get return type of parF
      let parFTy = getSimpleFunTy ("applyDimGenM:DArr: " ++ (show term)) keyTy parF
      -- make dim tuple of same shape as result type
      let (Term FunTok [_,resTy]) = parFTy
      resTup <- lift $ replaceTupLeavesWithVars resTy
      (dim, subs) <- lift $ freshTerm resTup
      -- if dim isn't already this shape, add constraint
      if quickUnify [parD :=: dim] 
      then return ()
      else modify ((parD :=: dim):)
      -- flatten layout function's body
      let layF' = flattenEmFun layF
      let term' = namedTy "DArr" [mode, keyTy, valTy, layF', parF, parD, mirD]
      -- if term has changed then return with new substitution
      if term /= term' 
      then return (term', [(term, term')])
      else return (term, [])
    _ -> return (term, [])
  ("DMap", [mode, keyTy, valTy, ordF, parF, parD, mirD]) -> case parF of -- TODO INFINATE MAY BE DUE TO RECREATION OF DIMID CONSTRS...
    (Term (Tok (Ty "FFun")) _) -> do
      -- get return type of parF
      let parFTy = getSimpleFunTy ("applyDimGenM:DMap: " ++ (show term)) (tup [keyTy, valTy]) parF
      -- make dim tuple of same shape as result type
      let (Term FunTok [_,resTy]) = parFTy
      resTup <- lift $ replaceTupLeavesWithVars resTy
      (dim, subs) <- lift $ freshTerm resTup
      -- if dim isn't already this shape, make constraint, and return term
      --if quickUnify [parD :=: dim] -- TODO REMOVED TO FIX INFINATE SOLVE LOOP AS MENTIONED ABOVE
      --then return ()
      --else modify ((parD :=: (trace ("applyDimGenM:adding pf dim constr: " ++ (show (parD :=: dim)) ) dim)):)
      return (term, [])
    _ -> return (term, [])
  -- other:
  -- --------
  other -> error $ "EmbeddedFuns:applyDimGenM: dim generator " ++ (show other) ++ " has not been implemented.\n" 

-- |replaceTupLeavesWithVars tupTerm. Replaces the leaves of a tuple tree
-- |that aren't variables, with new variables.
replaceTupLeavesWithVars :: Monad m => TyTerm -> IdxMonad m TyTerm
replaceTupLeavesWithVars term = case term of
  (Var i) -> return term
  (Term TupTok l) -> do
    l' <- mapM replaceTupLeavesWithVars l  
    return $ Term TupTok l'
  other -> do
    vid <- newidST dtvids
    return $ Var vid

-- |freshTerm term. Creates new var ids for all vars in term
-- |and replaces them.
freshTerm :: Monad m => TyTerm -> IdxMonad m (TyTerm, VarSubsts TyTerm)
freshTerm term = do
  -- make new vids
  let vids = getVarIdsInTerm term
  newVids <- mapM (\vid -> do nvid <- newidST dtvids; return (vid, Var nvid)) vids
  -- swap old vids for new ones in term
  let subs = fromDisjointList newVids
  let newTerm = applyVarSubsts subs term
  return (newTerm, subs)

isValidDim :: Set Idx -> TyTerm -> Bool
isValidDim vids term = case term of
  (Term TupTok l) -> and $ map (isValidDim vids) l
  (Var vid) -> Data.Set.member vid vids
  other -> False

-- |flattenTupTree term. Flattens any hierarchy of tuples into
-- |a flat list of terms, using a depth first traversal.
flattenTupTree :: TyTerm -> [TyTerm]
flattenTupTree (Term TupTok l) = concat $ map flattenTupTree l
flattenTupTree other = [other]

-- |flattenEmFun funTerm. If funTerm is an FFun then flattens it's
-- |body term into a flat list of terms using a depth first traversal.
-- |Otherwise just returns the term.
flattenEmFun :: TyTerm -> TyTerm
flattenEmFun term = case term of
  (Term (Tok (Ty "FFun")) [a,b]) -> fun a $ tup b'
    where b' = flattenTupTree b
  other -> other

