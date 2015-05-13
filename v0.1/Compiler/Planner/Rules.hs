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
module Compiler.Planner.Rules where

import qualified Data.Map.Strict as DM
import Control.Monad.State.Strict (StateT, runStateT, execStateT, evalStateT, lift, get, gets, modify)
import Data.Functor.Identity (runIdentity)
import Debug.Trace (trace)
import Data.Maybe (fromMaybe)

import Compiler.Front.Common
import Compiler.Front.Indices (IdxMonad, Idx, newidST)
import Compiler.Front.ExprTree

import qualified Compiler.Planner.RuleParser as P
import Compiler.Planner.Solutions

type ExpId = Idx

type RuleId = String

data Ruleset = Ruleset {
    ruleRanges :: DM.Map RuleId [Int],
    ruleDefs :: DM.Map RuleId (IdxTree, [Expr])
  } deriving (Show)

-- |loadRules varIds fileName. Loads ruleset from a file.
loadRules :: [(String, Idx)] -> String -> IO Ruleset
loadRules varIds fileName = do
  -- read and parse file
  str <- readFileForce fileName
  rs <- evalIdxStateT 0 (P.parseAndLabelRuleSet varIds str)
  -- pattern match
  case rs of
    -- import rules 
    (name, [(idx, rules)]) -> do
      let defs = DM.fromList $ map (\(n,it,exps) -> (n,(it,exps))) rules
      let ranges = DM.map (\(it,exps) -> [1..(length exps)]) defs
      return $ Ruleset { ruleDefs=defs, ruleRanges=ranges }
    -- invalid rs
    other -> error $ "Rules: loadRules: rule sets must have exactly one level: " ++ (show rs) 

-- |ruleit ruleExp exp. Instantiates rule applying it to argExp, by binding args in
-- |a let, and then doing the rule exp (fun app).
appRule :: Monad m => IdxTree -> Expr -> Expr -> IdxMonad m Expr
appRule ruleIt ruleExp argExp = do
  -- freshen var ids and names for ruleIt and ruleExp
  (it, inExp) <- renewIdAndExprIds ruleIt ruleExp
  -- create let-exp
  eid1 <- newidST eids
  let letExp = (Let eid1 it argExp inExp)
  return letExp

appRulesM :: Monad m => () -> Expr -> StateT (Ruleset, SolId) (IdxMonad m) Expr
appRulesM _ expr = do  
  -- apply recursively to children first
  expr' <- if isLeafExpr expr 
           then return expr -- base case
           else visitExprTree appRulesM (\_ -> \it -> return (it, ())) () expr -- rec case
  -- get rules from state
  (rules, sid) <- get 
  -- if it's a fun app of a fun in the rules, apply rule
  case expr' of 
    -- is a possible combinator fun app
    (App eid (Var _ vid nam) arg) -> case DM.lookup nam (ruleDefs rules) of
      -- there is a rule for this function
      Just rule@(it,rhsl) -> case sid of
        -- there is an id for this fun app
        (sidHd:sidRest) -> do
          -- get rhs to use
          let rhs = (if sidHd >= 1 && sidHd <= (length rhsl) 
                     then rhsl !! (sidHd-1) 
                     else error $ "Rules:appRulesM: part of solution id out of bounds!\n" ++ 
                          (show expr) ++ "\n" ++ (show expr') ++ "\n" ++ (show sid) ++ "\n" ++ (show rule))
          -- remove this rhs from the solution list
          modify (\st -> (rules, sidRest))
          -- init new let, and fun app expression
          expr'' <- lift $ appRule it rhs arg
          -- return new function expr
          return expr''
        -- no id for this fun app
        [] -> error $ "Rules:appRules: sol id too short! no id for " ++ (show expr')
      -- no rule for this function
      Nothing -> return expr'
    -- otherwise
    other -> return expr'

-- |applyRules rules solId ast. Applies the rules identified by the 
-- |solution id, to ast.
applyRules :: Monad m => Ruleset -> SolId -> Expr -> IdxMonad m Expr
applyRules rules sid ast = evalStateT (
  {-visitExprTree appRulesM (\_ -> \it -> return (it, ())) () ast >>=-} appRulesM () ast) (rules, sid)

accumRuleApps :: Monad m => Ruleset -> Expr -> StateT [(ExpId, RuleId, [Int])] m Expr
accumRuleApps rules expr = do
  -- apply recursively to children first
  expr' <- if isLeafExpr expr 
           then return expr -- base case
           else visitExprTree accumRuleApps (\rules -> \it -> return (it, rules)) rules expr -- rec case
  -- if it's a fun app of a fun in the rules, add to state
  case {-trace ("accumRuleApps " ++ (show expr') ++ "\n") $-} expr' of 
    -- is a possible combinator fun app
    (App eid (Var _ vid nam) arg) -> case DM.lookup nam (ruleRanges rules) of
      -- there is a rule for this function
      Just ran -> do
        modify ((eid,nam,ran):) -- add to state
        return expr'
      -- no rule for this function
      Nothing -> return expr'
    -- otherwise
    other -> return expr'

-- |getRuleApps rules ast. Returns a list of all the fun apps in ast
-- |for which rules exist.
getRuleApps :: Ruleset -> Expr -> [(ExpId, RuleId, [Int])]
getRuleApps rules ast = reverse $ runIdentity $ execStateT (
  {-(visitExprTree accumRuleApps (\rules -> \it -> return (it, rules)) rules ast) >>=-} accumRuleApps rules ast) []

-- |Returns strings for the rules in sid
getRuleNames :: Ruleset -> Expr -> [(ExpId, RuleId, [Int])] -> [Int] -> [String]
getRuleNames rules ast apps sid = strs
  where defs = ruleDefs rules
        strs = map (\((eid,rid,_),idx) -> showP $ listGet "getRuleNames" (snd $ fromMaybe (error $ "Rules:can't get rule def for " ++ (show rid)) $ DM.lookup rid defs) (idx-1)) $ zip apps sid

-- |Returns rule names for all combinations of rule applications
getAllRuleNames :: Ruleset -> Expr -> [(ExpId, RuleId, [Int])] -> [Int] -> [([Int], [String])]
getAllRuleNames rules ast ranges sid | length sid == length ranges = [(sid, (getRuleNames rules ast ranges sid))]
getAllRuleNames rules ast ranges sid = concat l
  where (eid,rid,range) = listGet "getAllRuleNames:range" ranges (length sid)
        l = map (\idx -> getAllRuleNames rules ast ranges $ sid ++ [idx]) range


