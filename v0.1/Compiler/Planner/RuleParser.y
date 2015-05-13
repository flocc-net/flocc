{
module Compiler.Planner.RuleParser ( parseRuleSet, parseAndLabelRuleSet, 
  Rule, Level, RuleSet ) where

import Compiler.Front.Indices ( Idx, IdxSet )
import Compiler.Front.ExprTree ( Expr(..), IdxTree(..), Val(..), initExprVarIds, initIdxTreeExpIds, initIdxTreeVarIds, renewExprIds )
import Compiler.Planner.RuleLexer ( Token(..), PosnToken(..), scanRuleSet )

import Control.Monad.State.Strict ( StateT, mapM )

}

%name parseInternal
%tokentype { PosnToken }
%error { parseError }

%token
    level  { PosnTok _ _ _ TokLevel }
    ruleset { PosnTok _ _ _ TokRuleset }
    let    { PosnTok _ _ _ TokLet }
    in     { PosnTok _ _ _ TokIn  }
    if     { PosnTok _ _ _ TokIf  }
    then   { PosnTok _ _ _ TokThen } 
    else   { PosnTok _ _ _ TokElse }
    '\\'   { PosnTok _ _ _ TokBSlash }
    '=>'   { PosnTok _ _ _ TokImplies }
    '->'   { PosnTok _ _ _ TokArrow }
    '='    { PosnTok _ _ _ TokEq }
    ','    { PosnTok _ _ _ TokComma }
    '_'    { PosnTok _ _ _ TokUnderscore }
    '('    { PosnTok _ _ _ TokLParen }
    ')'    { PosnTok _ _ _ TokRParen }
    '['    { PosnTok _ _ _ TokLSqParen }
    ']'    { PosnTok _ _ _ TokRSqParen }
    '|'    { PosnTok _ _ _ TokBar }
    ':'    { PosnTok _ _ _ TokColon }
    ';'    { PosnTok _ _ _ TokSemiColon }
    var    { PosnTok _ _ _ (TokVar $$) }
    bool   { PosnTok _ _ _ (TokBool $$) }
    int    { PosnTok _ _ _ (TokInt $$) }
    float  { PosnTok _ _ _ (TokFloat $$) }
    string { PosnTok _ _ _ (TokString $$) }
    null   { PosnTok _ _ _ TokNull }

%%

RuleSet   : ruleset var LevelList      { ($2, reverse $3) }

LevelList : {- empty -}                { [] }
          | LevelList LevelDec         { $2 : $1 }

LevelDec  : level int ':' RuleList     { ($2, reverse $4) }

RuleList  : {- empty -}                { [] }
          | RuleList Rule              { $2 : $1 } 

Rule      : var IdPat '=>' SubList ';' { ($1, $2, reverse $4) }

SubList   : Exp                        { [$1] }
          | SubList '|' Exp            { $3 : $1 }

Exp    : let IdPat '=' Exp in Exp { Let defId $2 $4 $6 }
       | '(' ExpList ')'          { cleanUpTuple (reverse $2) }
       | '\\' IdPat '->' Exp      { Fun defId $2 $4 }
       | if Exp then Exp else Exp { If defId $2 $4 $6 }
       | '[' ExpList ']'          { Rel defId (reverse $2) }
       | Exp Exp                  { App defId $1 $2 }
       | LitVal                   { Lit defId $1 }
       | var                      { Var defId defId $1 }
       | ruleset                  { Var defId defId "ruleset" } 
       | level                    { Var defId defId "level" }

LitVal : bool                     { B $1 }
       | int                      { I $1 }
       | float                    { F $1 }
       | string                   { S $1 }
       | null                     { NullVal }

{- remember! lists are being formed backwards!!! -}
ExpList : {- empty -}             { [] }
        | ExpList ',' Exp         { $3 : $1 }
        | Exp                     { [$1] }

IdPat  : '_'                      { IdxNub defId }
       | var                      { IdxLeaf defId defId $1 }
       | ruleset                  { IdxLeaf defId defId "ruleset" } 
       | level                    { IdxLeaf defId defId "level" }
       | '(' IdList ')'           { IdxTup defId (reverse $2) }

{- for now don't allow empty patterns like () -}
IdList : IdPat                    { [$1] }
       | IdList ',' IdPat         { $3 : $1 }

{

defId :: Idx
defId = -1

-- |Parse error function
parseError :: [PosnToken] -> a
parseError ((PosnTok _ lineNum colNum _):tl) = error $ "Rule file parse error on line " ++ (show lineNum)
  ++ ":" ++ (show colNum) ++ " near '"++ (concat $ map show $ take 10 tl) ++ "'"

-- |Converts tuples with no children to null vals, and expands out tuples
-- |with one child to be the child itself.
cleanUpTuple :: [Expr] -> Expr
cleanUpTuple exp = case exp of
  []           -> Lit defId (NullVal)
  (child:[])   -> child
  l            -> Tup defId l

-- |Labels the expression with expression ids and var ids
labelExpr :: Monad m => [(String, Idx)] -> Expr -> StateT IdxSet m Expr
labelExpr env expr = do
  expr' <- renewExprIds expr
  expr'' <- initExprVarIds env expr'
  return expr''

-- |A set of possible expansions for a function application
type Rule = (String, IdxTree, [Expr])

labelRule :: Monad m => 
  [(String, Idx)] -> 
  Rule -> StateT IdxSet m Rule
labelRule env (name,idpat,exprs) = do
  idpat' <- initIdxTreeExpIds idpat
  (idpat'', env') <- initIdxTreeVarIds idpat'
  exprs' <- mapM (labelExpr (env' ++ env)) exprs
  return (name,idpat'',exprs')

-- |A set of expansion rules for a particular nesting level
type Level = (Int, [Rule])

labelLevel ::  Monad m => 
  [(String, Idx)] -> 
  Level -> StateT IdxSet m Level
labelLevel env (levelNum, rules) = do
  rules' <- mapM (labelRule env) rules
  return (levelNum, rules')

-- |A set of rules for each nesting level of the architecture
type RuleSet = (String, [Level])

-- |Parse method to export. Takes a list of tokens and returns a rule set.
parseRuleSet :: [PosnToken] -> RuleSet
parseRuleSet = parseInternal

-- |Parse method that also creates unique ids for all expressions
-- |and for all variables
{-parseAndLabelRuleSet :: Monad m => [(String, Idx)] -> [PosnToken] -> StateT IdxSet m RuleSet
parseAndLabelRuleSet env tl = do
  let (ruleSetName, levelList) = parseRuleSet tl
  levelList' <- mapM (labelLevel env) levelList
  return (ruleSetName, levelList')
-}
parseAndLabelRuleSet :: Monad m => [(String, Idx)] -> String -> StateT IdxSet m RuleSet
parseAndLabelRuleSet env s = do 
  let tl = scanRuleSet s
  let (ruleSetName, levelList) = parseRuleSet tl
  levelList' <- mapM (labelLevel env) levelList
  return (ruleSetName, levelList')

}

