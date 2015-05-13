{
module Compiler.Front.SrcParser ( parse, parseAndLabel ) where

import Compiler.Front.Indices ( Idx, IdxSet )
import Compiler.Front.ExprTree ( Expr(..), IdxTree(..), Val(..), initExprVarIds, renewExprIds )
import Compiler.Front.SrcLexer ( Token(..) )

import Control.Monad.State.Strict ( StateT )

}

%name parseInternal
%tokentype { Token }
%error { parseError }

%token
    let    { TokLet }
    in     { TokIn  }
    if     { TokIf  }
    then   { TokThen } 
    else   { TokElse }
    '\\'   { TokBSlash }
    '->'   { TokArrow }
    '='    { TokEq }
    ','    { TokComma }
    '_'    { TokUnderscore }
    '('    { TokLParen }
    ')'    { TokRParen }
    '['    { TokLSqParen }
    ']'    { TokRSqParen }
    var    { TokVar $$ }
    bool   { TokBool $$ }
    int    { TokInt $$ }
    float  { TokFloat $$ }
    string { TokString $$ }
    null   { TokNull }

%%

Exp    : let IdPat '=' Exp in Exp { Let defId $2 $4 $6 }
       | '(' ExpList ')'          { Tup defId $2 }
       | '\\' IdPat '->' Exp       { Fun defId $2 $4 }
       | if Exp then Exp else Exp { If defId $2 $4 $6 }
       | '[' ExpList ']'          { Rel defId $2 }
       | Exp Exp                  { App defId $1 $2 }
       | LitVal                   { Lit defId $1 }
       | var                      { Var defId defId $1 }

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
       | '(' IdList ')'           { IdxTup defId $2 }

{- for now don't allow empty patterns like () -}
IdList : IdPat                    { [$1] }
       | IdList ',' IdPat         { $3 : $1 }

{

defId :: Idx
defId = -1

-- |Parse error function
parseError :: [Token] -> a
parseError tl = error $ "Parse error\n" ++ (show tl)

-- |Reverses idx tuple patterns to put them in the correct order as they were
-- |built using left recursion.
cleanUpIdxTrees :: IdxTree -> IdxTree
cleanUpIdxTrees it = case it of
  (IdxTup i l) -> IdxTup i (map cleanUpIdxTrees (reverse l))
  i -> i

-- |Converts tuples with no children to null vals, and expands out tuples
-- |with one child to be the child itself. Also reverses all lists of expressions
-- |to put them in the correct order as they were built using left recursion.
cleanUpTuples :: Expr -> Expr
cleanUpTuples exp = case exp of
  (Tup i [])         -> Lit i (NullVal)
  (Tup i (child:[])) -> cleanUpTuples child
  (Tup i l)          -> Tup i (map cleanUpTuples (reverse l))
  (Rel i l)          -> Rel i (map cleanUpTuples (reverse l))
  (Fun i it e)       -> Fun i (cleanUpIdxTrees it) (cleanUpTuples e)
  (App i fe ae)      -> App i (cleanUpTuples fe) (cleanUpTuples ae)
  (If i pe te ee)    -> If i (cleanUpTuples pe) (cleanUpTuples te) (cleanUpTuples ee)
  (Let i it be ie)   -> Let i (cleanUpIdxTrees it) (cleanUpTuples be) (cleanUpTuples ie)
  _                  -> exp
  

-- |Parse method to export as does some basic post processing
-- |using cleanUpTuples
parse :: [Token] -> Expr
parse tl = cleanUpTuples $ parseInternal tl

-- |Parse method that also creates unique ids for all expressions
-- |and for all variables
parseAndLabel :: Monad m => [(String, Idx)] -> [Token] -> StateT IdxSet m Expr
parseAndLabel env tl = do
  let expr = parse tl
  expr' <- renewExprIds expr
  expr'' <- initExprVarIds env expr'
  return expr''

}

