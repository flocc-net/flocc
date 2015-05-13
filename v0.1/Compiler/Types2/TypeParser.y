{
module Compiler.Types2.TypeParser ( parseTypes, TypeDec, typeDecToScheme,
  numberTypes, typeNameMap, typeEnv, typeDecsToSchemeExEnv,
  generateNamedSchemeEnv, generateNamedSchemeExEnv ) where

import Compiler.Types2.TypeLexer
import Compiler.Types2.TermLanguage 
import Compiler.Types2.TermBuilder
import Compiler.Types2.TypeAssignment

import Compiler.Front.Common (dtvids, runIdxStateT)
import Compiler.Front.Indices ( Idx, IdxSet, newid'' )
import Compiler.Front.ExprTree ( IdxTree(..), newExprVarId )

import Data.Functor.Identity ( Identity, runIdentity )
import Control.Monad.State.Strict ( StateT, lift, evalStateT, get, modify )
import qualified Data.Map.Strict as Data.Map

}

%name parseInternal
%tokentype { PosnToken }
%error { parseError }
%monad { MonadType }

%token
    '\n'   { PosnTok _ _ _ TokEOL }
    '->'   { PosnTok _ _ _ TokArrow }
    ','    { PosnTok _ _ _ TokComma }
    '_'    { PosnTok _ _ _ TokUnderscore }
    '('    { PosnTok _ _ _ TokLParen }
    ')'    { PosnTok _ _ _ TokRParen }
    name   { PosnTok _ _ _ (TokName $$) }
    var    { PosnTok _ _ _ (TokVar $$) }
    '::'   { PosnTok _ _ _ TokColon }
    'forall' { PosnTok _ _ _ TokForall }
    '=>'   { PosnTok _ _ _ TokImplies }

%%

Root : OptionalEOL TyDecs OptionalEOL  { reverse $2 }

TyDecs : {- empty -}                   { [] }
       | TyDec                         { [$1] }
       | TyDecs Newlines TyDec         { $3 : $1 }

OptionalEOL : {- empty -}              { [] }
            | Newlines                 { [] }

Newlines : '\n'                        { [] }
         | Newlines '\n'               { [] }

TyDec : StartTyDec OptionalIdPat '::' OptionalForall TyExp {%
          do ret <- get 
             let ret' = varEnvDiff ret (getIdxPatVarEnv $2)
             case ($4, ret') of
             -- if there is no forall but there are vars referenced
             -- that are not in the idx pattern, return all those 
               ([], a:b) -> return ($1,$2,ret',$5)
             -- else return the forall
               _         -> return ($1,$2,$4,$5) }

StartTyDec : var {% do resetVarEnv ; return $1 }

OptionalIdPat : {- empty -}            { IdxNub defId }
              | IdPat                  {  $1 }     

OptionalForall : {-  empty -}          { [] }
               | 'forall' IdList '=>'  { reverse $2 }

TyExp : Var                 { Var (snd $1) }
      | name TyParams       { ty $1 (reverse $2) }
      | TyExp '->' TyExp    { fun $1 $3  } 
      | '(' TyExpList ')'   { if length $2 == 1 then head $2 else (if length $2 == 0 then nullTy else tup $ reverse $2)  }

TyParams : {- empty -}             { [] }
         | TyParams TyParam        { $2 : $1 }

TyParam : name                     { if $1 == "UniVar" then (UniVar 0) else ty $1 [] }
        | Var                      { Var (snd $1) }
        | '(' TyExpList ')'        { if length $2 == 1 then head $2 else (if length $2 == 0 then nullTy else tup $ reverse $2) }

TyExpList : {- empty -}            { [] }
        | TyExpList ',' TyExp      { $3 : $1 }
        | TyExp                    { [$1] }

IdList : Var                       { [(fst $1, snd $1)] }
       | IdList ',' Var            { (fst $3, snd $3) : $1 }

IdPat  : '_'                       { IdxNub defId }
       | Var                       { IdxLeaf defId (snd $1) (fst $1) }
       | '(' IdPatList ')'         { IdxTup defId $ reverse $2 }

{- for now don't allow empty patterns like () -}
IdPatList : IdPat                  { [$1] }
          | IdPatList ',' IdPat    { $3 : $1 }

Var : var                          {% do id <- getVarId $1; 
                                         return ($1, id) }

{

defId :: Idx
defId = -1

-- |Shorthand to create new type terms
ty :: String -> [TyTerm] -> TyTerm
ty s l = Term (Tok (Ty s)) l

-- |Parse error function
parseError :: [PosnToken] -> a
parseError ((PosnTok _ lineNum colNum _):tl) = error $ "Type file parse error on line " ++ (show lineNum)
  ++ ":" ++ (show colNum) ++ " near '"++ (concat $ map show $ take 10 $ takeWhile (\(PosnTok _ _ _ t) -> t /= TokEOL) tl) ++ "'"

-- |idxTreeToIdTree takes an IdxTree and returns an IdTree 
-- | of all it's var ids.
idxTreeToIdTree :: IdxTree -> IdTree
idxTreeToIdTree it = case it of
  (IdxTup _ l)      -> IdTup $ map idxTreeToIdTree l
  (IdxLeaf _ vid _) -> IdLeaf vid
  (IdxNub _)        -> IdBlank

-- |Monad type of parser
type MonadType = StateT [(String, Idx)] (StateT IdxSet Identity)

-- |The return type of the parse
type TypeDec = (String, IdxTree, [(String, Idx)], TyTerm)

-- |Returns the type scheme of a type declaration
typeDecToScheme :: TypeDec -> TyScheme
typeDecToScheme (_,_,boundVars,ty) = 
  scm (map (\i -> Var i) $ snd $ unzip boundVars) ty

-- |typeDecToSchemeEx takes a type declaration and returns an 
-- |Scheme extended to include an IdTree of qualified variables.
typeDecToSchemeEx :: TypeDec -> TySchemeEx
typeDecToSchemeEx dec = SchemeEx (idxTreeToIdTree idxTree) scheme
  where (_,idxTree,_,_) = dec
        scheme = typeDecToScheme dec

-- |If the string exists in the state, then returns current binding or otherwise
-- |creates a new binding.
getVarId :: String -> MonadType Idx
getVarId s = do
  env <- get
  case lookup s env of
    Just idx -> return idx
    Nothing  -> do
      idx <- lift $ newid'' dtvids --vids --dtids
      modify (\env -> (s,idx):env)
      return idx

-- |Wipes all current bindings ready for the next type declaration
resetVarEnv :: MonadType ()
resetVarEnv = do
  modify (\env -> [])
  return ()

-- |Gets the var env defined by an idx pattern
getIdxPatVarEnv :: IdxTree -> [(String,Idx)]
getIdxPatVarEnv ip = case ip of
  IdxNub _ -> []
  IdxLeaf _ vid name -> [(name, vid)]
  IdxTup _ l -> concat $ map getIdxPatVarEnv l

-- |Performs set difference on var environments
varEnvDiff :: [(String, Idx)] -> [(String, Idx)] -> [(String,Idx)]
varEnvDiff a b = Data.Map.toList $ 
  (Data.Map.fromList a) Data.Map.\\ (Data.Map.fromList b)

-- |Parse method to export as does some basic post processing
-- |using cleanUpTuples
--parseTypes :: [PosnToken] -> StateT IdxSet Identity [TypeDec]
--parseTypes tl = evalStateT (parseInternal tl) []
parseTypes' :: String -> StateT IdxSet Identity [TypeDec]
parseTypes' s = evalStateT (parseInternal $ scanTypes s) []
--runIdentity $ evalIdxStateT 

parseTypes :: Monad m => String -> StateT IdxSet m [TypeDec]
parseTypes s = do
  let (types, idxset) = runIdentity $ runIdxStateT 0 (parseTypes' s)
  --error $ show idxset
  modify (\_ -> idxset)
  return types

-- |Number all types in a type dec list
numberTypes :: Monad m => [TypeDec] -> StateT IdxSet m [(Idx, TypeDec)]
numberTypes tl = do
  tl' <- mapM (\t -> do vid <- newExprVarId; return (vid,t)) tl
  return tl'

-- |Return a map of names to type env indices
typeNameMap :: [(Idx, TypeDec)] -> [(String, Idx)]
typeNameMap tl = map (\(i,(n,_,_,_)) -> (n,i)) tl

-- |Return a map of type indices to type schemes
typeEnv :: [(Idx, TypeDec)] -> [(Idx, TyScheme)]
typeEnv tl = map (\(i,tydec) -> (i, typeDecToScheme tydec)) tl

-- |Returns a named list of type schemes.
generateNamedSchemeEnv :: [TypeDec] -> [(String, TyScheme)]
generateNamedSchemeEnv tl = map (\tyDec@(name,_,_,_) -> (name, typeDecToScheme tyDec)) tl

-- |typeDecsToSchemeEnv takes an associative list of type declarations
-- |and returns an associative lift of SchemeEx values.
typeDecsToSchemeExEnv :: [(Idx, TypeDec)] -> [(Idx, TySchemeEx)]
typeDecsToSchemeExEnv tl = map (\(i,tydec) -> (i, typeDecToSchemeEx tydec)) tl

-- |Returns a named list of type scheme ex's.
generateNamedSchemeExEnv :: [TypeDec] -> [(String, TySchemeEx)]
generateNamedSchemeExEnv tl = map (\tyDec@(name,_,_,_) -> (name, typeDecToSchemeEx tyDec)) tl

}

