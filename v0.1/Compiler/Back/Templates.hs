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
module Compiler.Back.Templates where

import Compiler.Back.Graph
import Compiler.Back.GenDecls
import Compiler.Back.Gen
import Compiler.Back.Generators (genTypeName)
import Compiler.Back.Helper
import Compiler.Back.GraphInterpretter
import Compiler.Back.Arrays
import Compiler.Back.CartTopology
import Compiler.Back.StrTemplates (StrTem, applyT)

import Control.Monad (foldM)
import Control.Monad.State.Strict (gets, modify)
import Data.Maybe (fromMaybe)
import qualified Data.Set as DS
import qualified Data.IntMap as IM
import qualified Data.Map as DM
import Data.List ((\\), intersperse, zip4, unzip4)
import Data.Char (isAlphaNum)

-- |nt. shorthand for Nothing.
nt = Nothing

n0 = emptyNodeTreeEx

terr :: String -> Ty -> NodeTreeEx -> a
terr tn ty nodes = error $ "Template " ++ tn ++ " error\nType: " ++ (show ty) ++ "\nNodes: " ++ (show nodes) ++ "\n"

terr' :: Monad m => Ty -> NodeTreeEx -> GenM m
terr' ty nodes = do
  tn <- getTemplateName
  terr tn ty nodes

nullFun = Lf $ LfTy "NullFun" [];

nameTy :: String -> Ty
nameTy name = Lf $ LfTy name []

namedTy :: String -> [Ty] -> Ty
namedTy name l = Lf $ LfTy name l

temMsg :: Monad m => String -> GenM1 m Code
temMsg str = do
  -- get current function/template name
  tname <- getTemplateName
  -- display a comment, and a debug statement
  return $ "// " ++ str ++ " " ++ tname ++ "\n" ++
           "#ifdef DEBUG\n" ++
           "std::cerr << thisRank << \") " ++ str ++ " " ++ tname ++ "\\n\";\n"++ 
           "#endif\n"

dbgVal :: Monad m => String -> Code -> GenM1 m Code
dbgVal name val = do
  -- get current function/template name
  tname <- getTemplateName
  -- make template val
  return $ "// DBG " ++ tname ++ "." ++ name ++ "\n" ++
           "#ifdef DEBUG\n" ++
           "std::cerr << thisRank << \") DBG " ++ tname ++ "." ++ name ++ " = \" << " ++ val ++ " << \"\\n\";\n"++ 
           "#endif\n"

outMain :: Monad m => Code -> GenM m
outMain code = do
  bstr <- temMsg "BEGIN"
  estr <- temMsg "END"
  output "main" bstr
  output "main" code
  output "main" estr

-- |genVarExps srcId tem ty params. Generates a new var exp of type ty for each param,
-- |using the template tem, replacing <p> with each param, and replacing 
-- |<v> with the srcId. 
genVarExps :: Monad m => Id -> StrTem -> Ty -> [Code] -> GenM1 m ([IdTree], [IdTree])
genVarExps srcId tem ty params = do
  -- make vars
  varNames <- mapM (\param -> 
    do vid <- newInt ; 
       varExp ("varExp" ++ (show vid)) srcId (applyT tem [("p", param)]) ty ; 
       return $ Lf ("varExp" ++ (show vid))) params
  -- get var ids
  vids <- mapM (\(Lf n) -> do (VarV _ v) <- getLocalVal n; return v) varNames
  -- return
  return (varNames, vids)

-- |printInt template
t30 :: Monad m => Template m
t30 (t1 :-> t2)
   (LFun _ inN outN)
   | t1 == intTy && t2 == nullTy = do
     -- get input vars
     getVar (Lf "val") inN outVarName
     -- when gen is called, generate print
     setFun outN "gen" nt (\_ -> do
       outMain "std::cout << <val>;\n"
       return ())
t30 t n = terr' t n


