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
module Compiler.Back.FromFront where

import Compiler.Front.Indices (IdxMonad)

import qualified Compiler.Front.ExprTree as E
import qualified Compiler.Types2.TermLanguage as F
import qualified Compiler.Types2.TypeAssignment as F
import qualified Compiler.Types2.DepTypeAssignment as F
import qualified Compiler.Types2.EmbeddedFunctions as F
import qualified Compiler.Back.Graph as B
import qualified Compiler.Back.GraphBuilder as B

import qualified Data.IntMap.Strict as IM
import Data.Maybe (fromMaybe)
import Control.Monad.State.Strict ( lift, StateT, runStateT, get, gets, modify )


-- |translateTy type. Translates a front end type to a back end type.
translateTy :: F.TyTerm -> B.Ty
translateTy ty = case ty of
  (F.Term t l) -> case t of
    (F.FunTok) | length l == 2 -> (translateTy $ head l) B.:-> (translateTy $ head $ tail l) 
    (F.TupTok) -> B.Tup $ map translateTy l
    (F.Tok (F.Ty name)) -> B.Lf $ B.LfTy name l'
      where l' = map translateTy l
  (F.Var idx) -> error $ "Compiler.Back.FromFront:translateTy: front end type still contains type var " ++ (show idx) ++ "!\n" -- B.Lf $ B.VarTy $ show idx
  (F.Ref idx) -> error $ "Compiler.Back.FromFront:translateTy: front end type still contains ref " ++ (show idx) ++ "!\n"

-- |translateTyEnv. Translates a front end type environment to a back end
-- |one. Throws an error if input still contains a scheme with a bound variable.
translateTyEnv :: F.TyEnv -> B.NodeEnv B.Ty 
translateTyEnv env = IM.fromList tyList
  where tyList = map (\(idx, s@(F.Scheme l t)) 
                   -> if length l /= 0 
                      then error $ "Compiler.Back.FromFront: translateTyEnv: non-concrete type: " ++ (show s) 
                      else (idx, translateTy t)) env
