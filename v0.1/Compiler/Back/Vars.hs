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
module Compiler.Back.Vars where

import Data.Map.Strict as Data.Map (Map)
import Data.Set (Set, empty, insert)
import Control.Monad.State.Strict (StateT, modify, execStateT)
import Data.Functor.Identity (runIdentity)

data Scheme a = Scheme (Set String) a
  deriving (Show, Eq, Ord)

class ContainsVars ct where
  visitVars :: Monad m => (String -> m ct) -> ct -> m ct
  createVar :: String -> ct

-- |getVars container. Returns the set of vars in the var container.
getVars :: ContainsVars ct => ct -> Set String
getVars c = runIdentity $ execStateT (visitVars (\n -> do modify (\s -> insert n s); return $ createVar n) c) Data.Set.empty 

--substituteVars :: ContainsVars ct => Map String String -> ct -> ct
--substituteVars substs c = runIdentity $ execStateT () 
