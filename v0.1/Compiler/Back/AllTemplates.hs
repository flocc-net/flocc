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
module Compiler.Back.AllTemplates (templates) where

import Control.Monad.Catch

import Compiler.Back.Graph
import Compiler.Back.GenDecls
import Compiler.Back.Gen

import Compiler.Back.ScalTemplates (scalTemplates)
import Compiler.Back.ControlTemplates (ctrlTemplates)
import Compiler.Back.Maps.STemplates (smapTemplates)
import Compiler.Back.Maps.VTemplates (vmapTemplates)
import Compiler.Back.Maps.HTemplates (hmapTemplates)
import Compiler.Back.Maps.TTemplates (tmapTemplates)

templates :: (Monad m, MonadCatch m) => [(Id, Template m)]
templates = 
     scalTemplates
  ++ ctrlTemplates
  ++ smapTemplates
  ++ vmapTemplates
  ++ hmapTemplates
  ++ tmapTemplates
