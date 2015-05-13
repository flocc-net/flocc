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
module Compiler.Back.StrTemplates where

import Data.Map.Strict (Map)
import Data.Text (Text, replace, pack, unpack)
import qualified Data.Text as Txt
import Data.List (isInfixOf)
import Debug.Trace (trace)

type StrTem = String

nl = "\n"

-- |containsNl str. Returns True if 
-- |nl is in str.
containsNewline :: String -> Bool
containsNewline = isInfixOf nl

containsTemParam :: String -> String -> Bool
containsTemParam paramName = isInfixOf $ "<" ++ paramName ++ ">"

-- |indentString indent str. Returns str where
-- |indent has been added after every newline.
indentString :: String -> String -> String
indentString indent str = indent ++ str'
  where str' = unpack $ replace (pack nl) (pack $ nl ++ indent) (pack str)

-- |Creates a new string template
createT :: String -> StrTem 
createT str = str

-- |Expands a template with a single value mapping
applySingleT :: Text -> (String, String) -> Text
applySingleT str (name, val) = if containsTemParam name (unpack str) then
  replace (pack ("<" ++ {-(trace ("applySingleT:" ++ name) $ name)-} name ++ ">")) 
          (pack $ if containsNewline val then indentString "  " val else val) str
  else str
  

-- |Expands a template with an environment of values
applyT :: StrTem -> [(String, String)] -> String
applyT tem env = unpack $ foldl applySingleT (pack tem) env
