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
module Compiler.Front.Front where

import Compiler.Front.Common
import Compiler.Front.Indices
import Compiler.Front.ExprTree
import Compiler.Front.SrcLexer
import Compiler.Front.SrcParser

import Control.Monad.State (lift)

-- |parseSrc path. Returns the AST for the source code.
parseSrc :: Monad m => [(String, Idx)] -> String -> IdxMonad m Expr
parseSrc libVarIds src = do
  -- lex and parse it
  ast <- parseAndLabel libVarIds $ scan src
  return ast

-- |parseSrcFile path. Reads the contents of the file
-- |at path, and returns it's AST.
parseSrcFile :: [(String, Idx)] -> FilePath -> IdxMonad IO Expr
parseSrcFile libVarIds path = do
  -- read in file
  src <- lift $ readFileForce path
  -- lex and parse it
  ast <- parseAndLabel libVarIds $ scan src
  return ast

testParseSrcFile :: FilePath -> IO Expr
testParseSrcFile path = do
  -- read in file
  src <- readFileForce path
  return $ parse $ scan src
