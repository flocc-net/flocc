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
module Compiler.Planner.SolExec where

--import Prelude hiding (catch)
import Control.Exception (catch, SomeException)
import System.Directory
import qualified Control.Monad.Catch as CM
--import System.IO.Error hiding (catch)
import Data.Maybe (fromMaybe, isJust, fromJust, isNothing)
import Data.Time.Clock
import Data.Time.Format
import System.Exit (ExitCode(..))
import System.Process
import Control.Concurrent (threadDelay)
import System.IO (hGetContents, hReady, hGetChar, hPutStr, stderr, stdin)
import Data.Functor.Identity (runIdentity)
--import System.Timeout
import System.Locale

import Data.List (intercalate)
import qualified Data.Map.Strict as DM
import qualified Data.IntMap.Strict as IM
import Control.Monad.State.Strict (StateT, runStateT, execStateT, evalStateT, lift, get, gets, modify)

import Compiler.Front.Common
import Compiler.Front.Indices (Idx, IdxMonad, setMinIndices)
import Compiler.Front.Front
import Compiler.Front.ExprTree
--import Compiler.Front.SrcParser
import Compiler.Front.Preprocess

import Compiler.Types2.TermLanguage (Scheme(..), getFreeVarIdsInEnv, stripTermLabelsRec, Constr(..))
import Compiler.Types2.TypeAssignment (TySchemeEx, TyScheme, TyEnv, showExprWithTypes)
import Compiler.Types2.DepTypeAssignment (assignDepTypes2, assignDepTypes, applyVarSubstsToVarMap)
import Compiler.Types2.EmbeddedFunctions (simplifyFunsInEnv, evalEmFunM, showEmbeddedFuns)
import Compiler.Types2.FillGaps (remRedundantDims, fillGapsInEnv)
import Compiler.Types2.Types

import Compiler.Planner.InsertCasts
import Compiler.Planner.Solutions
import Compiler.Planner.Rules

import Compiler.Back.FromFront2 (translateTypes)
import Compiler.Back.GraphBuilder (graphFromExpr)
import Compiler.Back.Back 

import Control.Concurrent (forkIO, threadDelay, killThread)
import Control.Concurrent.MVar (newEmptyMVar, putMVar, takeMVar)
import System.IO (hPrint, hReady, hGetLine, Handle, stderr)
import Data.Char (isDigit)

import Debug.Trace (trace)
--import qualified System.IO.Error as Err (CM.catch)
import System.Timeout (timeout)

{-timeout :: Int -> IO a -> IO (Maybe a)
timeout us act = do
    mvar <- newEmptyMVar
    tid1 <- forkIO $ (putMVar mvar . Just $!) =<< act
    tid2 <- forkIO $ threadDelay us >> putMVar mvar Nothing
    res <- takeMVar mvar
    killThread (maybe tid1 (const tid2) res) `catch` ((hPrint stderr) :: SomeException -> IO ())
    return res-}

  --let cp = proc "mpic++" [flags, srcFileName, "-o", exFileName]
  --(_, Just hout, _, _) <- createProcess $ cp { std_out=CreatePipe }

getMaxId :: Expr -> TyEnv -> Idx 
getMaxId exp types = maximum [maxEid, maxVid, maxTEid, maxTVid]
  where minInt = minBound :: Int
        maxEid = runIdentity $ maxExpId exp
        maxVid = maximum $ (minInt):(map snd $ getVarExprIds exp)
        maxTEid = maximum $ (minInt):(map fst types)
        maxTVid = maximum $ (minInt):(getFreeVarIdsInEnv types)

showTime :: UTCTime -> String
showTime tm = formatTime defaultTimeLocale "%s" tm

maxTime = 60 --03*60 --30 --3000 -- 30 seconds

progFileName = "program.flocc"

data SolCtx = SolCtx { 
    ctxRuleset :: Ruleset,
    ctxLibSrc :: String,
    ctxProgramAst :: Maybe Expr,
    ctxVarIds :: [(String, Idx)],
    ctxVarTys :: [(Idx, TySchemeEx)],
    ctxVarIdMap :: DM.Map String Idx,
    ctxVarTyMap :: IM.IntMap TySchemeEx,
    ctxHeaderCode :: String,
    ctxFooterCode :: String,
    ctxMaxExecTime :: Int
  } deriving (Show)


-- |loadContext dirPath. Loads types, rules, flocc program,
-- |flocc library, header cpp and footer cpp code from directory
-- |at dirPath.
loadContext :: String -> IdxMonad IO SolCtx
loadContext path = do
  -- check path exists and is a dir
  exists <- lift $ doesDirectoryExist path
  case exists of
    True -> return ()
    False -> error $ "SolExec:loadContext: search cache directory " ++ path ++ " doesn't exist!"
  -- load flocc lib, header code, footer code
  libStr <- lift $ readFileForce (path ++ "/library.flocc")
  hdrCode <- lift $ readFileForce (path ++ "/header.h")
  ftCode <- lift $ readFileForce (path ++ "/footer.cpp")
  -- parse types
  (varIds, varTys) <- loadDepTypes (path ++ "/types.txt")
  let varTyMap = IM.fromList varTys
  -- parse rules
  ruleset <- lift $ loadRules varIds (path ++ "/ruleset.txt")
  -- parse and preprocess program
  src <- lift $ readFileForce (path ++ "/" ++ progFileName)
  ast <- parseSrc varIds (libStr ++ src)
  ast' <- preprocessExpr varIds ast
  -- check types of input program
  res <- assignDepTypes2 varTyMap ast'
  case res of
    Left bla -> {-error $ "program does type check" ++ (show bla) -- $-} return ()
    Right (cl@(ca :=: cb),tyenv) -> error $ "loadContext:program doesn't type check: " ++ (showP ast') ++ "\n" ++ 
                                 (showP cl) ++ "\n" ++ (show $ (showEmbeddedFuns $ stripTermLabelsRec ca) :=: (showEmbeddedFuns $ stripTermLabelsRec cb)) ++ "\n" ++ 
                                 (showExprWithTypes tyenv ast') ++ "\n" ++ (showExprTreeWithIds ast')
  -- return context
  let ctx = SolCtx { 
      ctxRuleset = ruleset,
      ctxLibSrc = libStr,
      ctxProgramAst = Just ast',
      ctxVarIds = varIds,
      ctxVarTys = varTys,
      ctxVarIdMap = DM.fromList varIds,
      ctxVarTyMap = varTyMap,
      ctxHeaderCode = hdrCode,
      ctxFooterCode = ftCode,
      ctxMaxExecTime = maxTime
    }
  return ctx

-- |completeSolution. Insert casts to make a target AST.
completeSolutions :: String -> SolCtx -> SolId -> IdxMonad IO (Maybe String)
completeSolutions path ctx sid = do
  let varIds = ctxVarIds ctx
  lift $ putStrE $ "entered complete solutions\n"
  -- get cached from context, or from file
  ast <- (case ctxProgramAst ctx of
            -- cache hit
            Just ast1 -> do
              -- update idxmonad
              mxIdx <- maxExpId ast1
              modify (\l -> map (\_ -> mxIdx+1) l)
              return ast1
            -- cache miss
            Nothing -> do
              -- check input program exists
              let fn = path ++ "/" ++ progFileName
              exists <- lift $ doesFileExist fn
              case exists of
                -- error file doesn't exist
                False -> error $ "SolExec: Flocc input program " ++ fn ++ " does not exist!"
                -- load, parse, and preprocess program
                True  -> do
                  -- load and parse program
                  let libSrc = ctxLibSrc ctx
                  src1 <- lift $ readFileForce fn
                  lift $ putStrE $ "read file" ++ src1 ++ "\n"
                  ast1 <- parseSrc varIds (libSrc ++ src1)
                  lift $ putStrE $ "parsed ast1 " ++ (showP ast1) ++ "\n"
                  -- preprocess
                  ast2 <- checkExpIdsUnique2 "parsed" ast1 >>= preprocessExpr varIds --ast1
                  lift $ putStrE $ "preprocessed first " ++ (showP ast2) ++ "\n"
                  --st <- get
                  --lift $ putStr $ "point1: " ++ (show st)
                  return ast2)
  -- apply rules for this solution (and preprocess to get rid of lets)
  let rules = ctxRuleset ctx 
  --st <- get
  --lift $ putStr $ "point2: " ++ (show st)
  ast1 <- checkExpIdsUnique2 "preprocessed1" ast >>= applyRules rules sid
  lift $ putStrE $ "applied rules print " ++ (showP ast1) ++ "\n"
  --st <- get
  --lift $ putStr $ "point3: " ++ (show st)
  ast2 <- checkExpIdsUnique2 "applied rules" ast1 >>= preprocessExpr varIds
  ast3 <- renewExprIds ast2
  -- insert casts to complete solution
  let types = ctxVarTyMap ctx
  let varIdMap = ctxVarIdMap ctx
  t0 <- lift $ getCurrentTime
  lift $ putStrE $ "preprocessed print " ++ (showP ast3) ++ "\n"
  sols <- CM.catch ({-checkExpIdsUnique2 "preprocessed2" ast3 >>=-} (findCasts types varIdMap ast3) >>= (return . Left)) 
                (\e -> return $ Right $ "findCasts:error while processing " ++ (showP ast3) ++ "\n\n" ++ (show (e :: CM.SomeException)))
  lift $ putStrE "findCasts returned\n"
  case sols of
    -- threw error
    Right err -> do
      -- save error
      let fn2 = path ++ "/" ++ (createFilename sid) ++ ".floccerr"
      lift $ writeFileForce fn2 $ "-- error while searching for solution for:\n" ++ (showP ast3) ++ "\n{-" ++ err ++ "-}\n"
      return $ Just err
    -- no solutions, couldn't complete!
    Left ([], dbgMsg) -> do
      -- duration of findCasts
      t1 <- lift $ getCurrentTime
      let castDur = realToFrac $ diffUTCTime t1 t0 
      -- save error
      let fn2 = path ++ "/" ++ (createFilename sid) ++ ".floccerr"
      lift $ writeFileForce fn2 $ "-- can't find solution for:\n" ++ (showP ast3) ++ "\n\n" ++ dbgMsg
      -- return error
      return $ Just $ "findCasts: no solutions found in " ++ (show castDur) ++ "s for:\n" ++ (showP ast3) ++ "\n" ++ (show ast3)
    -- save flocc source for best solution
    Left (solL{-@((expr,tys,costEst):_)-}, _) -> do
      -- duration of findCasts
      t1 <- lift $ getCurrentTime
      let castDur = realToFrac $ diffUTCTime t1 t0 
      -- preprocess again
      --expr' <- preprocessExpr varIds expr
      --error $ "complete solution for " ++ (show sid) ++ ":\n" ++ (show expr')
      -- save
      --let fn2 = path ++ "/" ++ (createFilename sid)
      --lift $ writeFileForce (fn2 ++ ".flocc") (show expr')
      -- save other versions too
      let sols = take numRedistSolsToTry solL
      mapM (\(idx,(expr,tys,costEst)) -> do
        -- write solution to file
        expr' <- preprocessExpr varIds expr
        let fn2 = path ++ "/" ++ (createFilename (sid ++ [idx]))
        lift $ writeFileForce (fn2 ++ ".flocc") (show expr)
        lift $ writeFileForce (fn2 ++ ".types") (show tys)
        lift $ writeFileForce (fn2 ++ ".withtypes2") ("-- sol:\n" ++ (showP expr) ++ "\n\npreprocessed:\n" ++ (showP expr') ++ "\n\nsol with types:\n" ++ (showExprWithTypes tys expr) )
        -- save solution info
        let info = SolMetaInfo { siCastCost=costEst, siNumCastSols=(length solL), siTimeCastSols=castDur }
        lift $ catchRetryIO (saveMetaInfo (fn2 ++ ".info") info) 10
        ) $ zip [1..] sols
      return Nothing

-- |generateSolution. Generate C++ from target AST.
generateSolution :: String -> SolCtx -> SolId -> IdxMonad IO (Maybe String)
generateSolution path ctx sid = do
  -- complete solution if doesn't exist
  let fn = path ++ "/" ++ (createFilename sid)
  exists <- lift $ doesFileExist (fn ++ ".flocc")
  r <- (case exists of 
          True -> return Nothing
          False -> do
            res <- completeSolutions path ctx (init sid) 
            exists' <- lift $ doesFileExist (fn ++ ".flocc")
            if exists' then return Nothing else return $ Just $ "solution " ++ fn ++ " not generated (file doesn't exist)")
  -- generate code for solution
  case r of
    Just err -> return $ Just err
    Nothing -> do
      -- load and parse program
      src <- lift $ readFileForce (fn ++ ".flocc")
      tySrc <- lift $ readFileForce (fn ++ ".types")
      let varIds = ctxVarIds ctx
      -- OLD: parsed and re-assigned types
      {-ast <- parseSrc varIds src
      --let varIds = ctxVarIds ctx
      --ast1 <- preprocessExpr varIds ast
      let ast1 = removeEmptyTups ast
      -- infer types (and simplify)
      let types = ctxVarTyMap ctx
      ret <- assignDepTypes2 types ast1
      let astTypes = (case ret of
                       Left tyenv -> tyenv
                       Right err@(cl,tyenv) -> error $ "generateSolution:assignDepTypesFailed: " ++ (show err) ++ 
                                                       "\n" ++ (showExprWithTypes tyenv ast1) ++ 
                                                       "\n" ++ (showExprTreeWithIds ast1))-}
      --astTypes <- assignDepTypes types ast
      -- NEW: load expr and types (and max sure current indices big enough)
      let types = ctxVarTyMap ctx
      let varIds = ctxVarIds ctx
      let ast1 = (catchRead ("source ast for " ++ (show sid)) src) :: Expr
      let astTypes = (catchRead ("types for " ++ (show sid)) tySrc) :: TyEnv
      let maxId = getMaxId ast1 astTypes
      setMinIndices maxId
      -- apply defaults to types
      let astTypeMp = IM.map (\(Scheme [] t) -> t) $ IM.fromList astTypes
      subs <- fillGapsInEnv astTypeMp
      let astTypes1 = IM.toList $ IM.map (Scheme []) $ applyVarSubstsToVarMap subs astTypeMp
      --let astTypes1' = astTypes
      -- simplify types
      let expEnv = IM.fromList $ makeExprMap ast1
      (astTypes2,_) <- evalEmFunM (simplifyFunsInEnv astTypes1) expEnv types
      -- encap fun parameters in lambdas
      (ast', astTypes3) <- encapFunVars astTypes2 ast1
      -- remove redundant mirr dims
      let astTypes4 = remRedundantDims $ IM.map (\(Scheme [] t) -> t) $ IM.fromList astTypes3
      -- write to file with types
      lift $ writeFileForce (fn ++ ".withtypes") $ (showExprWithTypes (IM.toList $ IM.map (Scheme []) astTypes4) ast') ++ "\n\n" ++ (showExprTreeWithIds ast')
      -- generate code
      (code, dfgStr) <- CM.catch (generate types astTypes4 ast')
                        (\e -> error $ "Error while code generating for " ++ (show sid) ++
                                       "\nAST:\n" ++ (showExprWithTypes (IM.toList $ IM.map (Scheme []) $ astTypes4) ast') ++ 
                                       "\nError: " ++ (show (e :: CM.SomeException)))
      -- save generated code to file
      let hdrCode = ctxHeaderCode ctx
      let ftCode = ctxFooterCode ctx
      lift $ writeFileForce (fn ++ ".cpp") (hdrCode ++ code ++ ftCode)
      lift $ writeFileForce (fn ++ ".dot") dfgStr
      return Nothing

-- |compileMpiCpp flags srcFileName exFileName.
compileCode :: [String] -> String -> String -> IO (Maybe (Int, String))
compileCode flags srcFileName exFileName = do
  (ex, out, err) <- readProcessWithExitCode "mpic++" (flags ++ [srcFileName, "-o", exFileName]) ""
  case ex of
    ExitSuccess   -> return Nothing
    ExitFailure c -> return $ Just (c, err)

-- |compileSolution. Compile generated C++.
compileSolution :: String -> SolCtx -> SolId -> IO (Maybe String)
compileSolution path ctx sid = do
  -- generate code if doesn't exist
  let fn = path ++ "/" ++ (createFilename sid)
  exists <- doesFileExist (fn ++ ".cpp")
  r <- (case exists of 
          True -> return Nothing
          False -> do
            let genSol = evalIdxStateT 0 (generateSolution path ctx sid)
            res <- CM.catch genSol
                         (\e -> trace "caught in compileSol" $ 
                                do tm <- getCurrentTime
                                   let msg = "generateSolution:error while generating " ++ (show sid) ++ "\n" ++ (show (e :: CM.SomeException))
                                   writeFileForce (fn ++ ".generr." ++ (showTime $ tm)) msg
                                   return $ Just msg)
            return res)
  -- compile code
  case r of
    Just err -> return $ Just err
    Nothing -> do
      s <- compileCode ["-O3"] (fn ++ ".cpp") fn
      case s of
        -- compile succeeded
        Nothing -> return Nothing
        Just (rcode, err) -> do 
          let msg = "compiling " ++ (show rcode) ++ ": " ++ err 
          tm <- getCurrentTime
          writeFileForce (fn ++ ".cpperr." ++ (showTime $ tm)) msg
          return $ Just msg

data ProcResult =
    ProcKilled String String
  | ProcSuccess Float String
  | ProcFailure Float Int String

getCharMaybe :: IO (Maybe Char)
getCharMaybe = do
  ready <- hReady stdin
  case ready of
    True -> do
      chr <- hGetChar stdin
      return $ Just chr 
    False -> return Nothing

-- DEPRECATED as left all stdout/err reading to the end, and so
-- processes with a lot of output just stall and timeout when the
-- stdout/err buffers are full.
{-waitProcess :: ProcessHandle -> UTCTime -> NominalDiffTime -> IO (Maybe ExitCode)
waitProcess proc t0 maxDur = do
  ex <- getProcessExitCode proc
  t1 <- getCurrentTime
  let dur = diffUTCTime t1 t0
  -- chr <- getCharMaybe
  case trace ("waiting: " ++ (show ex) ++ ", " ++ (show dur) ++ ", " ++ (show maxDur) ++ "\n" ) ex of
    -- if still running
    Nothing -> if dur > maxDur -- || (isJust chr && fromJust chr == 'c')
      -- if over run then return 
      then return Nothing 
      -- otherwise keep waiting for it
      else do threadDelay 100000 ; waitProcess proc t0 maxDur
    -- if finished
    Just ec -> return $ Just ec-}

whileM :: Monad m => (a -> m Bool) -> a -> (a -> m a) -> m a
whileM pred v0 action = do
  b <- pred v0
  case b of
    True  -> do 
      v1 <- action v0
      whileM pred v1 action
    False -> return v0

waitReadProcess :: (ProcessHandle, Handle, Handle) -> UTCTime -> NominalDiffTime -> String -> String -> IO (Maybe ExitCode, String, String)
waitReadProcess (proc, hout, herr) t0 maxDur outStr errStr = do
  ex <- getProcessExitCode proc
  t1 <- getCurrentTime
  let dur = diffUTCTime t1 t0
  case trace ("waiting: " ++ (show ex) ++ ", " ++ (show dur) ++ ", " ++ (show maxDur) ++ "\n" ) ex of
    -- if still running
    Nothing -> if dur > maxDur -- OR (isJust chr && fromJust chr == 'c')
      -- if over run then return 
      then return (Nothing, outStr, errStr) 
      -- otherwise 
      else do 
        -- get any output
        out <- whileM (\_ -> catch (hReady hout) (\e -> return $ fst (False, e :: IOError))) outStr 
                      (\s0 -> do s1 <- catch (hGetLine hout) (\e -> return $ fst (s0, e :: IOError)) ; return $ s0++s1)
        err <- whileM (\_ -> catch (hReady herr) (\e -> return $ fst (False, e :: IOError))) errStr 
                      (\s0 -> do s1 <- catch (hGetLine herr) (\e -> return $ fst (s0, e :: IOError)) ; return $ s0++s1)
        -- keep waiting for it
        threadDelay 100000 ; 
        waitReadProcess (proc, hout, herr) t0 maxDur out err
    -- if finished
    Just ec -> do
      -- get any output
      err <- catch (hGetContents herr) (\e -> return $ fst (outStr, e :: IOError))
      out <- catch (hGetContents hout) (\e -> return $ fst (errStr, e :: IOError))
      -- return 
      return $ (Just ec, outStr ++ out, errStr ++ err)

timeProcess :: String -> [String] -> NominalDiffTime -> IO ProcResult
timeProcess fileName args maxTime = do
  t0 <- getCurrentTime
  (_, Just hout, Just herr, proc) <- createProcess (proc fileName args) { std_out = CreatePipe, std_err = CreatePipe }
  --res <- waitProcess proc t0 maxTime
  (res, out, err) <- waitReadProcess (proc, hout, herr) t0 maxTime "" ""
  t1 <- getCurrentTime
  let dur = diffUTCTime t1 t0
  case res of 
    -- need to kill process
    Nothing -> do
      --err <- hGetContents herr
      --out <- hGetContents hout
      putStr "killing...."
      --length err `seq` terminateProcess proc
      terminateProcess proc
      putStr "done.\n"
      return $ ProcKilled out err
    -- process finished
    Just ec -> case ec of
      -- success
      ExitFailure ecd -> do
        -- get err string
        --err <- hGetContents herr
        return $ ProcFailure (realToFrac dur) ecd err
      -- error
      ExitSuccess -> do
        -- get out string, and extract time
        --out <- hGetContents hout
        let tmStr = last $ lines out
        let tmStr' = reverse $ takeWhile (\c -> isDigit c || c == '.' || c == '-' || c == '+' || c == 'e' || c == 'E') $ reverse tmStr
        let dur' = (catchRead "SolExec:timeProcess:parsing time from stdout" tmStr') :: Float
        return $ ProcSuccess dur' out

maxGenTime = 15*60*1000000

-- |execSolution. Time execution of solution (generate if not already).
execSolution :: String -> SolCtx -> SolId -> IO [SolCost]
execSolution path ctx sid = do
  putStrE "execSolution entered"
  -- create bin if doesn't exist
  let fn = path ++ "/" ++ (createFilename sid)
  exists <- doesFileExist fn
  r <- (case exists of 
          True -> return Nothing
          False -> do
            res <- timeout maxGenTime (compileSolution path ctx sid) 
            if isNothing res then putStr "generation timeout!\n" else return ()
            let res' = fromMaybe (Just "solution generation timeout") res
            return res')
  -- time bin running
  case trace ("execSolution: " ++ (show r)) r of
    Just err -> return [SolErr err]
    Nothing -> do
      let maxExecTime = realToFrac $ secondsToDiffTime $ fromIntegral $ ctxMaxExecTime ctx
      s <- timeProcess "mpirun" ["-np", "4", fn] maxExecTime
      case s of 
        ProcKilled out err -> do
          tm <- getCurrentTime
          timeout 500 (writeFileForce (fn ++ ".runout." ++ (showTime $ tm)) out)
          timeout 500 (writeFileForce (fn ++ ".runerr." ++ (showTime $ tm)) err)
          return [SolTimeout $ realToFrac maxExecTime]
        ProcSuccess dur out -> do
          tm <- getCurrentTime
          writeFileForce (fn ++ ".runout." ++ (showTime $ tm)) out
          return [SolSucc $ realToFrac dur]
        ProcFailure dur rcode err -> do
          let msg = "running: code " ++ (show rcode) ++ "\n" ++ err
          tm <- getCurrentTime
          writeFileForce (fn ++ ".runerr." ++ (showTime $ tm)) msg
          return [SolErr msg]

{-main :: IO ()
main = do
  putStr "RunProc test\n"
  -- compile program
  ret <- compileMpiCpp [] "/home/taj105/hello.cpp" "/home/taj105/hello"
  case ret of
    Nothing -> putStr "success!\n"
    Just (ec,err) -> putStr $ "error:\n" ++ err ++ "\n"
  putStr "done.\n"
  -- run program
  ret2 <- timeProcess "/home/taj105/hello" [] (secondsToDiffTime 1)
  case ret2 of
    ProcKilled -> putStr "killed!"
    ProcSuccess dt out -> putStr $ "success: " ++ out
    ProcFailure dt ex err -> putStr "failure :("
  putStr "\n"
  return ()-}
