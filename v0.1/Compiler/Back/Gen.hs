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
{-# LANGUAGE ScopedTypeVariables #-}

module Compiler.Back.Gen where

import Compiler.Back.Graph
import Compiler.Back.StrTemplates
import Compiler.Back.Helper
import Compiler.Back.GenDecls
import Compiler.Back.TypeNames

import Data.Map.Strict (Map, unionWith, unionsWith)
import qualified Data.Map.Strict as Data.Map
import qualified Data.IntMap.Strict as Data.IntMap
import qualified Data.Set
import Data.Maybe (fromMaybe, fromJust, isJust)
import Control.Monad.State.Strict (StateT, lift, get, gets, modify, execStateT)
import Control.Monad.Catch
import Data.Functor.Identity (runIdentity)
import Data.Char (toLower)
import Data.List (isInfixOf)


-- Code generator monad helper functions
-- --------------------------------------

-- |checkNodeTreeEx msg nodeTree. Checks if nodeTree has
-- |a non empty path, and if so throws an error.
checkNodeTreeEx :: Monad m => String -> NodeTreeEx -> GenM m
checkNodeTreeEx msg tree = case (treeLabel tree) of
  (nid, []) -> return ()
  (nid, path) -> genError $ "checkNodeTreeEx: Only types and vars can be accessed via TreePaths in NodeTrees: " ++ msg

getGenTrace :: Monad m => GenM1 m String
getGenTrace = do
  msg <- gets genDebugOut
  return msg

-- |createOrGetEnv tries to get local env, but if it doesn't exist
-- |creates an empty one and puts it in the state.
createOrGetEnv :: Monad m => NodeId -> GenM1 m (ValEnv m)
createOrGetEnv nid = do
  envs <- gets genTemEnvs
  case lookupNodeMaybe nid envs of
    Just env -> return env
    Nothing  -> do
      let env = emptyValEnv
      modify (\st -> st { genTemEnvs=Data.IntMap.insert nid env envs })
      return env

-- |returns the local context for the current node
getThisEnv :: Monad m => GenM1 m (ValEnv m)
getThisEnv = do
  st <- get
  let nid = genCurrentNode st
  env <- createOrGetEnv nid
--  let env = lookupNode "getThisEnv" nid $ genTemEnvs st
  return env

-- |modify current locals environment, creating a new one if it doesn't
-- |already exist.
modifyThisEnv :: Monad m => (ValEnv m -> ValEnv m) -> GenState m -> GenState m
modifyThisEnv f st = st { genTemEnvs=Data.IntMap.adjust f nid envs' }
  where nid = (genCurrentNode st)
        envs = genTemEnvs st
        envs' = case lookupNodeMaybe nid envs of
                  Just env -> envs
                  Nothing  -> Data.IntMap.insert nid emptyValEnv envs 

updateThisEnv :: Monad m => (ValEnv m -> ValEnv m) -> GenM m
updateThisEnv f = do
  modify $ modifyThisEnv f 

-- |createOrGetMembers nodeId. Returns the value environment for a 
-- |given node, creating a new empty one if it doesn't already exist.
createOrGetMembers :: Monad m => NodeId -> GenM1 m (ValEnv m)
createOrGetMembers nid = do
  envs <- gets genObjMembers
  case lookupNodeMaybe nid envs of
    Just env -> return env
    Nothing  -> do
      let env = emptyValEnv
      modify (\st -> st { genObjMembers=Data.IntMap.insert nid env envs })
      return env

-- |modifys a generator state's member environment for a node. If
-- |no environment exists yet, it creates a new one.
modifyMembers :: Monad m => NodeId -> (ValEnv m -> ValEnv m) -> GenState m -> GenState m
modifyMembers nid f st = {-trace ("new state at node " ++ (show nid) ++ ": " ++ (show nst) ++ "\n") $-} nst
  where envs = genObjMembers st
        envs' = case lookupNodeMaybe nid envs of
                  Just env -> envs
                  Nothing  -> Data.IntMap.insert nid emptyValEnv envs 
        nst = st { genObjMembers=Data.IntMap.alter (Just . f . fromJust) nid envs' }

-- |updates the generator state's member environment for a node.
updateMembers :: Monad m => NodeId -> (ValEnv m -> ValEnv m) -> GenM m
updateMembers nid f = do
  modify $ modifyMembers nid f

-- |createVar type generates a fresh id for each scalar part of the 
-- |the type, and composes them into an id tree for the VarV.
createVar :: Monad m => Ty -> GenM1 m IdTree
createVar ty = case ty of 
  (Lf a)    -> do
    vid <- newInt
    return $ Lf $ "v" ++ (show vid)
  (Tup l)   -> do
    l' <- mapM createVar l
    return $ Tup l'
  (a :-> b) -> do
    a' <- createVar a
    b' <- createVar b
    return $ a' :-> b'

-- Code generator monad functions
---------------------------------------

-- |newVar ids type generates fresh vars for the id tree and type,
-- |and adds the bindings to the local environment.
newVar :: Monad m => IdTree -> Ty -> GenM m
newVar id ty = do 
  -- align type and ids
  let vars1 = alignTrees ("newVar" ++ show (id, ty)) id ty
  -- create a new var tree for every id
  vars2 <- mapM (\(vid,vty) -> do var <- createVar vty; return (vid, VarV vty var)) vars1
  -- add these vars to the local environment
  updateThisEnv (updates vars2)

-- |newStructVar idTree tyTree. Creates a new struct variable
-- |for every id in the idTree. Differs from newVar, in that newVar
-- |creates a new variable for every scalar part of the type, rather
-- |than a struct for each id.
newStructVar :: Monad m => IdTree -> Ty -> GenM m
newStructVar id ty = do 
  -- align type and ids
  let vars1 = alignTrees ("newStructVar" ++ (show (id, ty))) id ty
  -- create a new struct var for every id
  vars2 <- mapM (\(vname,vty) -> do vid <- newInt; return (vname, VarV vty $ Lf $ "v" ++ (show vid))) vars1
  -- add these to the local environment
  updateThisEnv (updates vars2)

-- |newVal - add a val to thhis env
newVal :: Monad m => Id -> Val m -> GenM m
newVal name val = do
  updateThisEnv (updates [(name, val)])

newIntList :: Monad m => Id -> [Int] -> GenM m
newIntList name list = newVal name (ListV $ map ((LitV).(IntVal)) list)

getIntList :: Monad m => Id -> GenM1 m [Int]
getIntList name = do
  (ListV l) <- getLocalVal name
  let list = map (\(LitV (IntVal i)) -> i) l
  return list

-- setVar1 -- sets a node's public member to one of the vals in the local context
setVar1 :: Monad m => NodeTreeEx -> Id -> Id -> GenM m
setVar1 destNode destId srcId = do
  val <- getLocalVal srcId
  setVal destNode destId val

getVar1 :: Monad m => Id-> NodeTreeEx -> Id -> GenM m
getVar1 destId srcNode srcId = do
  -- get remote value
  val <- getVal srcNode srcId
  -- update local env
  let bindings = [(destId, val)]
  updateThisEnv (updates bindings) 

-- |alignVars destIds srcTy srcIds. Returns a list of mappings
-- |from ids in destIds to their equivalent ids and types in srcTy and srcId,
-- |expanding srcId to access struct members when needed. 
alignVars :: Monad m => IdTree -> Ty -> IdTree -> [(Id, Val m)]
alignVars destIds srcTy srcIds = case (destIds, srcTy, srcIds) of
  (Lf did, ty, id) -> [(did, VarV ty id)]
  (Tup dl, Tup tl, Tup il) | (length dl == length il) && (length il == length tl) -> concat $ map (\(d,i,t) -> alignVars d t i) $ zip3 dl il tl
  (d1 :-> d2, t1 :-> t2, s1 :-> s2) -> (alignVars d1 t1 s1) ++ (alignVars d2 t2 s2)
  tp@(_, _, Lf id) -> map (\(si,(di,t)) -> (di, VarV t (Lf si))) $ makeStructAccessors id (zipTrees ("alignVars" ++ (show tp)) destIds srcTy) -- zip to check types and dest ids align

-- |makeStructAccessors rootId tree. Makes variable names for
-- |accessing the tuple struct called rootId's members that correspond to leaves in tree. 
makeStructAccessors :: Id -> Tree a -> [(Id, a)]
makeStructAccessors rootId tree = case tree of 
  (Lf v) -> [(rootId, v)]
  (Tup l) -> concat $ map (\(t,idx) -> makeStructAccessors (rootId ++ ".v" ++ (show idx)) t) $ zip l [treeIndexBase..]
  (a :-> b) -> (makeStructAccessors (rootId ++ ".v" ++ (show treeIndexBase)) a) ++
               (makeStructAccessors (rootId ++ ".v" ++ (show (treeIndexBase+1))) b)


-- |aliasVar destIds srcIds. Gets the var(s) at srcIds,
-- |and aligns them with the destIds to create some new 
-- |local names for existing vars. 
aliasVar :: forall m . Monad m => IdTree -> IdTree -> GenM m
aliasVar destTree srcTree = do
  -- get src vars
  srcTypes <- visitTreeM (\vid -> do (VarV ty id) <- getLocalVal vid; return ty) srcTree
  srcIds   <- visitTreeM (\vid -> do (VarV ty id) <- getLocalVal vid; return id) srcTree
  -- get list of dest ids to 
  let nVars :: [(Id, Val m)] = (alignVars destTree srcTypes srcIds)
  -- add these vars to  the local env
  updateThisEnv (updates nVars)
  return ()

-- |varExp destId srcId strTem type. Creates a new binding
-- |in the local env called destId, which is bound to the
-- |expression strTem where <v> is replaced with
-- | the var name of the var srcId, with the given type.
-- |Note: the expression is re-evaluated at each reference.
varExp :: Monad m => Id -> Id -> Id -> Ty -> GenM m 
varExp destId srcId strTem ty = case containsTemParam "v" strTem of
  -- if template references the var
  True -> do -- get id of srcId var  
    varVal <- getLocalVal srcId
    case varVal of
      (VarV _ (Lf varId)) -> do
        -- make expression
        let exp = applyT strTem [("v", varId)]
        -- bind in local envq
        let var = VarV ty (Lf exp)  
        setLocalVal destId var
        return ()
      other -> error $ "gen:varExp:val called " ++ (show srcId) ++ " is not a var with a single id: " ++ (show other)
  -- if it doesn't just assign straight to var
  False -> setLocalVal destId $ VarV ty (Lf strTem)


-- TODO: Add list of existing vars that could be reused
--  rather than a new var created, and try and use one of these,
--  then update state to mark that var as used, so no other consumer
--  can use it. 

-- |ifnVarInit decName publicName localNames type val. If a public var already exists
-- |called publicName, then assign it to localNames, otherwise create
-- |a new local var called localNames, and assign it to publicName. Also create
-- |initializing declaration called decName that inits with val. If val is
-- |(LitV NulVal) then doesn't init with any parameters.
ifnVarInit :: Monad m => Id -> Id -> IdTree -> Ty -> Maybe IdTree -> GenM m
ifnVarInit decName publicName localNames varTy varVal = do
  thisNid <- gets genCurrentNode
  desc <- getNodeDesc thisNid
  codeSoFar <- gets genOutBuffs
  -- check if should be a struct (see if struct in any of the names)
  let isStruct = "struct" `isInfixOf` (map toLower $ decName ++ publicName ++ (concat $ flattenTree localNames))
  genTrace $ "ifnVarInit " ++ decName ++ " " ++ publicName ++ "(isStruct=" ++ (show isStruct) ++ ")"
  -- check if a public var exists
  thisNid <- gets genCurrentNode
  vals <- createOrGetMembers thisNid
  case lookupValMaybe publicName vals of
    -- public member exists
    Just val -> do
      -- TODO if it needs to be a struct, then declare a
      --      new var, and assign a value to it.
      case varVal of -- change: 18 oct 2013 - swapped Nothing and _
        -- doesn't need reinit so we're fine
        Nothing -> return () 
        -- try and reinitialize the already declared variable...
        Just initVars -> do
          initVals <- visitTreeM (\i -> do v <- getLocalVal i; return $ Lf v) initVars
          let initVal = treeValToVar ("ifnVarInit:reinit var:" ++ (show val) ++ " with " ++ (show initVals)) initVals
          runGen "initVar" decName [val, initVal]
        --_ -> error $ "ifnVarInit: can't reinitialize already declared var " 
        --             ++ publicName ++ " to " ++ (show varVal) ++ ", in node " ++ desc ++ ", val = " ++ (show val) ++ "!\n" ++ "\n\n" ++ (show codeSoFar)
      -- assign it to local names too
      getVar localNames (LLf (thisNid, []) ()) publicName
      -- assign declaration to blank 
      setLocalVal decName $ CodeV ""
      return ()
    -- public member doesn't exist
    Nothing -> do
      -- create local var
      if isStruct
      then newStructVar localNames varTy 
      else newVar localNames varTy
      -- create it's declaration
      case varVal of 
        Nothing   -> runGenV "declareVar" decName [localNames]
        Just valT -> runGenV "declareVarInit" decName [localNames, valT]
      -- assign to public member
      setVar (LLf (thisNid, []) ()) publicName localNames
      return ()

-- |ifnVar decName publicName localNames varTy. Works as ifnVarInit, only val has values Nothing.
ifnVar decName publicName localNames varTy = ifnVarInit decName publicName localNames varTy Nothing

-- |getLocalVal gets a value from the current node's
-- |local environment, or throws an error if it doesn't exist.
{-getLocalVal :: Monad m => Id -> GenM1 m (Val m)
getLocalVal vid = do
  env <- getThisEnv
  let val = lookupVal "getLocalVar" vid env
  return val-}

-- |setLocalVal id val. Binds val to  the name id
-- |in the local env.
setLocalVal :: Monad m => Id -> Val m -> GenM m
setLocalVal id val = do
  updateThisEnv (updates [(id, val)])

-- |getLVal varId. Returns the value of the var called varId
-- |in the current local environment or throws an error if it is
-- |not defined.
getLocalVal :: Monad m => Id -> GenM1 m (Val m)
getLocalVal varId = do
  thisId <- gets genCurrentNode
  env <- createOrGetEnv thisId
  case Data.Map.lookup varId env of
    Just val -> return val 
    Nothing  -> error $ "getLocalVal: nodeId=" ++ (show thisId) ++ ": var " ++ varId ++ " is not defined:\n" ++ (show env)

getLocalVar :: Monad m => IdTree -> GenM1 m (Val m)
getLocalVar vid = do
  -- get vals for ids
  valTr <- visitTreeM (\i -> do v <- getLocalVal i; return $ Lf v) vid
  return $ treeValToVar "getLocalVar:" valTr

-- |getVal srcNode srcId. Gets the public member called srcId at
-- |srcNode and returns it.
getVal :: Monad m => NodeTreeEx -> Id -> GenM1 m (Val m)
getVal srcNode srcId = do
  genTrace "entered getVal"
  let (nid, path) = treeLabel srcNode
  -- get public env
  st <- get
  genTrace "getVal: got public env"
  thisNodeDesc <- getNodeDesc $ genCurrentNode st
  srcNodeDesc <- getNodeDesc nid
  let errMsg = "getVal:thisNode=" ++ (show $ genCurrentNode st) ++
               ",srcNode=" ++ (show srcNode) ++ "\nthisNode: " ++ thisNodeDesc ++ "\nsrcNode: " ++ srcNodeDesc ++ "\n" ++ (show $ genGraphs st) ++ "\n\n"
  let remEnvs = genObjMembers st
  errTrace1 <- getGenTrace
  --remEnv <- createOrGetMembers nid
  let remEnv = lookupNode ("Node public member env defined! " ++ errMsg ++ errTrace1) nid remEnvs 
  -- get value 
  genTrace $ "getVal: looked up objMemEnv for " ++ (show $ treeLabel srcNode) ++ ": \n" ++ (show remEnv) 
  errTrace2 <- getGenTrace
  let val = lookupVal (errMsg {-++ errTrace2-}) srcId remEnv
  genTrace $ "getVal got val: " ++ (show val)
  let subVal = lookupSubVal ({-errTrace2 ++-} errMsg) val path
  genTrace $ "getVal subval path is: " ++ (show path)
  genTrace $ "getVal got subval: " ++ (show subVal)
  return subVal

-- |getValMaybe srcNode srcId. Looks up the public member called srcId
-- |in srcNode's public members. Throws an error if no public env exists
-- |for srcNode.
getValMaybe :: Monad m => NodeTreeEx -> Id -> GenM1 m (Maybe (Val m))
getValMaybe srcNode srcId = do
  thisNid <- gets genCurrentNode
  graphs <- gets genGraphs
  let errMsg = (show graphs) ++ "\ngetValMaybe:this=" ++ (show thisNid) ++ ",srcNode=" ++ (show srcNode) ++ ",srcId=" ++ srcId ++ ":"
  publicEnvs <- gets genObjMembers
  let (nid, path) = treeLabel srcNode
  case Data.IntMap.lookup nid publicEnvs of 
    Just env -> case Data.Map.lookup srcId env of
      Just val -> return $ Just $ lookupSubVal (errMsg ++ "val=" ++ (show val) ++ ":") val path
      Nothing  -> return Nothing
    Nothing -> return Nothing

-- |getVal2 srcNode srcId bindGenF. Gets the public member value stored at node
-- |srcNode under srcId, then applies bindGenF to create new local var-value bindings
-- |from the value, and updates the current node's local environment by adding these 
-- |bindings.
getVal2 :: Monad m => NodeTreeEx -> Id -> (Val m -> [(Id, Val m)]) -> GenM m
getVal2 srcNode srcId bindGenF = do
  -- get remote value
  val <- getVal srcNode srcId
  genTrace $ "getVal2: got remote value"
  -- generate new local bindings from it
  let bindings = bindGenF val
  -- update local env
  updateThisEnv (updates bindings)
  genTrace $ "getVal2: updated this env"
  genTrace $ "getVal2: src node " ++ (show srcNode) 
  genTrace $ "getVal2 src id " ++ srcId ++ "\n" 
  genTrace $ "getVal2 val " ++ (show val) ++ "\n" 
  genTrace $ "getVal2 bindings " ++ (show bindings)  
  genTrace $ "getVal2: " ++ (show srcNode) ++ "." ++ srcId ++ "\n" ++ (show bindings)

-- |setVal destNode destId val. Sets the public member called destId at destNode
-- |to val.
setVal :: Monad m => NodeTreeEx -> Id -> (Val m) -> GenM m
setVal destNode destId val = do
  genTrace $ "entered setVal with " ++ (show destNode) ++ "." ++ (show destId) ++ " = " ++ (show val)
  -- get the node id, and tree path
  let (destNodeId, destPath) = treeLabel destNode
  -- update the relevant binding in the node's public member environment
  updateMembers destNodeId $ Data.Map.alter (alterSubVal destPath val) destId
  genTrace $ "setVal " ++ (show $ treeLabel destNode) ++ "." ++ destId ++ " to " ++ (show val)
  mems <- createOrGetMembers destNodeId
  genTrace $ (show destNode) ++ " members=" ++ (show mems) ++ "\n" 
  genTrace "leaving setVal"

-- |setVal destNode destId srcId valGenF. Gets all the local vals in srcId, combines
-- |them into a new val using valGenF, and then adds this to destNode's public
-- |members under destId.
setVal2 :: Monad m => NodeTreeEx -> Id -> IdTree -> (Tree (Val m) -> Val m) -> GenM m
setVal2 destNode destId srcId valGenF = do
  -- get vals from local environment
  vals <- visitTreeM (\i -> do v <- getLocalVal i; return $ Lf v) srcId
  -- make them into a new val
  let val = valGenF vals
  setVal destNode destId val

-- |getVar -- gets a var from an object's environment into the local context
-- |if there is no members environment set yet, or the var doesn't exist, it throws
-- |an error.
getVar :: Monad m => IdTree -> NodeTreeEx -> Id -> GenM m
getVar destId srcNode srcId = do
  let errMsg = ("getVar" ++ (show (destId, srcNode, srcId)))
  genTrace $ "getVar: " ++ (show destId) ++ " = " ++ (show srcNode) ++ "." ++ srcId ++ "\n"
  getVal2 srcNode srcId (\val -> case val of -- check it's a var
    (VarV ty idTree) -> 
      -- depreceated: as didn't work when srcId is a single id
      --   and destId is a tree. 
      -- --------------------------
      -- align dest id tree with var&type trees
      --let ids = alignTrees (errMsg ++ "ids") destId idTree in
      --let types = alignTrees (errMsg ++ "types") destId ty in
      --let vars1 = zip ids types in -- DANGEROUS ZIPPING - ASSUMES alignTrees always follows the same order
      --let vars2 = map (\((n,vid),(_,ty)) -> (n, VarV ty vid)) vars1 in
      -- vars2  
      -- -------------------------------
      -- new version: expands with tuple accessors when needed
      alignVars destId ty idTree
    other -> error $ "getVar: " ++ (show srcNode) ++ "." ++ srcId ++ 
                                " is " ++ (show val) ++ ", not a var\n")

-- |ifVarExists destId srcNode srcId thenAction elseAction. Like getVar, only if the var
-- |doesn't exist it performs elseAction, and if it does, in after binding
-- |it to destId locally, it performs thenAction.
ifVarExists :: Monad m => Id -> NodeTreeEx -> Id -> (GenM m) -> (GenM m) -> GenM m
ifVarExists destId srcNode srcId thenAction elseAction = do
  -- see if remote value exists
  mbval <- getValMaybe srcNode srcId
  case mbval of
    -- if it does
    Just val -> do
      -- bind it locally
      getVar1 destId srcNode srcId
      -- perform action
      thenAction
    -- otherwise
    Nothing  -> elseAction

-- |isVarsExist vars thenAction elseAction. Checks if all the vars in the list
-- |[(destId, srcNode, srcId)] exist. If they do, binds them to the destIds in the
-- |local env, and performs thenAction. Else performs elseAction.
ifVarsExist :: Monad m => [(Id, NodeTreeEx, Id)] -> (GenM m) -> (GenM m) -> GenM m
ifVarsExist vars thenAction elseAction = do
  -- for all vals
  mbvals <- mapM (\(destId, srcNode, srcId) -> getValMaybe srcNode srcId) vars
  -- check if they are all true (return just)
  case and $ map isJust mbvals of
    -- all these vars exist
    True -> do
      -- bind them locally 
      mapM (\(destId,srcNode,srcId) -> getVar1 destId srcNode srcId) vars
      -- perform action
      thenAction
    -- they don't all exist
    False -> elseAction

-- |treeValToVar vals. Takes a tree of Var vals and composes them to form a
-- |Var val.
treeValToVar :: Monad m => String -> Tree (Val m) -> Val m
treeValToVar errMsg vals = VarV ty id
  -- check they are vars, and get type tree and id tree
  where errMsg' = errMsg ++ "treeValToVar(" ++ (show vals) ++ "): "
        id = runIdentity $ visitTreeM (\v -> let (ty,it) = varVal errMsg' v in return it) vals
        ty = runIdentity $ visitTreeM (\v -> let (ty,it) = varVal errMsg' v in return ty) vals

-- setVar -- sets a node's public member to one of the vars in the local context
setVar :: Monad m => NodeTreeEx -> Id -> IdTree -> GenM m
setVar destNode destId srcId = do
  setVal2 destNode destId srcId (treeValToVar "setVar:")

-- |setFun node procId argIdTree proc. Creates a new template procedure and
-- |adds it to the public members of the node given.
setFun :: Monad m => NodeTreeEx -> Id -> Maybe IdTree -> TemplateProc m -> GenM m
setFun destNode destId argIdTree proc = do
  -- check nodeTree doesn't refer to a tree path
  checkNodeTreeEx "setFun" destNode
  -- get the destination node id
  let (destNodeId, _) = treeLabel destNode
  -- check that destNode refers to the current node
  curNid <- gets genCurrentNode
  if curNid /= destNodeId 
    then error $ "setFun:Assigning a function '" ++ destId ++ "' to a node (" 
             ++ (show destNodeId) ++ ") that isn't the current node (" 
             ++ (show curNid) ++ ")! "
    else return ()
  -- update the relevant binding in the node's public member environment
  let val = (FunV argIdTree proc)
  updateMembers destNodeId $ Data.Map.alter (\_ -> Just val) destId
  genTrace $ "setFun " ++ (show $ treeLabel destNode) ++ "." ++ destId ++ " to " ++ (show val)
  return ()

-- |callFun node procId valIdTree. Gets the procedure stored at procId in node's 
-- |public members, and invokes it with the node as the current node.
callFun :: Monad m => NodeTreeEx -> Id -> Maybe IdTree -> GenM m
callFun node procId valIdTree = {-trace ("callFun: " ++ (show node) ++ "." ++ (show procId)) $-} do
  -- remember current node id, and look at next one
  st <- get
  let startNid = genCurrentNode st
  let (newNid, _) = treeLabel node
  -- debug trace
  genTrace $ "callFun (from " ++ (show startNid) ++ ") " ++ (show newNid) ++ "." ++ procId ++ " with (" ++ (show valIdTree) ++ ")\n" 
  -- get argument val tree from id tree
  valTree <- (case valIdTree of
    Just vt -> do
      vt' <- visitTreeM (\i -> do v <- getLocalVal i; return $ Lf v) vt
      return $ Just vt'
    Nothing -> return Nothing)
  -- update current node id
  modify (\s -> s { genCurrentNode=newNid } )
  -- log in debug trace
  genTrace $ "in:callFun (from " ++ (show startNid) ++ ") " ++ (show newNid) ++ "." ++ procId ++ " with (" ++ (show valTree) ++ ")\n" 
  -- check nodeTree doesn't refer to a tree path
  checkNodeTreeEx "callFun" node
  -- save current local context
  origLocals <- createOrGetEnv newNid
  -- search through members to get function
  errTrace <- getGenTrace
  let errMsg = "callFun:curNodeId=" ++ (show $ genCurrentNode st) ++ 
                      ",procNodeId=" ++ (show newNid) ++ 
                      ",procId=" ++ procId ++ 
                      ",with " ++ (show valTree) ++ "\n" ++ errTrace
  let remEnvs = genObjMembers st
  let remEnv = lookupNode (errMsg ++ "\nperhaps this node isn't in the dfg? e.g. a stream with no consumers.") newNid remEnvs 
  let val = lookupVal errMsg procId remEnv
  -- check its a procedure
  case val of
    FunV argIdTree proc -> do
      -- add valTree params to local context
      case (argIdTree, valTree) of
        (Just idTree, Just vals) -> do
          --let bindings = alignTrees idTree vals
          let bindings = treeToList $ zipValTrees idTree vals
          genTrace $ "callFun:zipValTrees:\n" ++ (show idTree) ++ " with \n" ++ (show vals) ++ "\nGives:\n" ++ (show bindings)
          --let bindings' = map (\(i, Lf v) -> (i, v)) bindings
          updateThisEnv (\env -> updates bindings env)
          -- apply it
          proc vals
        (Nothing, Nothing) -> do
          genTrace "here2\n"
          -- apply it
          proc (error $ "callFun, no vals supplied!")
        (Just _, Nothing) -> error $ "callFun: " ++ (show startNid) ++ " calling " ++ (show node) ++
                                     "." ++ procId ++ ", takes arguments but hasn't been given any."
        (Nothing, Just _) -> error $ "callFun: " ++ (show startNid) ++ " calling " ++ (show node) ++
                                     "." ++ procId ++ ", doesn't take arguments, but has been given some."
    other     -> error $ errMsg ++ ": " ++ (show node) ++ "." ++ procId ++ 
                                " is " ++ (show val) ++ ", not a procedure/funV.\n"
  -- remove valTree from local context
  updateThisEnv (\_ -> origLocals)
  -- reinstate previous current node id
  modify (\s -> s { genCurrentNode=startNid } )
  return ()

-- |callAll node procId valIdTree. Gets all of node's outputs
-- |and invokes the procedure called procId at each of them,
-- |with the parameters implied by valIdTree. Returns number of consumers.
callAll :: Monad m => NodeTreeEx -> Id -> Maybe IdTree -> GenM1 m Int
callAll = callConsumers
{-callAll node procId valIdTree = do
  -- get all node's outputs
  graph <- gets genGraph
  let [thisNode] = getNodes "callAll:thisNode:" graph [treeLabel node]
  let outIds = nodeOut thisNode
  -- call procId at each of them
  mapM (\nid -> callFun (LLf nid ()) procId valIdTree) outIds
  return ()-}

-- |callConsumers node procId valIdTree. Gets all of node's consumers
-- |and invokes the procedure callec procId at each of them, with the
-- |parameters implied by valIdTree. Then gets all members of the
-- |preceding nodes that have changed, merges the changes, and applies
-- |them to node's public members. Returns the number of consumers.
callConsumers :: Monad m => NodeTreeEx -> Id -> Maybe IdTree -> GenM1 m Int
callConsumers node procId valIdTree = do
  genTrace "entered callConsumers"
  -- check nodeTree doesn't refer to a tree path
  checkNodeTreeEx "callConsumers" node
  -- get node consumers
  (graph:tail) <- gets genGraphs
  let (nodeId, _) = treeLabel node
  let (producers, consumers) = getNodeConsumers graph nodeId
  -- trace for debugging
  startNid <- gets genCurrentNode
  genTrace $ "callConsumers (from " ++ (show startNid) ++ ") " ++ (show node) ++ "." ++ procId ++ " with (" ++ (show valIdTree) ++ ")\n" ++
                "producers: " ++ (show producers) ++ "\nconsumers: " ++ (show consumers) ++ "\n" ++ "graph: \n" ++ (show graph)
  -- get their public environments before the calls
  let prods = Data.Set.toList producers  
  envsBefore <- mapM createOrGetMembers prods
  -- call procId at each of the consumers
  let cons = Data.Set.toList consumers
  mapM (\nid -> callFun (LLf (nid,[]) ()) procId valIdTree) cons
  -- find changed members of environments
  envsAfter <- mapM createOrGetMembers prods
  let eqEnvsBefore = map (Data.Map.map toOrdVal) envsBefore
  let eqEnvsAfter = map (Data.Map.map toOrdVal) envsAfter
  let changedValEnvs = map (\(b,a) -> Data.Map.map fromOrdVal $ getMapChanges a b) $ zip eqEnvsBefore eqEnvsAfter 
  -- merge the changes into node's public members
  errTrace <- gets genDebugOut
  let errMsg = "callConsumers:\n" ++ errTrace 
  let merged = unionsWith (mergeVals (errMsg ++ " envsBefore:\n" ++ (show envsBefore) ++ "\n\nenvsAfter:\n" ++ (show envsAfter))) changedValEnvs 
  updateMembers nodeId (unionWith (mergeVals (errMsg ++ " envsBefore:\n" ++ (show envsBefore) ++ "\n\nenvsAfter:\n" ++ (show envsAfter))) merged)
  genTrace $ "finished callConsumers: " ++ (show merged)
  return $ length cons

-- |shouldBeGlobal node. Returns true if the value returned
-- |by node should be a global var (e.g. is used in a funNode). 
shouldBeGlobal :: Monad m => NodeTreeEx -> GenM1 m Bool
shouldBeGlobal node = do
  genTrace "entered shouldBeGlobal"
  -- check nodeTree doesn't refer to a tree path
  checkNodeTreeEx "shouldBeGlobal" node
  -- get node consumers
  graphs@(graph:tail) <- gets genGraphs
  let (nodeId, _) = treeLabel node
  let (_, consumers) = getNodeConsumers graph nodeId
  -- see if any of them are funNodes
  let nodes = getNodes ("shouldBeGlobal " ++ (show nodeId)) graphs $ Data.Set.toList consumers
  let funNodes = filter (isFunNd . nodeTy) nodes
  genTrace "entered shouldBeGlobal"
  -- if some are funNodes then return True
  return $ if funNodes == [] then False else True

-- |tryCall node procId valIdTree. Calls node.procId if it exists,
-- |and does nothing otherwise. 
tryCall :: Monad m => NodeTreeEx -> Id -> Maybe IdTree -> GenM m
tryCall node procId valIdTree = {-trace ("tryCall: " ++ (show node) ++ "." ++ procId ++ "(" ++ (show valIdTree) ++ ")\n") $-} do
  -- check nodeTree doesn't refer to a tree path
  checkNodeTreeEx "tryCall" node
  -- get node object members
  let (nodeId, _) = treeLabel node
  remEnv <- createOrGetMembers nodeId
  -- look for proc
  case Data.Map.lookup procId remEnv of
    Just val -> callFun node procId valIdTree -- if exists call it
    Nothing  -> return ()

-- |getCode destId srcNode srcId. Gets the code from srcNode.srcId
-- |and adds it to the local context under destId.
getCode :: Monad m => Id -> NodeTreeEx -> Id -> GenM m
getCode destId srcNode srcId = do
  genTrace $ "getCode: local " ++ destId ++ 
    " = " ++ (show srcNode) ++ "." ++ srcId 
  -- check nodeTree doesn't refer to a tree path
  checkNodeTreeEx "getCode" srcNode
  -- get code and return it
  getVal2 srcNode srcId (\val -> [(destId, val)]) 

-- |setCode destNode destId tem. Expands tem using the current
-- |local vars, and then sets destNode's public member called destId
-- |to the expanded code.
setCode :: Monad m => NodeTreeEx -> Id -> StrTem -> GenM m
setCode destNode destId tem = do
  genTrace $ "entered setCode " ++ (show destNode) ++ "." ++ destId ++ " = " ++ (show tem)
  -- check nodeTree doesn't refer to a tree path
  checkNodeTreeEx "setCode" destNode
  -- get local context
  env <- getThisEnv
  -- expand the template using its values
  let code = applyTem ("setCode:destNode=" ++ (show destNode) ++ ";destId=" ++ destId ++ ":") tem $ Data.Map.toList env
  -- set it
  setVal destNode destId (CodeV code)
  genTrace "leaving setCode"

-- |addCode destNode destId tem. Expands tem using the
-- |current local vars, gets the current value of destId
-- |at destNode, appends the expanded template, and saves it
-- |back to the state. destId must already exist or it will
-- |throw an error!
addCode :: Monad m => NodeTreeEx -> Id -> StrTem -> GenM m
addCode destNode destId tem = do
  genTrace $ "entered addCode " ++ (show destNode) ++ "." ++ destId ++ " += " ++ (show tem)
  -- check nodeTree doesn't refer to a tree path
  checkNodeTreeEx "addCode" destNode
  -- get local context
  env <- getThisEnv
  -- expand the template using its values
  let code2 = applyTem ("addCode:destNode=" ++ (show destNode) ++ ";destId=" ++ destId ++ ":") tem $ Data.Map.toList env
  -- get current val, if doesn't exist init to blank
  let (destNodeId, _) = treeLabel destNode
  mems <- createOrGetMembers destNodeId
  let val = fromMaybe (CodeV "") $ lookupValMaybe destId mems
  -- append code to it
  case val of
    CodeV code1 -> do 
      let code3 = code1 ++ code2 
      -- set it
      setVal destNode destId (CodeV code3)
      genTrace "leaving addCode"
      return ()
    other       -> error $ "addCode: " ++ (show other) ++ 
                           " is not code, when adding to " ++ (show destNode) ++ "." ++ destId 

expandTem :: Monad m => String -> StrTem -> GenM1 m Code
expandTem msg tem = do
  genTrace $ "entered expandTem: \n" ++ (show tem)  
  -- get local context
  env <- getThisEnv
  -- expand the template using its values
  let code = applyTem (msg ++ ":expandTem:") tem $ Data.Map.toList env
  return code

-- |output streamId template expands the template using the values of the current node's
-- |local vars and appends it to the stream identified by streamId. If the stream does not
-- |yet exist, creates it, and appends the expanded template to it.
output :: Monad m => Id -> StrTem -> GenM m
output sid tem = do
  genTrace $ "entered output to " ++ sid ++ ":\n" ++ (show tem)  
  -- get local context
  env <- getThisEnv
  -- expand the template using its values
  let code = applyTem "output:" tem $ Data.Map.toList env
  -- append the output to the correct stream
  modify (\st -> st { genOutBuffs=adjustOrCreate "" (\c -> c ++ code) sid $ genOutBuffs st } )
  genTrace $ "leaving output to " ++ sid

-- |outputDecl node dec. Checks to see if declaration should
-- |be global by calling shouldBeGlobal, and outputs to
-- |main or globals as appropriate.
outputDecl :: Monad m => NodeTreeEx -> StrTem -> GenM m
outputDecl node dec = do
  -- see if should be a global
  isGlob <- shouldBeGlobal node  
  -- output to correct stream
  let stm = if isGlob then "globals" else "main"
  output stm dec
  return ()

-- |getGlobal envName key. Looks up a value with key in the globals Map called envName.
getGlobal :: Monad m => String -> Tree OrdVal -> GenM1 m (Maybe (Val m))
getGlobal envName key = do
  globals <- gets (Data.Map.lookup envName . genGlobals)
  case globals of
    Just globals -> return $ Data.Map.lookup key globals
    Nothing      -> return Nothing 

-- |setGlobal key val. Inserts, updates, or deletes the value of key in the
-- |globals map.
setGlobal :: Monad m => String -> Tree OrdVal -> Maybe (Val m) -> GenM m
setGlobal envName key val = do
  modify (\st -> st { 
    genGlobals=Data.Map.alter (\env -> Just (Data.Map.alter (\_ -> val) key (fromMaybe Data.Map.empty env))) 
                              envName 
                              (genGlobals st) } )

-- |runGen genId destVarId argVars. Runs the generator called genId
-- |with arguments from argVars, and binds the result to destVarId in the current local
-- |vars environment.
runGen :: Monad m => Id -> Id -> [Val m] -> GenM m
runGen genId destVarId vals = do
  -- lookup generator
  gens <- gets (globGenerators . genConsts)
  case Data.Map.lookup genId gens of
    Just gen -> do
      -- run generator
      result <- gen vals
      -- assign result to destVarId
      updateThisEnv (\env -> Data.Map.alter (\_ -> Just result) destVarId env)
      return ()
    Nothing  -> error $ "runGen: no generator called " ++ genId ++ " in the generator constants!"

-- |runGenV genId destVarId varIds. Runs the generator called genId
-- |with arguments from the local variables refered to as varIds,
-- |and assigns the result to destVarId in the locals environment.
runGenV :: Monad m => Id -> Id -> [IdTree] -> GenM m
runGenV genId destVarId varIds = do
  genTrace $ "runGenV " ++ genId ++ " " ++ destVarId ++ " " ++ (show varIds)
  -- get vals for ids
  valTrList <- mapM (visitTreeM (\i -> do v <- getLocalVal i; return $ Lf v)) varIds
  let valList = map (treeValToVar "runGenV:") valTrList
  -- generate code
  runGen genId destVarId valList  

-- |getFun node. Returns a GraphV for the function graph
-- |stored in node.
-- TODO Will there ever be Lambdas that take Lambdas as arguments?
-- Because if so we need to support having trees of any kind of Vals
-- passed to Lambda input nodes, including GraphVs.
getFun :: Monad m => NodeTreeEx -> GenM1 m (Val m)
getFun nodeTr = do
  let (nodeId, path) = treeLabel nodeTr
  if path /= [] then 
    genError $"getFunNode: can't access fun graph in a nested tuple tree! " 
       ++ (show nodeId) ++ "." ++ (show path) 
  else return ()
  graphs <- gets genGraphs
  let node = lookupGraphNode "getFunNode" nodeId graphs
  let nty = nodeTy node
  case nty of
    FunNd {-inNid-} graph -> return $ fromFunNode nty
    other             -> genError $ "getFunNode: can't access fun graph from non-FunNd node: " ++ (show node)

varsToExclude :: Data.Map.Map Id ()
varsToExclude = Data.Map.fromList [(outVarName, ()), ("streamVar", ()), ("count", ())]

-- |evalFun funVal inVarVal outVarVal. Creates a new copy of 
-- |the graph funVal with new node ids, then assigns input and output
-- |vars to it, and generates the code for the graph.
evalFun :: (Monad m, MonadCatch m) => Val m -> Val m -> NodeTreeEx -> Val m -> GenM1 m Code
evalFun (GraphV {-inNid-} fgraphIn) inVar inNode outVar = do
  genTrace $ "entered evalFun with\ninVar:" ++ (show inVar) ++ "\noutVar: " ++ (show outVar) ++ "\ngraph:\n" ++ (show fgraphIn)
  -- get node to import env from
  let (inNodeId,_) = treeLabel inNode
  inEnv <- (if (inNode == emptyNodeTreeEx) 
    then return emptyValEnv -- no node given
    else (do -- get env from node
      publicEnvs <- gets genObjMembers ; 
      return $ (lookupNode ("evalFun: can't find env for input node " ++ (show inNode)) inNodeId publicEnvs) `Data.Map.difference` varsToExclude))
  -- un-nest subgraph if fgraphIn just returns another graph
  let fgraph = getNestedGraph fgraphIn
  genTrace $ "evalFun: un-nested graph to " ++ (show fgraph)
  -- save current graph
  graphs <- gets genGraphs
  -- remove any var nodes that have same ids as nodes in parent graphs
  let allParNodes = Data.IntMap.unions $ map graphNodes graphs
  let fgraph2 = removeParentNodes allParNodes fgraph
  -- duplicate fun graph
  embeddedGraphs <- gets (getGraphsInTys . globTypes . genConsts)  -- graphs in types
  let nextInt = (+1) $ maximum $ (map maxNodeId $ (fgraph2:graphs) ++ embeddedGraphs )
  genTrace $ "evalFun:nextInt=" ++ (show nextInt)
  skipInts nextInt
  newNids <- createNewNodeIds fgraph2
  genTrace $ "evalFun:newNids=" ++ (show newNids)
  let inNid = graphIn fgraph2
  let nInNid = fromMaybe (error $ "evalFun: inNid " ++ (show inNid) ++ " not in new node id map!") $ Data.IntMap.lookup inNid newNids
  let nfgraph = replaceNodeIds newNids fgraph2
  let outNid = graphOut nfgraph
  -- set the current graph to this function's graph
  graphStack <- pushGraph nfgraph
  -- copy types of old nodeids to new node ids
  modify (\st -> st { genConsts=(genConsts st) { globTypes=duplicateNodeEnvIds newNids (globTypes $ genConsts st) } } )
  -- assign ins and outs
  genTrace "evalFun: here" 
  setVal (LLf (nInNid, []) ()) outVarName inVar
  genTrace "evalFun: here2" 
  setVal (LLf (outNid, []) ()) outVarName outVar
  -- add vars from inEnv to inVar's public environment
  mapM (\(vid, val) -> setVal (LLf (nInNid, []) ()) vid val) $ Data.Map.toList inEnv
  -- save current "main" output stream
  outBufs <- gets genOutBuffs
  let origMain = fromMaybe (error $ "evalFun: no main buff! " ++ (show outBufs)) $ Data.Map.lookup "main" outBufs
  -- make current output stream blank
  modify (\st -> st {genOutBuffs=(Data.Map.insert "main" "" $ genOutBuffs st)})
  -- remember this node id
  thisNid <- gets genCurrentNode
  -- display flocc body code
  --output "main" $ "/* fun: " ++ (show fgraph2) ++ "*/\n"
  -- visit (once to propagate vars, and again to generate)
  --error $ "evalFun: \n" ++ (show nfgraph)
  generateM graphStack
  -- check if the input and output nids were the same (i.e. identity function)
  if (nInNid == outNid) && (inVar /= outVar) 
    then do runGen "assignVar" "outAssignment" [outVar, inVar]
            output "main" "// identity fun assignment\n<outAssignment>\n"
    else do return ()
  -- restore this node id
  modify (\st -> st { genCurrentNode=thisNid } )
  -- get "main" output stream
  outBufs2 <- gets genOutBuffs
  let newMain = fromMaybe (error $ "evalFun: no main buff! " ++ (show outBufs)) $ Data.Map.lookup "main" outBufs2
  -- restore "main" output stream to what it was
  modify (\st -> st {genOutBuffs=(Data.Map.insert "main" origMain $ genOutBuffs st)}) 
  -- restore graph to the previous graph
  popGraph
  -- return stuff generated in main
  genTrace "leaving evalFun"
  return newMain

-- |eval funId inVarId outVarId. Generates the code to
-- |implement the graph stored as funId in the local env
-- |with the vars stored as inVarId and outVarId in the
-- |local env.
{-eval :: Monad m => Id -> Id -> Id -> GenM m
eval funId inVarId outVarId = do
  -- get vals 
  funVal <- getLVal funId
  inVar <- getLVal inVarId
  outVar <- getLVal outVarId
  -- eval fun
  evalFun funVal inVar outVar-}

-- |genFun codeVarName funVal inVars outVars. Generates code to implement
-- |funVal using input vars inVars and outVars outVars (stored in local env).
-- |Stores the resultant code in the local env as codeVarName.
genFun :: (Monad m, MonadCatch m) => Id -> Val m -> Ty -> IdTree -> NodeTreeEx -> IdTree -> GenM m
genFun codeVarName funVal funTy inVars inNode outVars = do
  -- get vars 
  inV <- visitTreeM (\i -> do v <- getLocalVal i; return $ Lf v) inVars
  outV <- visitTreeM (\i -> do v <- getLocalVal i; return $ Lf v) outVars
  -- check types match
  let inVar = (treeValToVar "genFun:inV:" inV) 
  let outVar = (treeValToVar ("genFun(" ++ codeVarName ++ ", " ++ (show funVal) ++ "):outV:") outV)
  let (VarV inTy _) = inVar
  let (VarV outTy _) = outVar
  let funTy2 = inTy :-> outTy
  case {-funTy == funTy2 -} (mapTree eqTys funTy) == (mapTree eqTys funTy2) of
    -- types match
    True -> do
			-- generate code
			code <- evalFun funVal inVar inNode outVar
			-- assign code to codeVarName
			updateThisEnv (\env -> Data.Map.insert codeVarName (CodeV code) env)
			return ()
    -- types don't matchq
    False -> do
      let errMsg = "genFun:Var types don't match function type!\nvar type: " ++ 
                   (show funTy2) ++ "\nfun type: " ++ (show funTy) ++ "\n" ++ "\n" ++ 
                   (show $ mapTree eqTys funTy) ++ "\nfun type: " ++ (show $ (mapTree eqTys funTy2)) ++ "\n" ++ codeVarName ++ "\n\n"
      genError errMsg
      debug <- gets genDebugOut
      error $ debug ++ errMsg

-- |appFun codeVarName funNode inVars outVars. Generates code for the
-- |lambda at funNode, with inVars and outVars, assigning the generated
-- |code to codeVarName in the local environment.
genFunV :: (Monad m, MonadCatch m) => Id -> NodeTreeEx -> IdTree -> NodeTreeEx -> IdTree -> GenM m
genFunV codeVarName funNode inVars inNode outVars = do
  -- get function type
  types <- gets (globTypes . genConsts)
  let (funNodeId,_) = treeLabel funNode
  let funTy = lookupNode ("genFunV: can't find type for lambda node " ++ (show funNode)) funNodeId types
  -- get function
  fun <- getFun funNode
  -- generate code for it
  genFun codeVarName fun funTy inVars inNode outVars
  return ()

-- |getNestedGraph graph. Checks if graph returns another
-- |graph, and if it does, returns that nested graph.
getNestedGraph :: Graph -> Graph
getNestedGraph graph = case Data.IntMap.lookup (graphOut graph) (graphNodes graph) of
  Just outNode -> case nodeTy outNode of
    -- look at type of nested function
    FunNd graph' -> getNestedGraph graph'
    -- other 
    other -> graph
  Nothing -> graph -- removed error below. it's ok if outnode is not in the graph e.g. returns a 
                   -- value bound in a parent graph.
                   -- error $ "Back:Gen:getNestedGraph: out node not in graph!\n" ++ (show graph)

-- |getGraphTy graph. Returns the type of the function
-- |represented by the graph.
getGraphTy :: Monad m => Graph -> GenM1 m Ty
getGraphTy graph = do
  -- see if graph contains nested graph
  let graph' = getNestedGraph graph
  -- lookup types of in node and out node
  types <- gets (globTypes.genConsts)
  let inTy = fromMaybe (error $ "Back:Gen:getGraphTy: type of graph input node not in map: " ++ (show graph)) $ Data.IntMap.lookup (graphIn graph') types
  let outTy = fromMaybe (error $ "Back:Gen:getGraphTy: type of graph out node not in map: " ++ (show graph)) $ Data.IntMap.lookup (graphOut graph') types
  -- return as function type
  return $ inTy :-> outTy

-- |getGraphTyV val. Returns the type of the graph in the
-- |variable, type, or node respectively.
getGraphTyV :: Monad m => Either (Val m) NodeTreeEx -> GenM1 m Ty
getGraphTyV val = case val of
  Left (IdV vid) -> do
    (GraphV graph) <- getLocalVal vid
    getGraphTy graph
  Left (TyV (Lf (FunTy graph)))  -> do
    getGraphTy graph
  Right node     -> do
    (GraphV fun) <- getFun node
    getGraphTy fun
  other -> error $ "Back:Gen:getGraphTyV: can't get function from " ++ (show val)

-- |genTyFunV codeVarName funTy inVars outVars. Generates code for
-- |the function stored in funTy, with inVars and outVars.
genTyFunV :: (Monad m, MonadCatch m) => Id -> Ty -> IdTree -> NodeTreeEx -> IdTree -> GenM m
genTyFunV codeVarName funTy@(Lf (FunTy graph)) inVars inNode outVars = case funTy of
  -- get fun from type
  (Lf (FunTy graph)) -> do  
    -- DANGEROUS: doesn't check that inVar and outVar types match function
    -- get vars for ids
    --inVVals <- visitTreeM (\id -> do var <- getLocalVal id; return $ Lf var) inVars
    --outVVals <- visitTreeM (\id -> do var <- getLocalVal id; return $ Lf var) outVars
    --let inVar = treeValToVar "Back:Gen:genTyFunV: converting in tree of input vars to an input var." inVVals
    --let outVar = treeValToVar "Back:Gen:genTyFunV: converting in tree of output vars to an output var." outVVals
    -- generate code
    --code <- evalFun (GraphV graph) inVar outVar
    -- assign code to codeVarName
    --updateThisEnv (\env -> Data.Map.insert codeVarName (CodeV code) env)
    --return ()
    -- NEW VERSION: Does check types.
    tyOfFun <- getGraphTy graph
    genFun codeVarName (GraphV graph) tyOfFun inVars inNode outVars
  -- errorneous type
  other -> error $ "Back:Gen:genTyFunV: funTy does not contain a function graph!\n" ++ (show funTy)

-- TODO Generate function: generates class in decls
-- Class name
-- Method name
-- Function (in type/node)
-- ...

-- |genProjFun []. Generates a class for this projection function, with 
-- |proj() and inject() members. (Does not cache in globals).
genStaticFun :: (Monad m, MonadCatch m) => Graph -> Maybe Ty -> Maybe Ty -> String -> GenM1 m Ty
genStaticFun graph domTy' ranTy' qualifiers = do
  genTrace "ENTERED GENSTATICFUN:"
  -- get type of function
  funTy <- getGraphTy graph
  let (domTy :-> ranTy) = funTy
  if domTy /= fromMaybe domTy domTy' 
  then error $ "Back:Gen:genStaticFun:fun dom types don't match:\n" ++ 
               (show domTy) ++ "\n" ++ (show domTy') 
  else return ()
  if ranTy /= fromMaybe ranTy ranTy' 
  then error $ "Back:Gen:genStaticFun:fun range types don't match:\n" ++ 
               (show ranTy) ++ "\n" ++ (show ranTy') 
  else return ()
  -- create input and output variables
  vid <- newInt >>= (return . show)
  newStructVar (Lf ("arg"++vid)) domTy
  newStructVar (Lf ("res"++vid)) ranTy
  runGenV "declareVar" ("decArg"++vid) [Lf $ "arg"++vid]
  runGenV "declareVar" ("decRes"++vid) [Lf $ "res"++vid]
  -- generate code for function body
  genFun ("bodyCode"++vid) (GraphV graph) funTy (Lf $ "arg"++vid) (emptyNodeTreeEx) (Lf $ "res"++vid)
  -- generate class code and add to declarations
  let className = "fun_class_" ++ vid
  let (domTy :-> ranTy) = funTy
  runGenV "genTyName" "domTy" [Lf $ "arg"++vid]
  runGenV "genTyName" "ranTy" [Lf $ "res"++vid]
  --let ranTn' = fromMaybe (error $ "Back:Gen:genStaticFun: no type name for: " ++ (show ranTy)) ranTn
  let ret = (if ranTy == Lf NullTy || ranTy == Lf (LfTy "Null" [])
             then "return 0; // null value, is 0 char: "
             else "return ")
  let declCode = applyT (funClassTemplate vid) [("className", className), ("qualifiers", qualifiers), ("ret", ret)]
  output "funs" declCode
  return $ (Lf $ LfTy "FunClass" [Lf $ LfTy className []])

funClassTemplate :: String -> StrTem
funClassTemplate vid = "\
 \ namespace flocc {\n\
 \   struct <className> {\n\
 \   public:\n\
 \       <qualifiers> <ranTy> run(<domTy> <arg" ++ vid ++ ">) {\n\
 \           <decRes" ++ vid ++ ">;\n\
 \           <bodyCode" ++ vid ++ ">;\n\
 \           <ret> <res" ++ vid ++ ">;\n\
 \        }\n\
 \   };\n\
 \ }\n"



-- Generate functions
-- -----------------------------------------

outVarName = "vname"

-- |generateVisitor graph node performs whatever generation actions
-- |are required for each node in the graph.
generateVisitor :: (Monad m, MonadCatch m) => [Graph] -> Node -> GenM m
generateVisitor graphs node = {-trace ("genVisitor: " ++ (show node) ++ "\n") $-} do
  -- set current node to this one
  let thisNodeId = nodeId node
  modify (\st -> st {genCurrentNode=thisNodeId})
  genTrace $ "gen visiting " ++ (show thisNodeId) ++ ": " ++ (show node) ++ "\n"
  -- perform action for this node type
  case nodeTy node of
    GlobalVarNd ty vname -> do
      genTrace $ "gen visiting a GlobalVar and setting " ++ (outVarName) ++ " to " ++ (show vname) 
      setVal (LLf (thisNodeId, []) ()) outVarName (VarV ty (Lf vname))
      return ()
    TupNd -> do
      -- get vars from all inputs
      let inNodeIds = nodeIn node
      inNodeVars <- mapM (\nid -> getValMaybe (LLf (nid, []) ()) outVarName) inNodeIds
      let inNodes = getNodes "generateVisitor:tupNode:get input nodes" graphs inNodeIds
      -- (give correct types for missing vars)
      tyEnv <- gets (globTypes . genConsts)
      let (Tup tupTys) = lookupNode "generateVisitor:tupNode:tyTree:" thisNodeId tyEnv
      let inNodeVars' = map (\(nd, mbVar, ty) -> fromMaybe (VarV ty (Lf $ "noOutVarNode/*" ++ (show nd) ++ "*/")) mbVar) $ zip3 inNodes inNodeVars tupTys
      --let inNodeVars' = map (fromMaybe $ error errMsg) inNodeVars
      -- combine them into one var
      let outVar = treeValToVar "generateVisitor:TupNd:outVar:" (Tup $ map Lf inNodeVars')
      -- (do same with stream vars...)
      --inNodeSVars <- mapM (\nid -> getValMaybe (LLf (nid, []) ()) "streamVar") inNodeIds
      --let inNodeSVars' = map (\(nd, mbVar) -> fromMaybe (VarV (lfTy "unknownStreamVarType" []) (Lf $ "noStreamVarNode" ++ (show nd))) mbVar) $ zip inNodes inNodeSVars
      --let outSVar = treeValToVar "generateVisitor:TupNd:streamVar:" (Tup $ map Lf inNodeSVars')
      --setVal (LLf (thisNodeId, []) ()) "streamVar" outSVar   
      -- see if there is already an output var here
      thisPubEnv <- createOrGetMembers thisNodeId
      case Data.Map.lookup outVarName thisPubEnv of
        -- generate an assignment curVar = outVar 
        -- and leave var as curVar
        Just (VarV curVarTy curVarId) -> do
          -- don't do it immediately, but do it on second pass
          -- when "gen" functions are applied
          setFun (LLf (thisNodeId, []) ()) "gen" Nothing (\_ -> do
            runGen "assignVar" "outAssignment" [VarV curVarTy curVarId, outVar]
            output "main" "// TupNd assignment\n<outAssignment>\n")
          return ()
        -- use var from input as own output var
        Nothing -> setVal (LLf (thisNodeId, []) ()) outVarName outVar         
      return ()
    TupAccNd idx -> do
      -- get var from input and try to access idx part of it
      let [inNodeId] = nodeIn node
      outVar <- getValMaybe (LLf (inNodeId, [idx]) ()) outVarName
      let outVar' = fromMaybe (VarV (lfTy "unknownOutVarType" []) (Lf "noOutVar")) outVar
      -- (do same with stream vars...)
      --outSVar <- catch (getValMaybe (LLf (inNodeId, [idx]) ()) "streamVar") (\e -> return $ fst $ (Nothing, e :: SomeException))
      --let outSVar' = fromMaybe (VarV (lfTy "unknownStreamVarType" []) (Lf "noStreamVar")) outSVar
      --setVal (LLf (thisNodeId, []) ()) "streamVar" outSVar'
      -- see if there is already an output var here (called curVar)
      thisPubEnv <- createOrGetMembers thisNodeId
      case Data.Map.lookup outVarName thisPubEnv of
        -- generate an assignment curVar = outVar 
        -- and leave var as curVar
        Just (VarV curVarTy curVarId) -> do
          -- don't do it immediately, but do it on second pass
          -- when "gen" functions are applied
          setFun (LLf (thisNodeId, []) ()) "gen" Nothing (\_ -> do
            runGen "assignVar" "outAssignment" [VarV curVarTy curVarId, outVar']
            output "main" "// TupAccNd case assignment\n<outAssignment>\n")
          return ()
        -- use var from input as own output var
        Nothing -> setVal (LLf (thisNodeId, []) ()) outVarName outVar'
    LitNd val -> case val of
      -- if null val, don't assign it
      NulVal -> do
        newVar (Lf "v") $ scalValType val
        ifnVar "decNullVar" outVarName (Lf "nullVal") $ scalValType NulVal
        output "main" $ "// <v> = " ++ (show val) ++ "\n"
        return ()
      -- non-null val
      _ -> do
        -- create new var if doesn't already exist (e.g. output of fun)
        ifnVar "decVar" outVarName (Lf "v") $ scalValType val
        output "main" $ "<decVar><v> = " ++ (show val) ++ ";\n"
        -- create new var for value
        --newVar (Lf "v") $ scalValType val
        -- assign vname for the node
        --setVar (LLf (thisNodeId, []) ()) outVarName (Lf "v")
        -- output declaration and init to main stream
        --output "main" ("int <v> = " ++ (show val) ++ ";\n")
        return ()
    AppNd     -> do
      -- get input nodes
      let [funNode, inNode] = getNodes "generateVisitor:appNode:" graphs $ nodeIn node
      -- create type tree
      tyEnv <- gets (globTypes . genConsts)
      let tyTree = lookupNode "generateVisitor:appNode:tyTree:" (nodeId funNode) tyEnv
      -- create nodeid tree
      let nodeTree = buildNodeTree graphs thisNodeId tyTree
      -- see if is a library function or a lambda
      case nodeTy funNode of
        -- a library function
        VarNd fname -> do
          -- get template
          templates <- {-trace ("genVisitor: " ++ (show nodeTree) ++ "\n") $-} gets (globTemplates . genConsts)
          case Data.Map.lookup fname templates of
            Just temFun -> do
              -- execute template at node
              genTrace $ "applying template " ++ (show fname) ++ " with " ++ (show nodeTree)
              setLocalVal "tem" (IdV fname)
              temFun tyTree nodeTree
              return ()
            Nothing -> error $ "generateVisitor:appNode: can't find template for function " ++ fname ++ "!\n"
        -- a lambda term
        FunNd {-inNodeId-} funGraph -> do
          -- get input var
          -- 
          -- TODO Implement this case (although shouldn't these be removed by preprocessing)
          {-let maxInt = maxNodeId funGraph
          skipInts (maxInt+1)
          newNids <- createNewNodeIds funGraph
          let newFunGraph = replaceNodeIds newNids funGraph
          error $ show newFunGraph-}
          error $ "generateVisitor:FunNd not implemented yet:\nNode:" ++ (show node) ++ "\nGraph:\n" ++ (show funGraph)
          return ()
        -- anything else
        other -> genError $ "generateVisitor:AppNd: Function nodes must be either VarNds or FunNds:\n" ++ (show funNode)
    other -> return () -- do nothing

-- |geneateVisitor2 graph node. Tries to call the procedure
-- |"gen" for each node.
generateVisitor2 :: Monad m => [Graph] -> Node -> GenM m
generateVisitor2 graphs node = {-trace ("genVisitor2: " ++ (show node) ++ "\n") $-} do
  -- set current node to this one
  let thisNodeId = nodeId node
  modify (\st -> st {genCurrentNode=thisNodeId})
  genTrace $ "gen2 visiting " ++ (show thisNodeId) ++ "\n"
  -- try and invoke procedure "gen"
  tryCall (LLf (thisNodeId,[]) ()) "gen" Nothing

enabledFlagName = "nodeEnabled"

type EnabledFlags = Tree Bool

-- |generareVisitor3 graph node. Propagates "enabled" trees
-- |throughout graph, so discover which nodes should be visited
-- |and which should not.
generateVisitor3 :: Monad m => [Graph] -> Node -> GenM m
generateVisitor3 graphs node = do
  -- set current node to this one
  let thisNodeId = nodeId node
  modify (\st -> st {genCurrentNode=thisNodeId})
  genTrace $ "gen3 visiting " ++ (show thisNodeId) ++ "\n"
  -- propagate enabled flags
  case nodeTy node of
    -- literals are always enabled
    LitNd v      -> setVal (LLf (thisNodeId, []) ()) enabledFlagName (TreeV $ Lf $ BoolV True)
    -- functions are always enabled (since they are never key function parameters)
    FunNd {-_-} _ -> setVal (LLf (thisNodeId, []) ()) enabledFlagName (TreeV $ Lf $ BoolV True)
    -- get flags for inputs, and compose them
    -- if input doesn't have a flag, throw error
    TupNd        -> do
      let inNodeIds = nodeIn node
      inNodeFlagVals <- mapM (\nid -> getVal (LLf (nid, []) ()) enabledFlagName) inNodeIds
      -- get out of TreeV's and compose into a new Tup TreeV      
      let inNodeFlagTrees = map fromTreeVal inNodeFlagVals
      let flagTree = Tup inNodeFlagTrees
      setVal (LLf (thisNodeId, []) ()) enabledFlagName (TreeV flagTree)
    -- get flags for input, and select right part
    TupAccNd idx -> do
      -- get input's flag tree
      let [inNodeId] = nodeIn node
      inFlagVal <- getVal (LLf (inNodeId, []) ()) enabledFlagName
      let inFlagTree = fromTreeVal inFlagVal      
      -- get flag for this part of tuple
      let flagTree = lookupTreeNodeOrLeaf "generateVisitor3:TupAccNd:" inFlagTree [idx]
      setVal (LLf (thisNodeId, []) ()) enabledFlagName (TreeV flagTree)
    -- check that flags have been set for this, otherwise
    -- set to default: enabled.
    VarNd name   -> do
      inFlagVal <- getValMaybe (LLf (thisNodeId, []) ()) enabledFlagName 
      case inFlagVal of
        Just _ -> return () -- do nothing, because already defined 
        Nothing -> setVal (LLf (thisNodeId, []) ()) enabledFlagName (TreeV $ Lf $ BoolV True) -- set to default: true
    -- get flags for input, and if not all enabled
    -- set flag to disabled
    other -> do
      let inNodeIds = nodeIn node
      inNodeFlagVals <- mapM (\nid -> getVal (LLf (nid, []) ()) enabledFlagName) inNodeIds
      -- get out of TreeV's and check to see if any are false     
      let inFlagTree = Tup $ map fromTreeVal inNodeFlagVals
      case treeContains (\(BoolV flag) -> not flag) inFlagTree of
        -- if there is a disabled, this is disabled
        True  -> setVal (LLf (thisNodeId, []) ()) enabledFlagName (TreeV $ Lf $ BoolV False)
        -- if they are all enabled, this is enabled
        False -> setVal (LLf (thisNodeId, []) ()) enabledFlagName (TreeV $ Lf $ BoolV True)
   -- _ -> return ()

-- |visitIfEnabled visitFun graph node. Applies visitFun unless node's enabled
-- |flag tree is all false (i.e. there is no true)
visitIfEnabled :: Monad m => ([Graph] -> Node -> GenM m) -> [Graph] -> Node -> GenM m
visitIfEnabled visitFun graphs node = do
  -- see if this node is enabled
  flagTreeVal <- getVal (LLf (nodeId node, []) ()) enabledFlagName
  let flagTree = fromTreeVal flagTreeVal
  case treeContains (\(BoolV flag) -> flag) flagTree of
    False  -> return () -- don't visit it because all leaves are disabled
    True -> visitFun graphs node -- visit it, because at least one leaf is enabled

-- |generateM graph. Visits graph, calling generateVisitor at
-- |each node.
generateM :: (Monad m, MonadCatch m) => [Graph] -> GenM m
generateM graphs = do
  -- disable all nodes that aren't being used
  visitDeepestGraphM partitionByTy generateVisitor3 graphs
  -- init all nodes - invoking their templates
  visitDeepestGraphM partitionByTy (visitIfEnabled generateVisitor) graphs
  -- call "gen" proc for each node (where defined)
  visitDeepestGraphM partitionByTy (visitIfEnabled generateVisitor2) graphs
  return ()

-- |generate graph. Generates code for the graph given.
generate :: (Monad m, MonadCatch m) => (GenM m) -> Generators m -> Templates m -> NodeEnv Ty -> Graph -> Int -> m (Map Id Code)
generate initAction generators templates types graph numTopDims = do
  let initGlob = GenConsts {
    globTypes=types,
    globTemplates=templates,
    globGenerators=generators,
    globNumTopDims=numTopDims
  }
  let initSt = GenState {
    genGraphs=[graph],
    genCurrentNode=(-1),
    genCurrentInt=1,
    genTemEnvs=emptyNodeEnv,
    genObjMembers=emptyNodeEnv,
    genOutBuffs=Data.Map.empty,
    genGlobals=emptyValMap,
    genDebugOut="",
    genConsts=initGlob
  }
  genSt <- execStateT (initAction >> generateM [graph]) initSt
  return $ genOutBuffs genSt

