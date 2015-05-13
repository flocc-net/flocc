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
module Compiler.Types.TermLanguage where

import Compiler.Front.Indices (Idx, IdxSet, newid, newidST, getnid)
import Compiler.Front.Common (delimList, dtvids, funLParen, funRParen, findAndModify, foundKey, modifyValue, tracerEx, xor, Mappable(monadicMap), listGet)
import Compiler.Front.ExprTree (Expr(Tup), getExprId)
import Compiler.Types.Variables (VarsIn(..), VarSubsts, applyVarSubst)
--import ShowLatex

import Control.Monad.State.Strict
import Control.Monad.Identity
import Data.Foldable (foldrM)
import Data.Either (partitionEithers)
import Data.Set (Set, member)
import qualified Data.Set as DS
import qualified Data.Set (fromList, union)
import Data.List ((\\), nub)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M

import Debug.Trace (trace)

-- |Tracer function for debugging displaying all constraints as they are unified
trcUnifyCon :: Show a => a -> a
trcUnifyCon = id --tracerEx "Unifying: " -- id

-- |Data type for term language
data Term t =
    Var Idx
  | UniVar Idx
  | Ref Idx
  | Term t [Term t]
  deriving (Eq, Ord)

-- |Implementation of show for terms
instance Show t => Show (Term t) where
  show (Term t []) = (show t)
  show (Term t l) = "(" ++ (show t) ++ " " ++ (delimList " " $ map show l) ++ ")"
  show (Var i) = "v" ++ (show i)
  show (UniVar i) = "uv" ++ (show i)
  show (Ref i) = "r" ++ (show i)

-- |applyVarSubst takes a map of substitutions and a var id
-- |and returns the substituted value if there is one, or 
-- |Var i if there isn't.
{-applyVarSubst :: VarsIn a => VarSubsts a -> Idx -> a
applyVarSubst subs i = case IM.lookup i subs of
  Just b -> b
  Nothing -> newVar i-}

-- |mapTermM f term. Applies f to all subterms, and then to the new terms
-- |created by them.
mapTermM :: Monad m => (Term t -> m (Term t)) -> Term t -> m (Term t)
mapTermM f t = case t of
  (Term t l) -> do
    l' <- mapM (mapTermM f) l
    let t' = Term t l'  
    t'' <- f t'
    return t'' 
  other -> f other

instance Mappable (Term t) where
  monadicMap f term = case term of
    -- recursive case
    (Term t l) -> do
      l' <- mapM (monadicMap f) l
      let term' = Term t l'
      term'' <- f term'
      return term''
    -- base case
    other -> f term

{-instance ShowLatex t => ShowLatex (Term t) where
  showAsLatex (Term t []) = showAsLatex t
  showAsLatex (Term t l) = "(" ++ (showAsLatex t) ++ " " ++ (delimList " " $ map showAsLatex l) ++ ")"
  showAsLatex (Var i) = "\\var" ++ (show i)
  showAsLatex (Ref i) = "\\fun" ++ (show i)-}

-- |Allows terms to be compared
{-instance Ord t => Ord (Term t) where
  compare x y = case (x,y) of
    (Var a, Var b) -> compare a b
    (Ref a, Ref b) -> compare a b
    (Term t l, Term t' l') -> case compare t t' of
       EQ -> compare l l'
       other -> other
    (Ref _, Var _) -> LT
    (Var _, Ref _) -> GT
    (Var _, Term _ _) -> LT
    (Term _ _, Var _) -> GT
    (Ref _, Term _ _) -> LT
    (Term _ _, Ref _) -> GT 

  x <= y           =  compare x y /= GT
  x <  y           =  compare x y == LT
  x >= y           =  compare x y /= LT
  x >  y           =  compare x y == GT

  max x y 
       | x >= y    =  x
       | otherwise =  y
  min x y
       | x <  y    =  x
       | otherwise =  y-}

termContains :: Eq t => t -> Term t -> Bool
termContains tok term = case term of
  Term tok' l | tok == tok' -> True
  Term tok' l -> or $ map (termContains tok) l
  other -> False 

termContainsUniVar :: Term t -> Bool
termContainsUniVar term = case term of
  UniVar i -> True
  Term _ l -> or $ map termContainsUniVar l
  _ -> False

getVarIdsInTerm t = case t of
  Term t l -> nub $ concat $ map getVarIdsInTerm l
  Var i -> [i]
  _ -> []

getRefIdsInTerm :: Term t -> [Idx]
getRefIdsInTerm t = case t of
  Term t l -> concat $ map getRefIdsInTerm l
  Ref i -> [i]  
  _ -> []

instance VarsIn (Term t) where
  isVar (Var i) = Just i
  isVar _       = Nothing
  getVars t = Data.Set.fromList (getVarIdsInTerm t)
  newVar i = Var i
  applyVarSubsts subs t = case t of
    (Var i)      -> applyVarSubst subs i
    (Term tok l) -> Term tok $ map (applyVarSubsts subs) l
    other        -> other

-- |getSubTerms name offset. Gets all the nth type parameters of terms called
-- |name.
getSubTerms :: (Ord t, Show t) => t -> Int -> Term t -> DS.Set (Term t)
getSubTerms tok n ty = case ty of
    -- matching terms
    (Term tok' l) | tok == tok' -> l' `DS.union` (DS.singleton $ listGet "TermLang:getSubTerms" l n)
      where l' = DS.unions $ map rec l
    -- tuples
    (Term tok' l) -> DS.unions $ map rec l
    -- terminals
    other -> DS.empty
  where rec = getSubTerms tok n

-- |Data type for "term schemes", qualified terms in the language
-- |(those with bound variables)
data Scheme t = Scheme [Idx] (Term t)
  deriving (Eq)

-- |Display a term scheme
instance Show t => Show (Scheme t) where
  show (Scheme [] t) = show t 
  show (Scheme l t)  = "(forall " ++ (delimList "," $ map (\i -> ("V" ++ show i)) l) ++
                      " => " ++ (show t) ++ ")"

getSchemeTerm :: Scheme t -> Term t
getSchemeTerm (Scheme _ t) = t

-- |Returns a list of free variables in a term scheme
getFreeVarIdsInScheme :: Scheme t -> [Idx]
getFreeVarIdsInScheme (Scheme l t) = (getVarIdsInTerm t) \\ l

-- |Generalize a term to make it a scheme
generalizeTerm :: TermEnv t -> Term t -> Scheme t
generalizeTerm env t = Scheme vars t
  where vars = ((getVarIdsInTerm t) \\ (getFreeVarIdsInEnv env))

-- |Instantiates all unique vars with different ids, such that 
-- |two different unique vars will never equal each other.
instantiateUniVars :: Monad m => Term t -> StateT IdxSet m (Term t)
instantiateUniVars term = case term of
  (UniVar iv) -> do
    iv' <- newidST dtvids
    return (UniVar iv')
  (Term t l) -> do
    l' <- mapM instantiateUniVars l
    return (Term t l')
  other -> return other

-- |Instantiates a term scheme by replacing every qualified term variable
-- |with a new variable.
instantiateScheme :: (Eq t, Monad m) => Scheme t -> StateT IdxSet m (Term t) 
instantiateScheme (Scheme vars term) = do
  newVars <- mapM (\_ -> newTermVarIdxFromState) vars
  let varPairs = zip vars newVars
  let varSubs = map (\(from,to) -> (Var from) :|-> (Var to)) varPairs 
  let term' = forAllSubs subInTerm varSubs term
  term'' <- instantiateUniVars term'
  return term''

-- |Applies a function that takes a Term to a Scheme containing a term
applyToScheme :: (Term t -> Term t) -> Scheme t -> Scheme t
applyToScheme f (Scheme l t) = (Scheme l $ f t) 

-- |renumberScheme takes a scheme and replaces all integer var ids
-- |with new 1-based ints.
renumberScheme :: Eq t => Scheme t -> Scheme t
renumberScheme (Scheme l t) = Scheme (snd $ unzip newnums) (forAllSubs subInTerm subs t)
  where newnums = zip l [1..]
        subs = map (\(i1,i2) -> (Var i1 :|-> Var i2)) newnums

-- |renumberSchemes takes a list of schemes and replaces all bound
-- |integer var ids with new 1-based ones, and all free variables with
-- |integer var ids that start at the number after the new maximum bound var id.
renumberSchemes :: Eq t => [Scheme t] -> [Scheme t]
renumberSchemes l = map (\(Scheme l t) -> (Scheme l $ (forAllSubs subInTerm subs t))) reschemes
  where reschemes = map renumberScheme l
        freeVars = nub $ concat $ map getFreeVarIdsInScheme reschemes
        maxnum = maximum $ map (\(Scheme l _) -> maximum l) reschemes
        newnums = zip freeVars [(maxnum+1)..]
        subs = map (\(i1,i2) -> (Var i1 :|-> Var i2)) newnums

-- |IdTree is a succinct type for simple id trees.
data IdTree =
    IdTup [IdTree]
  | IdLeaf Idx
  | IdBlank
  deriving (Eq)

instance Show IdTree where
  show (IdTup l)  = "(" ++ (delimList ", " $ map show l) ++ ")"
  show (IdLeaf i) = "V" ++ (show i)
  show (IdBlank)  = "_"

-- |getIdsInIdTree takes an IdTree and returns a lift of 
-- |all id values it contains
getIdsInIdTree :: IdTree -> [Idx]
getIdsInIdTree it = case it of
  (IdTup l)  -> concat $ map getIdsInIdTree l 
  (IdLeaf i) -> [i]
  (IdBlank)  -> []

-- |getIdExprIdPairs zips together an IdTree and a tuple expression tree
-- |returning a lift of pairs of id tree ids to expression ids. 
getIdExprIdPairs :: (IdTree, Expr) -> [(Idx, Idx)]
getIdExprIdPairs ab = case ab of
  ((IdTup al),(Tup _ bl)) | length al == length bl -> concat $ map getIdExprIdPairs $ zip al bl
  ((IdLeaf ai),expr) -> [(ai, getExprId expr)]
  ((IdBlank),_) -> []
  other -> error $ "IdTree and Expr tuple tree are not isomorphic: " ++ (show ab)

-- |SchemeEx is a type that extends term schemes to
-- |have an extra tree of bound variables that can be
-- |used within the term.
data SchemeEx t = SchemeEx IdTree (Scheme t)
  deriving (Eq)

instance Show t => Show (SchemeEx t) where
  show (SchemeEx IdBlank inner) = show inner
  show (SchemeEx (IdTup []) inner) = show inner
  show (SchemeEx it inner) = "(forall " ++ (show it) ++ " => " ++ (show inner) ++ ")"

-- |Returns a list of free variables in a term scheme
getFreeVarIdsInSchemeEx :: SchemeEx t -> [Idx]
getFreeVarIdsInSchemeEx (SchemeEx it inner) = (getFreeVarIdsInScheme inner) \\ (getIdsInIdTree it)

-- |Generalize a term to make it a SchemeEx
generalizeTermEx :: TermEnv t -> Term t -> SchemeEx t
generalizeTermEx env t = SchemeEx IdBlank (generalizeTerm env t)

-- |Instantiates a term SchemeEx by replacing every qualified term variable
-- |with a new variable, and every function application qualified variable 
-- |with a ref to that var id (or expression id).
instantiateSchemeEx :: (Eq t, Monad m) => SchemeEx t -> Expr -> StateT IdxSet m (Term t) 
instantiateSchemeEx (SchemeEx it inner) expr = do
  term <- instantiateScheme inner
  let varPairs = getIdExprIdPairs (it, expr)
  let varSubs = map (\(from,to) -> (Var from) :|-> (Ref to)) varPairs 
  let term' = forAllSubs subInTerm varSubs term
  return term'

-- |instantiateSchemeEx2 takes an extended term scheme and returns a term. 
instantiateSchemeEx2 :: (Eq t, Show t, Monad m) => SchemeEx t -> StateT IdxSet m (Term t)
instantiateSchemeEx2 (SchemeEx it inner) = case it of
  IdBlank  -> instantiateScheme inner 
  IdTup [] -> instantiateScheme inner
  other    -> error $ "Can't instantitate an extended term scheme " 
                   ++ (show $ SchemeEx it inner) ++ " without a "
                   ++ "function app expression to bind the terms to."  

-- |schemeEnvToSchemeExEnv 
schemeEnvToSchemeExEnv :: TermEnv t -> [(Idx, SchemeEx t)]
schemeEnvToSchemeExEnv env = map (\(i,s) -> (i, SchemeEx IdBlank s)) env

type TermEnv t = [(Idx, Scheme t)]

-- |Get all unbound term vars in an environment
getFreeVarIdsInEnv :: TermEnv t -> [Idx]
getFreeVarIdsInEnv env = nub $ concat $ map getFreeVarIdsInScheme schemes
  where (_,schemes) = unzip env

emptyTermEnv :: TermEnv t
emptyTermEnv = []

mapTermEnv :: (Scheme t -> Scheme t) -> TermEnv t -> TermEnv t
mapTermEnv f env = map (\(i,t) -> (i,f t)) env

filterTermEnv :: ((Idx, Scheme t) -> Bool) -> TermEnv t -> TermEnv t
filterTermEnv f env = filter f env

lookupTerm :: Show t => TermEnv t -> Idx -> Scheme t
lookupTerm env idx = case lookup idx env of
  Just t -> t
  Nothing -> error $ "no term exists with idx " ++ (show idx) ++ " in env " ++ (show env) 

lookupTermMaybe :: TermEnv t -> Idx -> Maybe (Scheme t)
lookupTermMaybe env idx = lookup idx env

addTermToEnv :: TermEnv t -> Scheme t -> Idx -> TermEnv t
addTermToEnv env term idx = (idx,term):env

-- |Updates an entry in an environment to a new term, or adds it if it
-- |doesn't already exist.
updateTermInEnv :: TermEnv t -> Scheme t -> Idx -> TermEnv t
updateTermInEnv ((id, term):tail) newTerm searchId = if id == searchId 
  then ((searchId, newTerm):tail)
  else ((id, term):(updateTermInEnv tail newTerm searchId))
updateTermInEnv [] newTerm searchId = [(searchId, newTerm)]

concatTermEnvs :: [TermEnv t] -> TermEnv t
concatTermEnvs l = concat l

bindTermInState :: Monad a => Scheme t -> Idx -> StateT (TermEnv t) a (Scheme t)
bindTermInState term idx = do
  modify (\env -> addTermToEnv env term idx)
  return term 

-- |Binds a new term to an id that already has a binding.
rebindTermInState :: Monad a => Scheme t -> Idx -> StateT (TermEnv t) a (Scheme t)
rebindTermInState term idx = do
  modify (\env -> updateTermInEnv env term idx)
  return term

showTermFromEnv :: Show t => TermEnv t -> Idx -> String
showTermFromEnv env idx = " :: " ++ case lookupTermMaybe env idx of
  Just t -> show t
  Nothing -> "null"

monadicOr :: Monad m => Bool -> Bool -> m Bool
monadicOr a b = do 
  return (a || b)

-- |For terms a, b returns True iff a occurs somewhere in b
occursInTerm :: Eq t => (Term t) -> (Term t) -> State (TermEnv t) Bool
occursInTerm a b | a == b = return True
occursInTerm a (Term t l) = do 
  l' <- (mapM (occursInTerm a) l)
  foldrM monadicOr False l'
occursInTerm _ _          = return False

occursInTermTrans :: Eq t => Monad m => (Term t) -> (Term t) -> StateT (TermEnv t) m Bool
occursInTermTrans a b | a == b = return True
occursInTermTrans a (Term t l) = do 
  l' <- (mapM (occursInTermTrans a) l)
  foldrM monadicOr False l'
occursInTermTrans _ _          = return False

-- |For terms a, b returns True iff a occurs somewhere in b, ignoring ref nodes
occursInTermIgnoreRefs :: Eq t => (Term t) -> (Term t) -> Bool
occursInTermIgnoreRefs a b | a == b = True
occursInTermIgnoreRefs a (Term t l) = foldr (||) False $ map (occursInTermIgnoreRefs a) l
occursInTermIgnoreRefs _ _          = False

newTermVarIdxFromState :: Monad a => StateT (IdxSet) a Idx
newTermVarIdxFromState = do
  idxset <- get
  let (nid,nidxset) = getnid dtvids idxset
  modify (\_ -> nidxset)
  return nid

-- |Returns a var with a new idx
newTermVarFromState :: Monad a => StateT (IdxSet) a (Term t)
newTermVarFromState = do idx <- newTermVarIdxFromState ; return (Var idx)

-- |Creates a new term var and binds it in the state env
bindNewTermVarInState :: Monad a => Idx -> StateT (TermEnv t) (StateT (IdxSet) a) (Term t)
bindNewTermVarInState i = do
  nvar <- lift newTermVarFromState
  bindTermInState (Scheme [] nvar) i
  return nvar  

-- |A function that generates a new Idx
type GenerateIdFunction = State IdxSet Idx

-- |Picks freshs var ids for all vars, whilst maintaining equalities within the term
renewTermVarIdsMemorized :: (Term t) -> StateT (State IdxSet Idx, [(Idx, Idx)]) (State IdxSet) (Term t)
renewTermVarIdsMemorized term = case term of
  (Term t l) -> (Term t) `fmap` mapM renewTermVarIdsMemorized l
  (Var x) -> do
    (genid, mp) <- get
    case lookup x mp of
      Just y  -> return (Var y)   
      Nothing -> do y <- lift genid
                    modify (\(gf,mp') -> (gf, (x,y):mp'))
                    return (Var y) 
  _ -> return term

-- |Picks fresh var ids for all vars, returning the new term with vars substituted, and
-- |the list of substitutions it applied
renewTermVarIdsWithSubs :: Monad a => (Term t) -> StateT IdxSet a (Term t, [Subst (Term t)])
renewTermVarIdsWithSubs term = do
  idxset <- get
  let ((t', (_, sublist)), idxset') = runState (runStateT (renewTermVarIdsMemorized term) (newid dtvids, [])) idxset
  modify (\i -> idxset')
  let subs = map (\(a,b) -> (Var a) :|-> (Var b)) sublist
  return (t', subs)

renewTermVarIds :: Monad a => Term t -> StateT IdxSet a (Term t)
renewTermVarIds t = do 
  idxset <- get
  let (t',idxset') = runState (evalStateT (renewTermVarIdsMemorized t) (newid dtvids, [])) idxset 
  modify (\i -> idxset')
  return t'

-- |Picks fresh var ids for vars in each term in the environment such that
-- |no variable is used in more than one term in the environment, but 
-- |variable patterns are preserved for each term.
--renewTermVarsInEnv :: Monad a => TermEnv t -> StateT IdxSet a (TermEnv t)
--renewTermVarsInEnv env = do
--  env' <- mapM (\(i,t) -> do t' <- renewTermVarIds t ; return (i,t')) env
--  return env'

--renewTermVarIds :: Term t -> State IdxSet (Term t)
--renewTermVarIds t = evalStateT (renewTermVarIdsMemorized t) (newid dvids, []) 

data Subst t = t :|-> t
  deriving (Eq, Show)

-- |Apply the function cumulatively to the argument 
-- |once for every argument in the subst list
-- |in order of list left to right.
forAllSubs :: (Subst t -> a -> a) -> [Subst t] -> a -> a
forAllSubs f (h:r) a = forAllSubs f r (f h a)
forAllSubs _ []    a = a

subInTerm :: Eq t => Subst (Term t) -> Term t -> Term t
subInTerm sb term = 
  let (x :|-> s) = sb in
  if x == term then s
  else case term of 
    Term t l -> Term t $ map (subInTerm sb) l
    _ -> term

-- |Substitutes all occurances in term, returning the term in the left if it was affected
-- |or in the right if it was not
subInTermReturnAffected :: Eq t => Subst (Term t) -> Term t -> Either (Term t) (Term t)
subInTermReturnAffected sb term =
  let (x :|-> s) = sb in
  if x == term then Left s
  else case term of
    Term t l -> 
      let m = map (subInTermReturnAffected sb) l in
      let (ll,rl) = partitionEithers m in 
        case ll of 
          [] -> Right (Term t ll)
          _  -> Left (Term t (map (either id id) m))
    _ -> Right term

-- |If the substitution would substitute a bound variable, ignore it.
-- |This is safe as in the unlikely event that a substitution involves the same
-- |variable id as a qualified variable, the fact that its not free ensures it
-- |was never supposed to be substituted as it should have no external visibility.
subInScheme :: Eq t => Subst (Term t) -> Scheme t -> Scheme t
subInScheme sub (Scheme [] t) = (Scheme [] $ subInTerm sub t)
subInScheme sub scm = if elem a l then scm else (Scheme l $ subInTerm sub t)  
  where ((Scheme l t), ((Var a) :|-> b)) = (scm, sub)


data Constr t = t :=: t
  deriving (Eq, Show)

applyVarSubstsToConstr :: VarsIn t => VarSubsts t -> Constr t -> Constr t
applyVarSubstsToConstr subs (a :=: b) = (applyVarSubsts subs a) :=: (applyVarSubsts subs b)
 
type WeightedConstr t = (Constr t, Int)

subInConstr :: Eq t => Subst (Term t) -> Constr (Term t) -> Constr (Term t)
subInConstr s (a :=: b) = (subInTerm s a) :=: (subInTerm s b) 

occursInConstr :: Eq t => (Term t) -> (Constr (Term t)) -> State (TermEnv t) Bool
occursInConstr t (a :=: b) = do
  inA <- occursInTerm t a
  if inA 
    then return True
    else do
      inB <- occursInTerm t b
      return inB

-- |A function that tries to expand a constraint, returning left with the expansion list
-- |if it could, or right if it failed.
type UnifierExtension t = TermEnv t -> Constr (Term t) -> Either [Constr (Term t)] (Constr (Term t)) 

-- |Always returns failure for the constraint
defaultUnifierExtension :: UnifierExtension t
defaultUnifierExtension env c = (Right c)

-- |Unify the set of constraints given the term environment used to resolve Ref terms, returns either
-- |the set of substitutions in the left, or the constraint it failed on in the right.
monadicUnify :: Eq t => Show t => [Constr (Term t)] -> StateT (UnifierExtension t) (State (TermEnv t)) (Either [(Subst (Term t))] (Constr (Term t)))
monadicUnify [] = return (Left []) -- end of list
monadicUnify (c:r) = do 
  env <- lift get
  case trcUnifyCon c of
    -- term equality
    (Term t l :=: Term t' l') | t == t' && length l == length l' -> 
      monadicUnify ((map (\(a,b)->(a :=: b)) $ zip l l') ++ r)
    -- lookup references into the environment
--    (Ref i :=: t) -> monadicUnify (((lookupTerm env i) :=: t):r)
--    (s :=: Ref i) -> monadicUnify ((s :=: (lookupTerm env i)):r)
    -- variables
    (Var a :=: Var a') | a == a' -> monadicUnify r 
    (s :=: (Var i)) -> 
      let x = (Var i) in
      if s == x then monadicUnify r 
      else do 
        occIn <- lift (occursInTerm x s)
        if occIn 
          then error $ "circular constraint " ++ (show c) ++ 
                              " remaining " ++ (show r) -- return (Right (s :=: x))
          else do 
            let sub = (x :|-> s)
            rec <- (monadicUnify (map (subInConstr sub) r))
            case rec of 
              Left a -> return (Left (sub:a))
              Right a -> return (Right a) 
    ((Var i) :=: t) -> 
      let x = (Var i) in
      if t == x then monadicUnify r 
      else do
        occIn <- lift (occursInTerm x t) 
        if occIn 
          then error $ "circular constraint " ++ (show c) ++ 
                              " remaining " ++ (show r) -- return (Right (x :=: t))
          else do
            let sub = (x :|-> t)
            rec <- monadicUnify (map (subInConstr sub) r) 
            case rec of 
              Left a -> return (Left (sub:a))
              Right a -> return (Right a)
    -- pass to unifier extension function
    _ -> do 
         exF <- get
         case (exF env c) of
           (Left cl) -> monadicUnify (cl ++ r)
           (Right failC) -> return (Right failC)

-- |Unifies a set of constraints where a unifier extension function can be used
unifyConstraintsEx :: Eq t => Show t => 
  [Constr (Term t)] -> 
  TermEnv t -> 
  UnifierExtension t -> 
    Either [(Subst (Term t))] (Constr (Term t))
unifyConstraintsEx cl env exF = evalState (evalStateT (monadicUnify cl) exF) env

-- |Unifies a set of constraints
unifyConstraints :: Eq t => Show t => 
  [Constr (Term t)] -> 
  TermEnv t -> 
    Either [(Subst (Term t))] (Constr (Term t))
unifyConstraints cl env = unifyConstraintsEx cl env defaultUnifierExtension

-- |The type for a unifier extension that is monadic
type MonadicUnifierExtension t m = 
  TermEnv t -> 
  Constr (Term t) -> 
  m (Either [Constr (Term t)] (Constr (Term t)))

-- |The type of a unifier extention that only uses the Identity monadic
type IdentityUnifierExtension t = MonadicUnifierExtension t Identity

-- |Default monadic unifier extension just fails of the constraint
defaultMonadicUnifierExtension :: Monad m => MonadicUnifierExtension t m
defaultMonadicUnifierExtension env c = return $ Right c

-- |The unify function that permits nesting of monads
monadicUnifyTrans :: Eq t => Show t => Monad m => 
  [Constr (Term t)] -> 
  StateT (MonadicUnifierExtension t m) 
    (StateT (TermEnv t) m) 
    (Either [(Subst (Term t))] (Constr (Term t)))
monadicUnifyTrans [] = return (Left []) -- end of list
monadicUnifyTrans (c:r) = do 
  env <- lift get
  case trcUnifyCon c of
    -- term equality
    (Term t l :=: Term t' l') | t == t' && length l == length l' -> 
      monadicUnifyTrans ((map (\(a,b)->(a :=: b)) $ zip l l') ++ r)
    -- lookup references into the environment
    --(Ref i :=: t) -> monadicUnifyTrans (((lookupTerm env i) :=: t):r)
    --(s :=: Ref i) -> monadicUnifyTrans ((s :=: (lookupTerm env i)):r)
    -- variables
    (Var a :=: Var a') | a == a' -> monadicUnifyTrans r 
    (s :=: (Var i)) -> 
      let x = (Var i) in
      if s == x then monadicUnifyTrans r 
      else do 
        occIn <- lift (occursInTermTrans x s)
        if occIn 
          then error ("circular constraint " ++ (show c) ++ 
                      " remaining " ++ (show r)) -- $ return (Right (s :=: x))
          else do 
            let sub = (x :|-> s)
            rec <- (monadicUnifyTrans (map (subInConstr sub) r))
            case rec of 
              Left a -> return (Left (sub:a))
              Right a -> return (Right a) 
    ((Var i) :=: t) -> 
      let x = (Var i) in
      if t == x then monadicUnifyTrans r 
      else do
        occIn <- lift (occursInTermTrans x t) 
        if occIn 
          then error ("circular constraint " ++ (show c) ++ 
                      " remaining " ++ (show r)) -- $ return (Right (x :=: t))
          else do
            let sub = (x :|-> t)
            rec <- monadicUnifyTrans (map (subInConstr sub) r) 
            case rec of 
              Left a -> return (Left (sub:a))
              Right a -> return (Right a)
    -- pass to unifier extension function
    _ -> do 
         exF <- get
         ret <- lift $ lift $ exF env c
         case ret of
           (Left cl) -> monadicUnifyTrans (cl ++ r)
           (Right failC) -> return (Right failC)

-- |Unifies a set of constraints where a monad can be passed to the extension function
unifyConstraintsEx2 :: (Eq t, Show t, Monad m) =>
  [Constr (Term t)] -> 
  TermEnv t -> 
  MonadicUnifierExtension t m -> 
    m (Either [(Subst (Term t))] (Constr (Term t)))
unifyConstraintsEx2 cl env exF = evalStateT (evalStateT (monadicUnifyTrans cl) exF) env

-- |The unify function that permits nesting of monads, and takes a set of terminal
-- |var ids which should not be expanded. This allows unification to ke place
-- |for a subexpression rather than the entire program.
monadicUnifyTrans2 :: Eq t => Show t => Monad m => 
  [Constr (Term t)] -> 
  StateT (MonadicUnifierExtension t m, Set Idx) 
    (StateT (TermEnv t) m) 
    (Either [(Subst (Term t))] (Constr (Term t)))
monadicUnifyTrans2 [] = return (Left []) -- end of list
monadicUnifyTrans2 (c:r) = do
  (exF, termIds) <- get 
  env <- lift get
  case trcUnifyCon c of
    -- term equality
    (Term t l :=: Term t' l') | t == t' && length l == length l' -> 
      monadicUnifyTrans2 ((map (\(a,b)->(a :=: b)) $ zip l l') ++ r)
    -- lookup references into the environment
    --(Ref i :=: t) -> monadicUnifyTrans2 (((lookupTerm env i) :=: t):r)
    --(s :=: Ref i) -> monadicUnifyTrans2 ((s :=: (lookupTerm env i)):r)
    -- variables (where the var being sub'ed isn't a terminal)
    (Var a :=: Var a') | a == a' -> monadicUnifyTrans2 r 
    (s :=: (Var i)) | not (member i termIds) -> 
      let x = (Var i) in
      if s == x then monadicUnifyTrans2 r 
      else do 
        occIn <- lift (occursInTermTrans x s)
        if occIn 
          then error $ "circular constraint " ++ (show c) ++ 
                              " remaining " ++ (show r) -- return (Right (s :=: x))
          else do 
            let sub = (x :|-> s)
            rec <- (monadicUnifyTrans2 (map (subInConstr sub) r))
            case rec of 
              Left a -> return (Left (sub:a))
              Right a -> return (Right a) 
    ((Var i) :=: t) | not (member i termIds) -> 
      let x = (Var i) in
      if t == x then monadicUnifyTrans2 r 
      else do
        occIn <- lift (occursInTermTrans x t) 
        if occIn 
          then error $ "circular constraint " ++ (show c) ++ 
                              " remaining " ++ (show r) -- return (Right (x :=: t))
          else do
            let sub = (x :|-> t)
            rec <- monadicUnifyTrans2 (map (subInConstr sub) r) 
            case rec of 
              Left a -> return (Left (sub:a))
              Right a -> return (Right a)
    -- variables (where one or both of the vars is a terminal)
    (Var a :=: Var a') -> monadicUnifyTrans2 r -- both terminals
    (s :=: (Var i))    -> monadicUnifyTrans2 r -- var i terminal, s some other term
    ((Var i) :=: t)    -> monadicUnifyTrans2 r -- var i terminal, t some other term
    -- pass to unifier extension function
    _ -> do 
         ret <- lift $ lift $ exF env c
         case ret of
           (Left cl) -> monadicUnifyTrans2 (cl ++ r)
           (Right failC) -> return (Right failC)

-- |Unifies a set of constraints where a monad can be passed to the extension function,
-- |and where a set of "terminal var ids" that won't be simplified during unification
-- |can be passed to the constraint solver.
unifyConstraintsEx3 :: (Eq t, Show t, Monad m) =>
  [Constr (Term t)] -> 
  TermEnv t -> 
  MonadicUnifierExtension t m ->
  Set Idx ->  
    m (Either [(Subst (Term t))] (Constr (Term t)))
unifyConstraintsEx3 cl env exF termIds = 
  evalStateT (evalStateT (monadicUnifyTrans2 cl) (exF,termIds)) env

-- |Base class for tokens for term languages with function types and tuples
data FunctionToken t = 
    FunTok 
  | TupTok
  | Tok t
    deriving (Eq, Ord)

type FuncTokTerm t = Term (FunctionToken t)

isFuncTerm :: Term (FunctionToken t) -> Bool
isFuncTerm (Term FunTok _) = True
isFuncTerm _ = False

instance Show t => Show (FunctionToken t) where
  show (FunTok) = "Fun"
  show (TupTok) = "Tup"
  show (Tok t) = (show t)

-- |Pretty print function term
showFunctionTerm :: Show t => Term (FunctionToken t) -> String
showFunctionTerm (Term FunTok (a:b:_)) = funLParen ++ (show a) ++ " -> " ++ (show b) ++ funRParen
showFunctionTerm (Term TupTok l) = "(" ++ (delimList ", " $ map showFunctionTerm l) ++ ")"
showFunctionTerm t = (show t)

-- |Pretty print function scheme
showFunctionScheme :: Show t => Scheme (FunctionToken t) -> String
showFunctionScheme (Scheme [] term) = showFunctionTerm term
showFunctionScheme (Scheme vars term) = "(forall " ++ 
  (delimList "," $ map (\i -> ("V" ++ show i)) vars) ++
  " => " ++ (showFunctionTerm term) ++ ")"

-- |Type of a function that performs some var substitution on a FuncTokTerm
--type RenewFuncVarIdsFunction a t = Monad a =>
--  GenerateIdFunction ->
--  FuncTokTerm t ->
--  StateT [(Idx, Idx)] (StateT IdxSet a) (FuncTokTerm t)

-- |Renews terms, whenever it comes across a new var it checks to see
-- |if a there already exists a substitution for it, and if not creates a replacement
--renewFunVarIdsInTermMemorize :: (RenewFuncVarIdsFunction t) -> RenewFuncVarIdsFunction t
--renewFunVarIdsInTermMemorize funf genf term = case term of
--  (Term FunTok [dom, ran]) -> funf genf term
--  _ -> do return undefined

-- |Renews terms, whenever comes across a var that exists in the substituion list
-- |it substitutes it, otherwise it leaves it alone
--renewFunVarIdsInTermLookup :: (RenewFuncVarIdsFunction t) -> RenewFuncVarIdsFunction t
--renewFunVarIdsInTermLookup funf genf term = case term of
--  (Term FunTok [dom, ran]) -> funf genf term
--  _ -> do return undefined  --(union [])

-- |A stack of term environments
type TermEnvStack t = [TermEnv t]

emptyTermEnvStack :: TermEnvStack t
emptyTermEnvStack = []

pushTermEnv :: TermEnv t -> TermEnvStack t -> TermEnvStack t
pushTermEnv item stack = item:stack

pushTermEnvInState :: Monad a => TermEnv t -> StateT (TermEnvStack t) a (TermEnv t)
pushTermEnvInState env = do
  modify (pushTermEnv env)
  return env

popTermEnv :: TermEnvStack t -> TermEnvStack t
popTermEnv (item:stack) = stack
popTermEnv [] = error "Cannot pop an item from an empty TermEnvStack"

popTermEnvInState :: Monad a => StateT (TermEnvStack t) a (TermEnvStack t)
popTermEnvInState = do
  modify popTermEnv
  stack <- get
  return stack

peekTermEnv :: TermEnvStack t -> TermEnv t
peekTermEnv (top:rest) = top
peekTermEnv [] = error "Cannot peek at an item in an empty TermEnvStack"

peekTermEnvInState :: Monad a => StateT (TermEnvStack t) a (TermEnv t)
peekTermEnvInState = do
  stack <- get
  return (peekTermEnv stack)

termEnvStackLength :: TermEnvStack t -> Int
termEnvStackLength stack = length stack

lookupTermFromStack :: Show t => TermEnvStack t -> Idx -> Maybe (Term t)
lookupTermFromStack (top:stack) i = case lookupTermMaybe top i of
  Just (Scheme [] t) -> Just t
  Nothing -> lookupTermFromStack stack i
  t -> error $ "Term stacks should only contain schemes with no qualifiers " ++ (show t) ++
               " from " ++ (show (top:stack))
lookupTermFromStack [] i = Nothing

lookupTermFromStackInState :: (Show t, Monad a) => 
  Idx -> 
  StateT (TermEnvStack t) a (Maybe (Term t))
lookupTermFromStackInState i = do
  stack <- get
  return (lookupTermFromStack stack i)

lookupTermFromHeadInState :: (Show t, Monad a) =>
  Idx -> 
  StateT (TermEnvStack t) a (Maybe (Term t))
lookupTermFromHeadInState i = do
  stack <- get
  case stack of
    (head:rest) -> case (lookupTermMaybe head i) of
      Just (Scheme [] t) -> return (Just t)
      Nothing -> return Nothing 
      r  -> error $ "Term stacks should only contain schemes with no qualifiers " ++
                    (show r) ++ " from " ++ (show stack)
    [] -> error "Cannot lookup term from empty stack" 

addTermToStack :: Term t -> Idx -> TermEnvStack t -> TermEnvStack t
addTermToStack term i (top:rest) = (addTermToEnv top (Scheme [] term) i):rest
addTermToStack term i [] = addTermToStack term i (pushTermEnv emptyTermEnv [])

-- |Adds a term binding to the TermEnvStack in the state
addTermToStackInState :: Monad a => Term t -> Idx -> StateT (TermEnvStack t) a ()
addTermToStackInState term i = do
  modify (\stack -> addTermToStack term i stack)
  return ()

schemeModifier :: (Term t -> Term t) -> Scheme t -> Scheme t
schemeModifier f (Scheme vars term) = (Scheme vars $ f term) 

-- |Changes a term in one of the stack frames
modifyTermInStack :: (Term t -> Term t) -> Idx -> TermEnvStack t -> (Maybe (TermEnvStack t))
modifyTermInStack _ _ [] = Nothing
modifyTermInStack f id (top:rest) = case findAndModify (foundKey id) (modifyValue $ schemeModifier f) top of
  Just top' -> Just (top':rest)
  Nothing -> case modifyTermInStack f id rest of 
               Just list -> Just (top:list)
               Nothing -> Nothing

-- |Changes term in stack frame or raises error if no term with the given id exists
modifyTermInStackOrError :: Show t => (Term t -> Term t) -> Idx -> TermEnvStack t -> TermEnvStack t
modifyTermInStackOrError modF id stack = case modifyTermInStack modF id stack of
  Just stack' -> stack'
  Nothing -> error ("Var " ++ (show id) ++ " not declared in TermEnvStack " ++ (show stack))

-- |Changes a term in one of the stack frames in the state, or if no var with that id exists
-- |in the stack, raises an error
modifyTermInStackState :: (Monad a, Show t) => (Term t -> Term t) -> Idx -> StateT (TermEnvStack t) a ()
modifyTermInStackState modF id = do
  modify (modifyTermInStackOrError modF id)
  return ()

--class Experm t where
--  fun :: t -> t -> t
--  tup :: [t] -> t

--data Term t =
 --   Tok t
--  | Fun (Term t) (Term t)
--  | Tup [Term t]
--  | Var Idx
--  | Ref Idx
--  deriving (Eq)

--instance Show t => Show (Term t) where
--- show (Tok t) = show t
--  show (Fun a b) = (show a) ++ " -> " ++ (show b)
--  show (Tup l) = "(" ++ (delimList ", " $ map show l) ++ ")"
--  show (Var i) = "V" ++ (show i)
--  show (Ref i) = "r" ++ (show i)



--data MPIToken =
--    Fun
--  | Tup 
--  | Dist
--  | Part
--  | Mirr
--  | Sing
--  | Grid
--  | FunCmpSeq
--  | FunCmpPair
--  | Zero
--  | Succ
--  | Lit Int
--    deriving (Show, Eq)

--newtype MPITerm = MPITerm (Term MPIToken)

--instance ExpTerm MPITerm where
--  fun a b = Term Fun [a, b]
--  tup l   = Term Tup l

--mpiD loc alg = Term Dist [loc, alg]
--parD kf pf = Term Part [kf, pf]

--mpiParD = Term Fun [mpiD (Var 1) (parD (Var 2) (Var 3)), mpiD (Var 1) (parD (Var 2) (Var 3))]
