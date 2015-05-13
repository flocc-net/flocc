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
module Compiler.Front.Common where

import Compiler.Front.Indices (IdxSet)
-- import GlobalEnv (globalNames)

import Control.Monad.State.Strict
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Data.Map (lookup, size, intersection, union, empty, insert, adjust, member, toList, toAscList, fromAscList)
import qualified Data.IntMap.Strict as IM
import Data.Set (Set, union, intersection)
import qualified Data.Set (null, empty, delete, member, insert)
import Data.Char (toUpper, toLower)
import Data.List (intersect, intersperse)
import Control.Exception (SomeException)
import Control.Monad.Catch (catch, MonadCatch)
import Control.Concurrent (threadDelay)
import qualified Data.ByteString.Char8 as BS
import Data.Either
import System.IO (hPutStr, stderr)
import Data.Typeable

import Debug.Trace (trace)

debug = False

putStrE = hPutStr stderr

class ShowP a where
  showP :: a -> String

instance ShowP Int where
  showP i = show i

instance ShowP Char where
  showP c = show c

instance ShowP a => ShowP (Maybe a) where
  showP (Just a) = "Just " ++ (showP a)
  showP Nothing = "Nothing"

instance (ShowP a, ShowP b) => ShowP (Either a b) where
  showP ab = case ab of
    Left a -> "Left " ++ (showP a)
    Right b -> "Right " ++ (showP b)

instance (ShowP a, ShowP b) => ShowP (a, b) where
  showP (a,b) = "(" ++ (showP a) ++ ", " ++ (showP b) ++ ")"

instance (ShowP a, ShowP b, ShowP c) => ShowP (a, b, c) where
  showP (a,b,c) = "(" ++ (showP a) ++ ", " ++ (showP b) ++ ", " ++ (showP c) ++ ")"

-- |isString s. Returns true if this value is a string.
--isString :: (Typeable a) => a -> Bool
--isString n = typeOf n == typeOf "abc"

instance (ShowP a, Show a) => ShowP [a] where
  showP l = {-if isString l then show l else-} concat $ map (++"\n") $ map showP l

instance (ShowP a) => ShowP (IM.IntMap a) where
  showP mp = concat $ map (++"\n") $ map showP $ IM.toList mp

instance (ShowP k, ShowP v) => ShowP (Map k v) where
  showP mp = concat $ map (++"\n") $ map showP $ Data.Map.toList mp

class FunctorM f where
  fmapM :: Monad m => (a -> m b) -> f a -> m (f b)

instance FunctorM [] where
  fmapM f l = mapM f l

-- |Class for types that can be mapped over using a 
-- |monadic transformation function.
class Mappable a where
  monadicMap :: Monad m => (a -> m a) -> a -> m a

-- |Class for types that carry a count.
class Counted a where
  getCount :: a -> Int
  setCount :: Int -> a -> a

-- |Increments the count of a counted value by 1.
incCount :: Counted a => a -> a
incCount a = setCount ((getCount a) + 1) a

readFileForce :: String -> IO String
readFileForce name = (BS.readFile name) >>= (return . BS.unpack)

writeFileForce :: String -> String -> IO ()
writeFileForce name str = BS.writeFile name (BS.pack str) 

catchRetry :: MonadCatch m => (m a) -> Int -> m (Either a SomeException)
catchRetry action retriesRem = do 
  catch (action >>= (return . Left)) (\e -> if retriesRem > 0 then catchRetry action (retriesRem-1) else return $ Right (e :: SomeException))

catchRetry2 :: MonadCatch m => (m a) -> Int -> m a
catchRetry2 action retriesRem = do 
  catch action (\e -> if retriesRem > 0 then catchRetry2 action (retriesRem-1) else error $ "catchRetry2:" ++ (show (e :: SomeException)))

catchRetryIO :: (IO a) -> Int -> IO a
catchRetryIO action retriesRem = do 
  catch action (\e -> if retriesRem > 0 then do threadDelay 100000 ; catchRetryIO action (retriesRem-1) else error $ "catchRetryIO:" ++ (show (e :: SomeException)))

catchRead :: (Show a, Read a) => String -> String -> a
catchRead msg str = case reads str of
  [(v, s)] -> v
  other -> error $ "catchRead: " ++ msg ++ ": error reading \"" ++ str ++ "\". reads returned:\n" ++ (show other)
  
readMaybe :: (Show a, Read a) => String -> Maybe a
readMaybe str = case reads str of
  [(v, s)] -> Just v
  other -> Nothing

dotToScore = \c -> if c == '.' then '_' else c

scoreToDot = \c -> if c == '_' then '.' else c

-- |Lifts a function to work on a pair
liftPair :: (a -> b) -> (a, a) -> (b, b)
liftPair f (a1, a2) = (f a1, f a2)

-- |Returns all but the last n elements of a list
droplast :: Int -> [a] -> [a]
droplast n a | n < (length a) = take t a where t = (length a) - n
droplast 0 a = a
droplast _ [] = []
droplast _ _ = [] -- if ask to drop more elements than there are

-- |Pads the list with copies of the second argument until it is at least the length
-- |given by the fourth argument. The third argument should be the length 
-- |of the input list. 
prepad :: [a] -> a -> Int -> Int -> [a]
prepad a c cl pl | cl < pl = prepad (c:a) c (cl+1) pl
prepad a c cl pl | cl >= pl = a

indent :: a -> Int -> [a] -> [a]
indent c 0 s = s
indent c l s = indent c (l-1) (c:s)

-- |toUpperFst makes first character of string upper case and rest lower case
toUpperFst :: String -> String
toUpperFst []    = []
toUpperFst (f:r) = (toUpper f):(map toLower r) 

-- |underscoresToUppers takes a string with underscores and removes them
-- |making the next character uppercase.
underscoresToUppers :: String -> String
underscoresToUppers [] = []
underscoresToUppers (c1:[]) = [c1]
underscoresToUppers (c1:r) = if c1 == '_' then toUpperFst $ underscoresToUppers r else c1:(underscoresToUppers r)

-- |Takes either a left or a right function, and either a left
-- |or a right value, and applies the function to the value, 
-- |returning the result in the left if both the function, 
-- |and the value were left, and right otherwise.
lr :: (Either (b -> a) (b -> a)) -> Either b b -> Either a a
lr (Left f) (Left t) = Left (f t)
lr (Right f) (Right t) = Right (f t)
lr (Left f) (Right t) = Right (f t)
lr (Right f) (Left t) = Right (f t)

-- |Takes a function and either a left or a right term
-- |and returns the result of applying that function to
-- |the term still wrapped in the appropriate left or right
-- |of its parent
lr0 :: (b -> a) -> Either b b -> Either a a
lr0 f (Left t) = Left (f t)
lr0 f (Right t) = Right (f t)

-- |Idx numbers 
eids :: Int
eids = 0 -- expression ids
vids :: Int
vids = 1 -- var ids
rndnums :: Int
rndnums = 2 -- random nums
--dvids :: Int
--dvids = 3 -- distributution var ids
dtvids :: Int
dtvids = 4  -- data type var ids
graphClusterIDs :: Int
graphClusterIDs = 5
codeVarIDs :: Int
codeVarIDs = 6

numIdxSetCategories = 7

-- TODO: This will fail as the number of names grows!!!!
initIdxSet numGlobNames = [numGlobNames + 1 | i <- [0..6] ]

-- |Runs an idx state computation
evalIdxState :: Int -> (State IdxSet a) -> a
evalIdxState numGlobNames m = evalState m (initIdxSet numGlobNames)
 
evalIdxStateT :: Monad m => Int -> (StateT IdxSet m a) -> m a
evalIdxStateT numGlobNames m = evalStateT m (initIdxSet numGlobNames)

runIdxStateT :: Monad m => Int -> (StateT IdxSet m a) -> (m (a, IdxSet))
runIdxStateT numGlobNames m = runStateT m (initIdxSet numGlobNames)

showList :: Show a => [a] -> String
showList l = concat $ map (\a -> (show a) ++ "\n") l

delimList :: String -> [String] -> String
delimList d l = droplast (length d) (concat $ map (\a -> a ++ d) l)

-- |Shows a lookup table, nicely padded
showLookupTable :: Show a => Show b => Int -> [(a,b)] -> String
showLookupTable n l = concat $ map (\(a,b) ->
  let astr = (show a) in 
    (prepad astr ' ' (length astr) n) ++ ": " ++ (show b) ++ "\n"
  ) l

-- |Left and right parentheses for function types
funLParen = "["
funRParen = "]"

-- |Searches the list for an item satisfying the predicate, and modifie
-- |the first occurance using the function.
findAndModify :: (a -> Bool) -> (a -> a) -> [a] -> (Maybe [a])
findAndModify _ _ [] = Nothing
findAndModify pred modF (head:rest) = case (pred head) of
  True  -> Just ((modF head):rest)
  False -> case (findAndModify pred modF rest) of
             Just l -> Just (head:l)
             Nothing -> Nothing

-- |Searches the list for an item satisfying the predicate, and modifie
-- |all occurances using the function.
findAndModifyAll :: (a -> Bool) -> (a -> a) -> [a] -> [a]
findAndModifyAll _ _ [] = []
findAndModifyAll pred modF (head:rest) = case (pred head) of
  True  -> (modF head):(findAndModifyAll pred modF rest)
  False -> head:(findAndModifyAll pred modF rest)

-- |Searches the list for an item satisfying the predicate, and replaces the 
-- |first occurance with the value given in the second argument.
findAndReplace :: (a -> Bool) -> a -> [a] -> (Maybe [a])
findAndReplace pred val list = findAndModify pred (\a -> val) list

-- |Searches the list for an item satisfying the predicate, and replaces the 
-- |first occurance with the value given in the second argument.
findAndReplaceAll :: (a -> Bool) -> a -> [a] -> [a]
findAndReplaceAll pred val list = findAndModifyAll pred (\a -> val) list

-- |Simple boolean predicate for finding a key in a key value list
foundKey :: Eq k => k -> (k,v) -> Bool
foundKey searchKey (currentKey, v) = searchKey == currentKey

-- |Simple function that modifies the second element in a pair using a function
modifyValue :: (v -> v) -> (k,v) -> (k,v)
modifyValue modF (k,v) = (k,(modF v))

-- |Debug function for tracing 
tracer :: Show a => a -> a
tracer a = trace ((show a) ++ "\n") $ a

-- |Debug function for tracing, that can be curried with a label string
tracerEx :: Show a => String -> a -> a
tracerEx s a = trace (s ++ (show a) ++ "\n") $ a

-- |Debug function for tracing, that takes a label string and a custom show function
tracerEx2 :: String -> (a -> String) -> a -> a
tracerEx2 s f a = trace (s ++ (f a) ++ "\n") $ a

-- |Debug function for tracing, that takes a label string, show function, and object to
-- |display
tracerEx3 :: String -> (a -> String) -> a -> b -> b
tracerEx3 s f a b = trace (s ++ (f a) ++ "\n") $ b

-- |Flips an associative list so that the keys become value's and 
-- |visa versa.
flipAssocList :: [(a, b)] -> [(b, a)]
flipAssocList l = let (al, bl) = unzip l in zip bl al

-- |Implementation or exclusive or
xor :: Bool -> Bool -> Bool
xor True a = not a
xor False a = a

isLeft :: Either a b -> Bool
isLeft (Left _) = True
isLeft _ = False

-- |maybeError takes a string message and a maybe value
-- |returning the enclosed value when its a Just
-- |or returning an error with the message otherwise
maybeError :: String -> Maybe a -> a
maybeError msg mb = case mb of
  Just a  -> a
  Nothing -> error msg

-- |maybeList takes a maybe value and returns
-- |either a singleton, or empty list depending on the value
maybeList :: Maybe a -> [a]
maybeList m = case m of
  Just a -> [a]
  Nothing -> []

-- |fromMaybePair takes a pair of maybe values and if
-- |both are Just return a single maybe holding the pair
fromMaybePair :: (Maybe a, Maybe b) -> Maybe (a, b)
fromMaybePair pr = case pr of 
  (Just a, Just b) -> Just (a, b)
  _                -> Nothing

-- |fromIntMap im. Returns a Data.Map.Strict map from an 
-- |IntMap.
fromIntMap :: IM.IntMap t -> Map Int t
fromIntMap m = Data.Map.fromAscList $ IM.toAscList m 

-- |toIntMap m. Returns a Data.IntMap.Strict map from a
-- |Data.Map.Strict.
toIntMap :: Map Int t -> IM.IntMap t
toIntMap m = IM.fromAscList $ Data.Map.toAscList m 

-- |lookupOrValue takes a key, map, and value and looks
-- |that key up in the map, returning the associated value if it exists
-- |or the value given otherwise.
lookupOrValue :: (Ord k) => k -> Map k v -> v -> v
lookupOrValue key arr v2 = case Data.Map.lookup key arr of
  Just v1 -> v1
  Nothing -> v2

-- |lookupIntOrValue takes a key, map, and value and looks
-- |that key up in the map, returning the associated value if it exists
-- |or the value given otherwise.
lookupIntOrValue :: Int -> IM.IntMap v -> v -> v
lookupIntOrValue key arr v2 = case IM.lookup key arr of
  Just v1 -> v1
  Nothing -> v2

-- |lookupOrError takes an error message string, key and a map,
-- |and tries to lookup from the map, returning the element if
-- |it exists, or throwing an error with the message otherwise 
lookupOrError :: (Show k, Ord k) => String -> k -> Map k v -> v
lookupOrError errorMsg key arr = case Data.Map.lookup key arr of
  Just value -> value
  Nothing -> error $ "Map lookup error: " ++ errorMsg ++ " " ++ (show key)

-- |lookupIntOrError takes an error message string, key and an intmap,
-- |and tries to lookup from the map, returning the element if
-- |it exists, or throwing an error with the message otherwise 
lookupIntOrError :: String -> Int -> IM.IntMap v -> v
lookupIntOrError errorMsg key arr = case IM.lookup key arr of
  Just value -> value
  Nothing -> error $ "IntMap lookup error: " ++ errorMsg ++ " " ++ (show key)

lookupAssocOrValue :: (Eq k, Show k) => a -> k -> [(k, a)] -> a
lookupAssocOrValue val key env = case lookup key env of
  Just a  -> a
  Nothing -> val

-- |replaceAssocVal takes an error message string, key value and assoc
-- |array and returns the list with the first occurence of the key replaced
-- |with the value, or throws an error if that key does not exist in the list.
replaceAssocVal :: Eq a => String -> a -> v -> [(a,v)] -> [(a,v)]
replaceAssocVal msg key val list = case list of
  [] -> error msg
  ((a,b):rest) -> if a == key then (a,val):rest else (a,b):(replaceAssocVal msg key val rest)

-- |unionsCheckDisjoint takes a list of sets and throws the error message
-- |if they are not disjoint, or returns the unions set otherwise.
unionsCheckDisjoint :: (Ord a, Show a) => String -> [Set a] -> Set a
unionsCheckDisjoint _ [] = error "unionsCheckDisjoint: no sets"
unionsCheckDisjoint _ (h:[]) = h
unionsCheckDisjoint msg (h:r) = foldl (\acc -> \s -> if Data.Set.null (acc `intersection` s) then acc `union` s else error $ msg ++ (show $ h:r)  ) h r

-- |mapUnionCheckDisjoint checks thats is operands are disjoint before performing their union
mapUnionCheckDisjoint :: (Ord k, Show k, Show v) => String -> Map k v -> Map k v -> Map k v
mapUnionCheckDisjoint msg a b = case Data.Map.size (a `Data.Map.intersection` b) of
  0 -> a `Data.Map.union` b
  _ -> error $ msg ++ ":mapUnionCheckDisjoint maps not disjoint: \n" 
                   ++ (Compiler.Front.Common.showList $ Data.Map.toAscList a) ++ "\n" 
                   ++ (Compiler.Front.Common.showList $ Data.Map.toAscList b)

-- |mapUnionCheckDisjoint checks thats is operands are disjoint before performing their union
imapUnionCheckDisjoint :: (Show v) => String -> IM.IntMap v -> IM.IntMap v -> IM.IntMap v
imapUnionCheckDisjoint msg a b = case IM.null (a `IM.intersection` b) of
  True -> a `IM.union` b
  False -> error $ msg ++ ":imapUnionCheckDisjoint maps not disjoint: \n" 
                   ++ (Compiler.Front.Common.showList $ IM.toAscList a) ++ "\n" 
                   ++ (Compiler.Front.Common.showList $ IM.toAscList b)

-- |deleteIfExists deletes from the set if it contains it, or nothing afterwards
deleteIfExists :: (Ord x) => x -> Set x -> Set x
deleteIfExists x set = case Data.Set.member x set of
  True  -> Data.Set.delete x set
  False -> set

-- |assocToListMap takes an associative array (which may contain duplicates) and returns
-- |a Map of lists.
assocToListMap :: Ord k => [(k, v)] -> Map k [v]
assocToListMap ((k, v):r) = case Data.Map.member k acc of
    True  -> Data.Map.adjust (\lst -> v:lst) k acc
    False -> Data.Map.insert k [v] acc
  where acc = (assocToListMap r)
assocToListMap [] = Data.Map.empty

-- |takeOrError throws an error if the input array isn't the exact length
-- |given by the integer argument, or returns it otherwise
takeOrError :: Show a => String -> Int -> [a] -> [a]  
takeOrError msg n l = case n == length l of
  True  -> take n l 
  False -> error $ msg ++ " " ++ (show l)

-- |updateList updates an element in a list.
updateListItem :: [a] -> (a -> a) -> Int -> [a]
updateListItem (h:r) f 0 = (f h):r
updateListItem (h:r) f n = updateListItem r f (n-1)
updateListItem []    f n = error "Common:updateListItem: index less than list length."

-- |listItem list idx. Returns list item at idx, or error if idx is out of range.
listIdx :: Show a => [a] -> Int -> a
listIdx l idx | idx >= 0 && idx < length l = l !! idx
listIdx l idx = error $ "listIdx:index out of range:idx=" ++ (show idx) ++ "\nlist=\n" ++ (show l) 

-- |listItem list idx. Returns list item at idx, or error if idx is out of range.
listGet :: Show a => String -> [a] -> Int -> a
listGet msg l idx | idx >= 0 && idx < length l = l !! idx
listGet msg l idx = error $ msg ++ "\nlistIdx:index out of range:idx=" ++ (show idx) ++ "\nlist=\n" ++ (show l) 

-- intersects ll. Returns intersection of all lists
intersects :: Eq a => [[a]] -> [a]
intersects (a:b:[]) = a `intersect` b
intersects (h:r) = (intersects r) `intersect` h
intersects [] = error "intersects must have at least 2 lists"

-- |pairUp f l. Returns a new list formed by applying f to
-- |all adjacent pairs in l. e.g. pairUp (+) [1,2,3] = [3,5]
pairUp :: (a -> a -> b) -> [a] -> [b]
pairUp f [] = []
pairUp f [a] = []
pairUp f (a1:a2:tl) = (f a1 a2):(pairUp f (a2:tl))

-- |hasCycle seenVars edges. Returns True iff the directed graph has a cycle (i.e.
-- |contains a back edge that points to a vertex that is the input vertex for
-- |an edge that has already been visited.)
hasCycle :: Ord a => Set a -> [(a,[a])] -> Bool
hasCycle _ [] = False
hasCycle vars (hd@(lhs,rhs):tl) = (or $ map (\v -> Data.Set.member v vars') rhs) || (hasCycle vars' tl)
  where vars' = Data.Set.insert lhs vars
