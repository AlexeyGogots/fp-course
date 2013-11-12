{-# LANGUAGE NoImplicitPrelude #-}

module Structure.BKTree
(
  BKTree
, empty
, bktree
, isEmpty
, size
, (.:.)
, member
, withinDistance
, fromWords
, fromDictionaryFile
) where

import Core
import Structure.MetricSpace
import Data.Map(Map)
import qualified Data.Map as M
import Data.Foldable
import qualified Data.Foldable as F
import Data.Monoid
import qualified Prelude as P

data BKTree a =
  Node a !Int (BMap a)
  | Leaf
  deriving (Eq, Show)

empty ::
  BKTree a
empty =
  Leaf

instance MetricSpace a => Monoid (BKTree a) where
  mempty =
    empty
  t `mappend` u =
    foldl' (flip (.:.)) t (asList u)
  mconcat =
    foldl' mappend empty

instance Foldable BKTree where
  foldl f z =
    foldl' f z . asList
  foldr f z =
    F.foldr f z . asList

bktree ::
  (MetricSpace a, Foldable f) =>
  f a
  -> BKTree a
bktree =
  foldl' (flip (.:.)) empty

isEmpty ::
  BKTree a
  -> Bool
isEmpty Leaf =
  True
isEmpty (Node _ _ _) =
  False

size ::
  BKTree a
  -> Int
size Leaf =
  0
size (Node _ s _) =
  s

(.:.) ::
  MetricSpace a =>
  a
  -> BKTree a
  -> BKTree a
a .:. Leaf =
  Node a 1 M.empty
a .:. Node z s m =
  let d = z <--> a
  in Node z (s+1) (M.alter (\zz -> Just $! case zz of
                                             Just w -> a .:. w
                                             Nothing -> Node a 1 M.empty) d m)

infixr 5 .:.

member ::
  MetricSpace a =>
  a
  -> BKTree a
  -> Bool
member _ Leaf =
  False
member a (Node z _ m) =
  let d = z <--> a
  in d == 0 || F.any (member a) (d `M.lookup` m)

withinDistance ::
  MetricSpace a =>
  Int
  -> a
  -> BKTree a
  -> [(Int, a)]
withinDistance _ _ Leaf =
  []
withinDistance n a t@(Node z _ _) =
  let d = z <--> a
      k = M.toList (usingMap (breakMap d n) M.empty t) >>= \(_, u) -> withinDistance n a u
  in (if d <= n then ((d, z) :) else id) k

fromWords ::
  String
  -> BKTree String
fromWords =
  bktree . words

fromDictionaryFile ::
  FilePath
  -> IO (BKTree String)
fromDictionaryFile p =
  fmap fromWords $ readFile p

-- not exported

type BMap a =
  Map Int (BKTree a)

asList ::
  BKTree a
  -> [a]
asList Leaf =
  []
asList (Node a _ m) =
  a : (asList `concatMap` P.map snd (M.toList m))

usingMap ::
  (BMap a -> x)
  -> x
  -> BKTree a
  -> x
usingMap _ l Leaf =
  l
usingMap f _ (Node _ _ m) =
  f m

breakMap ::
  Int
  -> Int
  -> BMap a
  -> BMap a
breakMap d n m =
  fst $ M.split (d + n + 1) (snd $ M.split (d - n - 1) m)
