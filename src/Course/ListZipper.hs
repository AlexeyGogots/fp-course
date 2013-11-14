{-# LANGUAGE NoImplicitPrelude #-}

module Course.ListZipper where

import Course.Core
import Course.List
import Course.Optional
import Course.Functor
import Course.Apply
import Course.Applicative
import Course.Bind
import Course.Extend
import Course.Comonad
import Course.Traversable
import qualified Prelude as P

-- $setup
-- >>> import Data.Maybe(isNothing)
-- >>> import Test.QuickCheck
-- >>> import qualified Prelude as P(return, maybe)
-- >>> import Core(Num(..), id, const)
-- >>> import Data.List(null)
-- >>> instance Arbitrary a => Arbitrary (ListZipper a) where arbitrary = do l <- arbitrary; x <- arbitrary; r <- arbitrary; P.return (ListZipper l x r)

-- A `ListZipper` is a focussed position, with a list of values to the left and to the right.
--
-- For example, taking the list [0,1,2,3,4,5,6], the moving focus to the third position, the zipper looks like:
-- ListZipper [2,1,0] 3 [4,5,6]
--
-- Supposing then we move left on this zipper:
-- ListZipper [1,0] 2 [3,4,5,6]
--
-- then suppose we add 17 to the focus of this zipper:
-- ListZipper [1,0] 19 [3,4,5,6]
data ListZipper a =
  ListZipper (List a) a (List a)
  deriving Eq

-- A `MaybeListZipper` is a data structure that allows us to "fail" zipper operations.
-- e.g. Moving left when there are no values to the left.
--
-- We then overload operations polymorphically to operate on both `ListZipper` and `MaybeListZipper`
-- using the `ListZipper'` type-class below.
data MaybeListZipper a =
  IsZ (ListZipper a)
  | IsNotZ
  deriving Eq

-- Exercise 1
--
-- | Implement the `Functor` instance for `ListZipper`.
--
-- >>> (+1) <$> (ListZipper [3,2,1] 4 [5,6,7])
-- [4,3,2] >5< [6,7,8]
instance Functor ListZipper where
  f <$> (ListZipper l x r) =
    ListZipper (f <$> l) (f x) (f <$> r)

-- Exercise 2
--
-- | Implement the `Functor` instance for `MaybeListZipper`.
--
-- >>> (+1) <$> (IsZ (ListZipper [3,2,1] 4 [5,6,7]))
-- [4,3,2] >5< [6,7,8]
instance Functor MaybeListZipper where
  f <$> (IsZ z) =
    IsZ (f <$> z)
  _ <$> IsNotZ =
    IsNotZ

-- Exercise 3
--
-- | Create a `MaybeListZipper` positioning the focus at the head.
--
-- prop> xs == toListZ (fromList xs)
fromList ::
  List a
  -> MaybeListZipper a
fromList Nil =
  IsNotZ
fromList (h:.t) =
  IsZ (ListZipper Nil h t)

-- Exercise 4
--
-- | Retrieve the `ListZipper` from the `MaybeListZipper` if there is one.
--
-- prop> null xs == isNothing (toMaybe (fromList xs))
--
-- prop> toMaybe (fromMaybe z) == z
toOptional ::
  MaybeListZipper a
  -> Optional (ListZipper a)
toOptional IsNotZ =
  Empty
toOptional (IsZ z) =
  Full z

fromMaybe ::
  Optional (ListZipper a)
  -> MaybeListZipper a
fromMaybe Empty =
  IsNotZ
fromMaybe (Full z) =
  IsZ z

asZipper ::
  (ListZipper a -> ListZipper a)
  -> MaybeListZipper a
  -> MaybeListZipper a
asZipper f =
  asMaybeZipper (IsZ . f)

(>$>)::
  (ListZipper a -> ListZipper a)
  -> MaybeListZipper a
  -> MaybeListZipper a
(>$>) =
  asZipper

asMaybeZipper ::
  (ListZipper a -> MaybeListZipper a)
  -> MaybeListZipper a
  -> MaybeListZipper a
asMaybeZipper _ IsNotZ =
  IsNotZ
asMaybeZipper f (IsZ z) =
  f z

(>->) ::
  (ListZipper a -> MaybeListZipper a)
  -> MaybeListZipper a
  -> MaybeListZipper a
(>->) =
  asMaybeZipper

-- Exercise 5
--
-- | Convert the given zipper back to a list.
toList ::
  ListZipper a
  -> List a
toList (ListZipper l x r) =
  reverse l ++ x:.r

-- | Convert the given (maybe) zipper back to a list.
toListZ ::
  MaybeListZipper a
  -> List a
toListZ IsNotZ =
  Nil
toListZ (IsZ z) =
  toList z

-- Exercise 6
--
-- | Update the focus of the zipper with the given function on the current focus.
--
-- >>> withFocus (+1) (ListZipper Nil 0 [1])
-- Nil >1< [1]
--
-- >>> withFocus (+1) (ListZipper [1,0] 2 [3,4])
-- [1,0] >3< [3,4]
withFocus ::
  (a -> a)
  -> ListZipper a
  -> ListZipper a
withFocus f (ListZipper l x r) =
  ListZipper l (f x) r

-- Exercise 7
--
-- | Set the focus of the zipper to the given value.
-- /Tip:/ Use `withFocus`.
--
-- >>> setFocus 1 (ListZipper Nil 0 [1])
-- Nil >1< [1]
--
-- >>> setFocus 1 (ListZipper [1,0] 2 [3,4])
-- [1,0] >1< [3,4]
setFocus ::
  a
  -> ListZipper a
  -> ListZipper a
setFocus =
  withFocus . const

-- A flipped infix alias for `setFocus`. This allows:
--
-- z := "abc" -- sets the focus on the zipper z to the value "abc".
(.=) ::
  ListZipper a
  -> a
  -> ListZipper a
(.=) =
  flip setFocus

-- Exercise 8
--
-- | Returns whether there are values to the left of focus.
--
-- >>> hasLeft (ListZipper [1,0] 2 [3,4])
-- True
--
-- >>> hasLeft (ListZipper Nil 0 [1,2])
-- False
hasLeft ::
  ListZipper a
  -> Bool
hasLeft (ListZipper l _ _) =
  not (isEmpty l)

-- Exercise 9
--
-- | Returns whether there are values to the right of focus.
--
-- >>> hasRight (ListZipper [1,0] 2 [3,4])
-- True
--
-- >>> hasRight (ListZipper [1,0] 2 Nil)
-- False
hasRight ::
  ListZipper a
  -> Bool
hasRight (ListZipper _ _ r) =
  not (isEmpty r)

-- Exercise 10
--
-- | Seek to the left for a location matching a predicate, starting from the
-- current one.
--
-- prop> findLeft (const True) >-> fromList xs == fromList xs
--
-- prop> findLeft (const False) (ListZipper l x r) == IsNotZ
findLeft ::
  (a -> Bool)
  -> ListZipper a
  -> MaybeListZipper a
findLeft p (ListZipper ls x rs) =
  case break p (x:.ls) of
    (rs', x':.ls') -> IsZ (ListZipper ls' x' (reverse rs' ++ rs))
    _ -> IsNotZ

-- Exercise 11
--
-- | Seek to the right for a location matching a predicate, starting from the
-- current one.
--
-- prop> findRight (const True) >-> fromList xs == fromList xs
--
-- prop> findRight (const False) (ListZipper l x r) == IsNotZ
findRight ::
  (a -> Bool)
  -> ListZipper a
  -> MaybeListZipper a
findRight p (ListZipper ls x rs) =
  case break p (x:.rs) of
    (ls', x':.rs') -> IsZ (ListZipper (reverse ls' ++ ls) x' rs')
    _ -> IsNotZ

-- Exercise 12
--
-- | Move the zipper left, or if there are no elements to the left, go to the far right.
-- CAUTION: This function is non-total, why?
--
-- >>> moveLeftLoop (ListZipper [3,2,1] 4 [5,6,7])
-- [2,1] >3< [4,5,6,7]
--
-- >>> moveLeftLoop (ListZipper Nil 1 [2,3,4])
-- [3,2,1] >4< Nil
moveLeftLoop ::
  ListZipper a
  -> ListZipper a
moveLeftLoop (ListZipper Nil x r) =
  let (x':.r') = (reverse (x:.r))
  in ListZipper r' x' Nil
moveLeftLoop (ListZipper (h:.t) x r) =
  ListZipper t h (x:.r)

-- Exercise 13
--
-- | Move the zipper right, or if there are no elements to the right, go to the far left.
--
-- >>> moveRightLoop (ListZipper [3,2,1] 4 [5,6,7])
-- [4,3,2,1] >5< [6,7]
--
-- >>> moveRightLoop (ListZipper [3,2,1] 4 Nil)
-- Nil >1< [2,3,4]
moveRightLoop ::
  ListZipper a
  -> ListZipper a
moveRightLoop (ListZipper l x Nil) =
   let (x':.l') = reverse (x:.l)
   in ListZipper Nil x' l'
moveRightLoop (ListZipper l x (h:.t)) =
   ListZipper (x:.l) h t

-- Exercise 14
--
-- | Move the zipper one position to the left.
--
-- >>> moveLeft (ListZipper [3,2,1] 4 [5,6,7])
-- [2,1] >3< [4,5,6,7]
--
-- >>> moveLeft (ListZipper Nil 1 [2,3,4])
-- ><
moveLeft ::
  ListZipper a
  -> MaybeListZipper a
moveLeft (ListZipper Nil _ _) =
  IsNotZ
moveLeft (ListZipper (h:.t) x r) =
  IsZ (ListZipper t h (x:.r))

-- Exercise 15
--
-- | Move the zipper one position to the right.
--
-- >>> moveRight (ListZipper [3,2,1] 4 [5,6,7])
-- [4,3,2,1] >5< [6,7]
--
-- >>> moveRight (ListZipper [3,2,1] 4 Nil)
-- ><
moveRight ::
  ListZipper a
  -> MaybeListZipper a
moveRight (ListZipper _ _ Nil) =
  IsNotZ
moveRight (ListZipper l x (h:.t)) =
  IsZ (ListZipper (x:.l) h t)

-- Exercise 16
--
-- | Swap the current focus with the value to the left of focus.
--
-- >>> swapLeft (ListZipper [3,2,1] 4 [5,6,7])
-- [4,2,1] >3< [5,6,7]
--
-- >>> swapLeft (ListZipper Nil 1 [2,3,4])
-- ><
swapLeft ::
  ListZipper a
  -> MaybeListZipper a
swapLeft (ListZipper Nil _ _) =
  IsNotZ
swapLeft (ListZipper (h:.t) x r) =
  IsZ (ListZipper (x:.t) h r)

-- Exercise 17
--
-- | Swap the current focus with the value to the right of focus.
--
-- >>> swapRight (ListZipper [3,2,1] 4 [5,6,7])
-- [3,2,1] >5< [4,6,7]
--
-- >>> swapRight (ListZipper [3,2,1] 4 Nil)
-- ><
swapRight ::
  ListZipper a
  -> MaybeListZipper a
swapRight (ListZipper _ _ Nil) =
  IsNotZ
swapRight (ListZipper l x (h:.t)) =
  IsZ (ListZipper l h (x:.t))

-- Exercise 18
--
-- | Drop all values to the left of the focus.
--
-- >>> dropLefts (ListZipper [3,2,1] 4 [5,6,7])
-- Nil >4< [5,6,7]
--
-- >>> dropLefts (ListZipper Nil 1 [2,3,4])
-- Nil >1< [2,3,4]
--
-- prop> dropLefts (ListZipper l x r) == ListZipper Nil x r
dropLefts ::
  ListZipper a
  -> ListZipper a
dropLefts (ListZipper _ x r) =
  ListZipper Nil x r

-- Exercise 19
--
-- | Drop all values to the right of the focus.
--
-- >>> dropRights (ListZipper [3,2,1] 4 [5,6,7])
-- [3,2,1] >4< Nil
--
-- >>> dropRights (ListZipper [3,2,1] 4 Nil)
-- [3,2,1] >4< Nil
--
-- prop> dropRights (ListZipper l x r) == ListZipper l x Nil
dropRights ::
  ListZipper a
  -> ListZipper a
dropRights (ListZipper l x _) =
  ListZipper l x Nil

-- Exercise 20
--
-- Move the focus left the given number of positions. If the value is negative, move right instead.
moveLeftN ::
  Int
  -> ListZipper a
  -> MaybeListZipper a
moveLeftN n z | n == 0 =
  IsZ z
moveLeftN n z | n < 0 =
  moveRightN (negate n) z
moveLeftN n z | otherwise =
  moveLeftN (pred n) >-> moveLeft z

-- Exercise 21
--
-- Move the focus right the given number of positions. If the value is negative, move left instead.
moveRightN ::
  Int
  -> ListZipper a
  -> MaybeListZipper a
moveRightN n z | n == 0 =
  IsZ z
moveRightN n z | n < 0 =
  moveLeftN (negate n) z
moveRightN n z | otherwise =
  moveRightN (pred n) >-> moveRight z

-- Exercise 22
--
-- | Move the focus left the given number of positions. If the value is negative, move right instead.
-- If the focus cannot be moved, the given number of times, return the value by which it can be moved instead.
--
-- >>> moveLeftN' 4 (ListZipper [3,2,1] 4 [5,6,7])
-- Left 3
--
-- >>> moveLeftN' 1 (ListZipper [3,2,1] 4 [5,6,7])
-- Right [2,1] >3< [4,5,6,7]
--
-- >>> moveLeftN' 0 (ListZipper [3,2,1] 4 [5,6,7])
-- Right [3,2,1] >4< [5,6,7]
--
-- >>> moveLeftN' (-2) (ListZipper [3,2,1] 4 [5,6,7])
-- Right [5,4,3,2,1] >6< [7]
--
-- >>> moveLeftN' (-4) (ListZipper [3,2,1] 4 [5,6,7])
-- Left 3
moveLeftN' ::
  Int
  -> ListZipper a
  -> Either Int (ListZipper a)
moveLeftN' n z =
  let moveLeftN'' n' z' q =
        if n' == 0
          then
            Right z'
          else
            if n' < 0
              then
                moveRightN' (negate n') z
              else
                case moveLeft z' of
                  IsZ zz -> moveLeftN'' (n' - 1) zz (q + 1)
                  IsNotZ -> Left q
  in moveLeftN'' n z 0

-- Exercise 23
--
-- | Move the focus right the given number of positions. If the value is negative, move left instead.
-- If the focus cannot be moved, the given number of times, return the value by which it can be moved instead.
--
-- >>> moveRightN' 4 (ListZipper [3,2,1] 4 [5,6,7])
-- Left 3
--
-- >>> moveRightN' 1 (ListZipper [3,2,1] 4 [5,6,7])
-- Right [4,3,2,1] >5< [6,7]
--
-- >>> moveRightN' 0 (ListZipper [3,2,1] 4 [5,6,7])
-- Right [3,2,1] >4< [5,6,7]
--
-- >>> moveRightN' (-2) (ListZipper [3,2,1] 4 [5,6,7])
-- Right [1] >2< [3,4,5,6,7]
--
-- >>> moveRightN' (-4) (ListZipper [3,2,1] 4 [5,6,7])
-- Left 3
moveRightN' ::
  Int
  -> ListZipper a
  -> Either Int (ListZipper a)
moveRightN' n z =
  let moveRightN'' n' z' q =
        if n' == 0
          then
            Right z'
          else
            if n' < 0
              then
                moveLeftN' (negate n') z
              else
                case moveRight z' of
                  IsZ zz -> moveRightN'' (n' - 1) zz (q + 1)
                  IsNotZ -> Left q
  in moveRightN'' n z 0

-- Exercise 24
--
-- | Move the focus to the given absolute position in the zipper. Traverse the zipper only to the extent required.
--
-- >>> nth 1 (ListZipper [3,2,1] 4 [5,6,7])
-- [1] >2< [3,4,5,6,7]
--
-- >>> nth 5 (ListZipper [3,2,1] 4 [5,6,7])
-- [5,4,3,2,1] >6< [7]
--
-- >>> nth 8 (ListZipper [3,2,1] 4 [5,6,7])
-- ><
nth ::
  Int
  -> ListZipper a
  -> MaybeListZipper a
nth i z =
  if i < 0
    then
      IsNotZ
    else
      case moveLeftN' i z of
             Left a -> moveRightN (i-a) z
             Right (ListZipper l _ _) -> moveLeftN (length l) z

-- Exercise 25
--
-- | Return the absolute position of the current focus in the zipper.
--
-- >>> index (ListZipper [3,2,1] 4 [5,6,7])
-- Just 3
--
-- prop> P.maybe True (\i -> P.maybe False (==z) (toOptional (nth i z))) (index z)
index ::
  ListZipper a
  -> Optional Int
index (ListZipper l _ _) =
  Full (length l)

-- Exercise 26
--
-- | Move the focus to the end of the zipper.
-- CAUTION: This function is non-total, why?
--
-- >>> end (ListZipper [3,2,1] 4 [5,6,7])
-- [6,5,4,3,2,1] >7< Nil
end ::
  ListZipper a
  -> ListZipper a
end (ListZipper l x r) =
  let (x':.r') = reverse (x:.r)
  in ListZipper (r' ++ l) x' Nil

-- Exercise 27
--
-- | Move the focus to the start of the zipper.
--
-- >>> start (ListZipper [3,2,1] 4 [5,6,7])
-- Nil >1< [2,3,4,5,6,7]
start ::
  ListZipper a
  -> ListZipper a
start (ListZipper l x r) =
  let (x':.r') = reverse (x:.l)
  in ListZipper Nil x' (r' ++ r)

-- Exercise 28
--
-- | Delete the current focus and pull the left values to take the empty position.
--
-- >>> deletePullLeft (ListZipper [3,2,1] 4 [5,6,7])
-- [2,1] >3< [5,6,7]
--
-- >>> deletePullLeft (ListZipper Nil 1 [2,3,4])
-- ><
deletePullLeft ::
  ListZipper a
  -> MaybeListZipper a
deletePullLeft (ListZipper Nil _ _) =
  IsNotZ
deletePullLeft (ListZipper (h:.t) _ r) =
  IsZ (ListZipper t h r)

-- Exercise 29
--
-- | Delete the current focus and pull the right values to take the empty position.
--
-- >>> deletePullRight (ListZipper [3,2,1] 4 [5,6,7])
-- [3,2,1] >5< [6,7]
--
-- >>> deletePullRight (ListZipper [3,2,1] 4 Nil)
-- ><
deletePullRight ::
  ListZipper a
  -> MaybeListZipper a
deletePullRight (ListZipper _ _ Nil) =
  IsNotZ
deletePullRight (ListZipper l _ (h:.t)) =
  IsZ (ListZipper l h t)

-- Exercise 30
--
-- | Insert at the current focus and push the left values to make way for the new position.
--
-- >>> insertPushLeft 15 (ListZipper [3,2,1] 4 [5,6,7])
-- [4,3,2,1] >15< [5,6,7]
--
-- >>> insertPushLeft 15 (ListZipper Nil 1 [2,3,4])
-- [1] >15< [2,3,4]
--
-- prop> P.maybe False (==z) (toMaybe (deletePullLeft (insertPushLeft i z)))
insertPushLeft ::
  a
  -> ListZipper a
  -> ListZipper a
insertPushLeft a (ListZipper l x r) =
  ListZipper (x:.l) a r

-- Exercise 31
--
-- | Insert at the current focus and push the right values to make way for the new position.
--
-- >>> insertPushRight 15 (ListZipper [3,2,1] 4 [5,6,7])
-- [3,2,1] >15< [4,5,6,7]
--
-- >>> insertPushRight 15 (ListZipper [3,2,1] 4 Nil)
-- [3,2,1] >15< [4]
--
-- prop> P.maybe False (==z) (toMaybe (deletePullRight (insertPushRight i z)))
insertPushRight ::
  a
  -> ListZipper a
  -> ListZipper a
insertPushRight a (ListZipper l x r) =
  ListZipper l a (x:.r)

-- Exercise 32
--
-- | Implement the `Apply` instance for `ListZipper`.
-- This implementation zips functions with values by function application.
--
-- >>> ListZipper [(+2), (+10)] (*2) [(*3), (4*), (5+)] <*> ListZipper [3,2,1] 4 [5,6,7]
-- [5,12] >8< [15,24,12]
instance Apply ListZipper where
  ListZipper fl fx fr <*> ListZipper al ax ar =
    ListZipper (zipWith ($) fl al) (fx ax) (zipWith ($) fr ar)

-- Exercise 33
--
-- | Implement the `Apply` instance for `MaybeListZipper`.
--
-- /Tip:/ Use `<*>` for `ListZipper`.
instance Apply MaybeListZipper where
  IsNotZ <*> _ = IsNotZ
  _ <*> IsNotZ = IsNotZ
  IsZ f <*> IsZ a = IsZ (f <*> a)

-- Exercise 34
--
-- | Implement the `Applicative` instance for `ListZipper`.
-- This implementation produces an infinite list zipper (to both left and right).
--
-- /Tip:/ Use @Data.List#repeat@.
instance Applicative ListZipper where
  pure a =
    ListZipper (repeat a) a (repeat a)

-- Exercise 35
--
-- | Implement the `Applicative` instance for `MaybeListZipper`.
--
-- /Tip:/ Use @pure@ for `ListZipper`.
instance Applicative MaybeListZipper where
  pure =
    IsZ . pure

-- Exercise 36
--
-- | Implement the `Extend` instance for `ListZipper`.
-- This implementation "visits" every possible zipper value derivable from a given zipper (i.e. all zippers to the left and right).
--
-- /Tip:/ Use @Data.List#unfoldr@.
--
-- >>> id <<= (ListZipper [2,1] 3 [4,5])
-- [[1] >2< [3,4,5],Nil >1< [2,3,4,5]] >[2,1] >3< [4,5]< [[3,2,1] >4< [5],[4,3,2,1] >5< Nil]
instance Extend ListZipper where
  f <<= z =
    ListZipper (unfoldr ((<$>) (\z' -> (f z', z')) . toOptional . moveLeft) z) (f z) (unfoldr ((<$>) (\z' -> (f z', z')) . toOptional . moveRight) z)

-- Exercise 37
--
-- | Implement the `Comonad` instance for `ListZipper`.
-- This implementation returns the current focus of the zipper.
--
-- >>> copure (ListZipper [2,1] 3 [4,5])
-- 3
instance Comonad ListZipper where
  copure (ListZipper _ x _) =
    x

-- Exercise 38
--
-- | Implement the `Traversable` instance for `ListZipper`.
-- This implementation traverses a zipper while running some `Applicative` effect through the zipper.
-- An effectful zipper is returned.
instance Traversable ListZipper where
  traverse f (ListZipper l x r) =
    (ListZipper . reverse) <$> (traverse f $ reverse l) <*> f x <*> traverse f r

-- Exercise 39
--
-- | Implement the `Traversable` instance for `MaybeListZipper`.
--
-- /Tip:/ Use `traverse` for `ListZipper`.
instance Traversable MaybeListZipper where
  traverse _ IsNotZ =
    pure IsNotZ
  traverse f (IsZ z) =
    IsZ <$> traverse f z

-----------------------
-- SUPPORT LIBRARIES --
-----------------------

instance Show a => Show (ListZipper a) where
  show (ListZipper l x r) =
    stringconcat [show l, " >", show x, "< ", show r]

instance Show a => Show (MaybeListZipper a) where
  show (IsZ z) = show z
  show IsNotZ = "><"
