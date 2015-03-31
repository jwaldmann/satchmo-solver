-- | This is a wrapper for Data.IntSet.
-- It replaces the fixed element type (Int)
-- with element type (Enum k => k).
-- Typical usage is for element types like
-- newtype T = T Int deriving Enum
-- that give more type safety in application programs,
-- and toEnum/fromEnum is no-op (hopefully).
-- Note that some type signatures here (e.g., toList)
-- are not most general. This is to avoid ambiguity errors.

module Data.EnumSet where

import Prelude hiding (null)
import qualified Prelude
import qualified Data.IntSet as I

newtype Set k = Set (I.IntSet)

fromList :: Enum k => [k] -> Set k
fromList xs = Set $ I.fromList $ map fromEnum xs

toList :: Enum k => Set k -> [k]
toList (Set s) = map toEnum $ I.toList s

null (Set s) = I.null s

singleton :: Enum k => k -> Set k
singleton x = Set $ I.singleton $ fromEnum x

empty = Set I.empty
member k (Set s) = I.member (fromEnum k) s
notMember k (Set s) = I.notMember (fromEnum k) s
isSubsetOf (Set s1) (Set s2) = I.isSubsetOf s1 s2

insert :: Enum k => k -> Set k -> Set k
insert k (Set s) = Set $ I.insert (fromEnum k) s

delete :: Enum k => k -> Set k -> Set k
delete k (Set s) = Set $ I.delete (fromEnum k) s

union :: Enum k => Set k -> Set k -> Set k
union (Set s1) (Set s2) = Set $ I.union s1 s2

intersection :: Enum k => Set k -> Set k -> Set k
intersection (Set s1) (Set s2) = Set $ I.intersection s1 s2

difference :: Enum k => Set k -> Set k -> Set k
difference (Set s1) (Set s2) = Set $ I.difference s1 s2

filter p (Set s) = Set $ I.filter (p . toEnum) s
partition p (Set s) =
  let (s1,s2) = I.partition (p . toEnum) s
  in  (Set s1, Set s2)
      
