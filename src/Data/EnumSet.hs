module Data.EnumSet where

import Prelude hiding (null)
import qualified Prelude
import qualified Data.IntSet as I

newtype Set k = Set (I.IntSet)

fromList xs = Set $ I.fromList $ map fromEnum xs
toList (Set s) = map toEnum $ I.toList s

null (Set s) = I.null s
empty = Set I.empty

member k (Set s) = I.member (fromEnum k) s
notMember k (Set s) = I.notMember (fromEnum k) s
isSubsetOf (Set s1) (Set s2) = I.isSubsetOf s1 s2

insert k (Set s) = Set $ I.insert (fromEnum k) s
delete k (Set s) = Set $ I.delete (fromEnum k) s

union (Set s1) (Set s2) = Set $ I.union s1 s2
intersection (Set s1) (Set s2) = Set $ I.intersection s1 s2
difference (Set s1) (Set s2) = Set $ I.difference s1 s2

filter p (Set s) = Set $ I.filter (p . toEnum) s
partition p (Set s) =
  let (s1,s2) = I.partition (p . toEnum) s
  in  (Set s1, Set s2)
      