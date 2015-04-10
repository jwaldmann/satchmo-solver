-- | This is a wrapper for Data.IntMap.
-- It replaces the fixed key type (Int)
-- with a key of type (Enum k => k).
-- Typical usage is for key types like
-- newtype T = T Int deriving Enum
-- that give more type safety in application programs,
-- and toEnum/fromEnum is no-op (hopefully).
-- Note that some type signatures here (e.g., toList)
-- are not most general. This is to avoid ambiguity errors.

{-# language NoMonomorphismRestriction #-}

module Data.EnumMap where

import qualified Data.IntMap.Strict as IM
import Prelude hiding ( map )
import qualified Prelude as P

newtype Map k v = Map { unMap :: IM.IntMap v }  deriving (Eq, Ord)

instance (Show v, Show k, Enum k) => Show (Map k v) where
  show m = "fromList " ++ show (toList m)

from (k,v) = (fromEnum k, v)
to (k,v) = (toEnum k, v)

empty = Map $ IM.empty
singleton k v = Map $ IM.singleton (fromEnum k) v

toList :: Enum k => Map k v -> [(k,v)]
toList (Map m) = P.map to $ IM.toList m

toAscList :: Enum k => Map k v -> [(k,v)]
toAscList (Map m) = P.map to $ IM.toAscList m

fromList :: Enum k => [(k,v)] -> Map k v
fromList kvs = Map $ IM.fromList $ P.map from kvs

fromListWith :: Enum k => (v -> v -> v) -> [(k,v)] -> Map k v
fromListWith f kvs = Map $ IM.fromListWith f $ P.map from kvs

(!) :: (Show k, Show v, Enum k) => Map k v -> k -> v
mm @ (Map m) ! k = -- m IM.! fromEnum k
  IM.findWithDefault (error $ "missing key " ++ show k ++ " in " ++ show mm)
    (fromEnum k) m

lookup k (Map m) = IM.lookup (fromEnum k) m

insert k v (Map m) = Map $ IM.insert (fromEnum k) v m
size (Map m) = IM.size m
null (Map m) = IM.null m
elems (Map m) = IM.elems m

filter :: Enum k => (v -> Bool) -> Map k v -> Map k v
filter p (Map m) = Map $ IM.filter p m

delete :: Enum k => k -> Map k v -> Map k v
delete k (Map m) = Map $ IM.delete (fromEnum k) m
-- fold f z (Map m) = IM.fold f z m
findWithDefault d k (Map m) = IM.findWithDefault d (fromEnum k) m
difference (Map m1) (Map m2) = Map $ IM.difference m1 m2

union :: Enum k => Map k v -> Map k v -> Map k v
union (Map m1) (Map m2) = Map $ IM.union m1 m2

unions ms = Map $ IM.unions $ P.map unMap ms
unionWith f (Map m1) (Map m2) = Map $ IM.unionWith f m1 m2

intersection :: Enum k => Map k v1 -> Map k v2 -> Map k v1
intersection (Map m1) (Map m2) = Map $ IM.intersection m1 m2

intersectionWith :: Enum k => (v1 -> v2 -> v3) -> Map k v1 -> Map k v2 -> Map k v3
intersectionWith f (Map m1) (Map m2) = Map $ IM.intersectionWith f m1 m2

split :: Enum k => k -> Map k v -> (Map k v, Map k v)
split k (Map m) =
    let (lo, hi) = IM.split (fromEnum k) m
    in  (Map lo, Map hi)

adjust :: Enum k => (v -> v) -> k -> Map k v -> Map k v
adjust f k (Map m) = Map $ IM.adjust f (fromEnum k) m

alter  f k (Map m) = Map $ IM.alter f (fromEnum k) m

keys :: Enum k => Map k v -> [k]
keys (Map m) = P.map toEnum $ IM.keys m

map :: Enum k => (v -> w) -> Map k v -> Map k w
map f (Map m) = Map $ IM.map f m

mapWithKey :: Enum k => (k -> v -> w) -> Map k v -> Map k w
mapWithKey f (Map m) = Map $ IM.mapWithKey ( \ k v -> f (toEnum k) v ) m

findMin (Map m) = to $ IM.findMin m
findMax (Map m) = to $ IM.findMax m
