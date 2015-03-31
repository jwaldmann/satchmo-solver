{-# language NoMonomorphismRestriction #-}

module Data.EnumMap where

import qualified Data.IntMap as IM
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

fromList :: Enum k => [(k,v)] -> Map k v
fromList kvs = Map $ IM.fromList $ P.map from kvs

fromListWith :: Enum k => (v -> v -> v) -> [(k,v)] -> Map k v
fromListWith f kvs = Map $ IM.fromListWith f $ P.map from kvs

(!) :: (Show k, Show v, Enum k) => Map k v -> k -> v
mm @ (Map m) ! k = -- m IM.! fromEnum k
  IM.findWithDefault (error $ "missing key " ++ show k ++ " in " ++ show mm)
    (fromEnum k) m

insert k v (Map m) = Map $ IM.insert (fromEnum k) v m
size (Map m) = IM.size m
null (Map m) = IM.null m
elems (Map m) = IM.elems m

filter :: Enum k => (v -> Bool) -> Map k v -> Map k v
filter p (Map m) = Map $ IM.filter p m
delete k (Map m) = Map $ IM.delete (fromEnum k) m
fold f z (Map m) = IM.fold f z m
findWithDefault d k (Map m) = IM.findWithDefault d (fromEnum k) m
difference (Map m1) (Map m2) = Map $ IM.difference m1 m2
union (Map m1) (Map m2) = Map $ IM.union m1 m2
unions ms = Map $ IM.unions $ P.map unMap ms
unionWith f (Map m1) (Map m2) = Map $ IM.unionWith f m1 m2
intersection (Map m1) (Map m2) = Map $ IM.intersection m1 m2

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
