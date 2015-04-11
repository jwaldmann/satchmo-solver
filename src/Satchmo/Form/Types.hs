{-# language GeneralizedNewtypeDeriving #-}

module Satchmo.Form.Types

( V
, Literal, variable, positive
, Clause, clause, literals, unit, nullC, emptyC, sizeC, insertC, unionC
, compatibleC
, get_value, without, withouts
)

where

import qualified Data.EnumMap as M
  
newtype V = V Int deriving (Enum, Show, Eq, Ord)

data Literal = Literal { variable :: ! V, positive :: ! Bool }
  deriving ( Eq, Ord )

instance Show Literal where
  show l = show
         $ (if positive l then id else negate )
         $ fromEnum $ variable l
           
newtype Clause = Clause ( M.Map V Bool )
  deriving (Eq, Ord)

instance Show Clause where
  show cl = show $ literals cl

clause vbs = Clause $ M.fromList vbs

sizeC (Clause m) = M.size m

get_value (Clause m) v = M.lookup v m

emptyC = Clause M.empty
unit cl = 1 == sizeC cl
nullC cl = 0 == sizeC cl
insertC v b (Clause m) = Clause $ M.insert v b m
unionC (Clause a) (Clause b) =
  Clause $ M.unionWith
    ( \ l r -> if l /= r then error "unionC: conflict" else l)
    a b

compatibleC (Clause a) (Clause b) = 
    M.intersection a b == M.intersection b a
             
literals :: Clause -> [ Literal ]
literals (Clause m) = map (uncurry Literal) $ M.toList m

without (Clause m) v = Clause $ M.delete v m
withouts (Clause m) a = Clause $ M.difference m a
