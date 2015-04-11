{-# language GeneralizedNewtypeDeriving #-}

module Satchmo.State.Model 

( State, root, current, get_level, the_assignment
, get_reason, get_decision_level, get_assigned, get_assignment
, unit_clauses

, positive_clauses_for, negative_clauses_for, empty_clauses
, units, variables, size, satisfied, contradictory
, initial, assign, descend_from
, drop_variable, add_clauses, learn_and_backjump
, Reason (..), Origin (..), Time, Level
, get_clause, get_unit_clause
, V, C, CNF, literals, without, smallest_clauses, Clause
, emptyC, insertC, sizeC, unionC, compatibleC, get_value
, variable, positive, Literal
)
  
where

import Satchmo.Form
   hiding (assign, drop_variable, add_clauses
          ,empty_clauses,  get_unit_clause)
import qualified Satchmo.Form.Model as F

import qualified Data.EnumMap as M
import qualified Data.EnumSet as S
import Data.Function (on)
import Data.List ( sortBy )
import Control.Monad ( guard )

-- | clock ticks at each assignment (decide or propagate)
newtype Time = Time Int deriving (Enum, Show, Eq, Ord)

-- | decision level (ticks only at decisions)
newtype Level = Level Int deriving (Enum, Show, Eq, Ord)

data State =
     State { root :: ! CNF
           , assignment :: ! (M.Map V Bool)
           , reason :: ! (M.Map V Reason)
           , time :: ! Time
           , level :: ! Level
           , assigned :: ! (M.Map V Time)
           , decision_level :: ! (M.Map V Level)
           }

-- | clauses that are not definitely satisfied
-- under the current partial assignment
current s = cnf $ do
  cl <- clausesL $ root s
  guard $ not $ flip any (literals cl) $ \ l ->
    Just (positive l) == M.lookup (variable l) (assignment s) 
  return $ cl `withouts` assignment s

-- | this returns the original clauses
-- which are currently unit.
unit_clauses s = do
  cl <- clausesL $ root s
  guard $ not $ flip any (literals cl) $ \ l ->
    Just (positive l) == M.lookup (variable l) (assignment s)
  let clnow = cl `withouts` assignment s
  guard $ unit clnow
  return cl

empty_clauses s = do
  cl <- clausesL $ root s
  guard $ not $ flip any (literals cl) $ \ l ->
    Just (positive l) == M.lookup (variable l) (assignment s)
  let clnow = cl `withouts` assignment s
  guard $ nullC clnow
  return cl

get_unit_clause s cl =
  F.get_unit_clause undefined $ cl `withouts` assignment s 

instance Show State where
  show f = unlines
     [ unwords [ show $ time f , show $ level f ]
     -- , "root: " ++ show ( root f  )
     -- , "assignment: " ++ show (assignment f )
     , "current: " ++ show ( current f )
     , unlines $ do
          (l,vs) <- M.toAscList $ M.fromListWith S.union $ do
            (v,l) <- M.toList $ decision_level f
            return (l, S.singleton v)
          let us = do
               v <- sortBy (compare `on` (assigned f M.!)) $ S.toList vs
               return $ ( if assignment f M.! v then id else negate )
                      $ fromEnum v
          return $ unwords $ show l : ":" :  map show us
     ]

data Origin = Input -- ^ this clause is an element of the input CNF
            | Resolved C C -- ^ this clause appeared by resolution (elimination)
            | Learnt -- ^ this clause was learnt
    deriving ( Eq, Ord, Show )

-- | the reason for the current value of a variable.
data Reason
  = Decided -- ^ the value was assigned when entering a subtree
  | Propagated C -- ^ the value was computed by unit propagation, using this clause
    deriving ( Eq, Ord, Show )

the_assignment s = assignment s
get_assignment f v = assignment f M.! v
get_assigned f v = assigned f M.! v
get_reason f v = reason f M.! v
get_decision_level f v = decision_level f M.! v
get_level f = level f

initial cnf = State { root = cnf
                  , assignment = M.empty, reason = M.empty
                  , time = Time 0
                  , level = Level 0
                  , assigned = M.empty
                  , decision_level = M.empty
                  }

drop_variable v s =
  s { root = F.drop_variable v $ root s }

add_clauses cls s =
  s { root = F.add_clauses cls $ root s }

descend_from _ s = s

assign re (v,b) s =
  let this_level = case re of
        Decided -> succ $ level s
        Propagated {} -> level s
  in  s { assignment = M.insert v b $ assignment s
        , reason = M.insert v re $ reason s
        , assigned = M.insert v (time s) $ assigned s
        , time = succ $ time s
        , decision_level =
             M.insert v this_level $ decision_level s
        , level = this_level
        }

learn_and_backjump s (cl, lvl) =
  let ignore = M.filter ( > lvl ) $ decision_level s
      cleanup m = M.difference m ignore
  in s { root = F.add_clauses [cl] $ root s
       , assignment = cleanup $ assignment s
       , reason = cleanup $ reason s
       , assigned = cleanup $ assigned s 
       , time = succ $ time s
       , decision_level = cleanup $ decision_level s
       , level = lvl
       }
