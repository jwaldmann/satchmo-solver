{-# language GeneralizedNewtypeDeriving #-}

module Satchmo.State

( State, root, current, get_level, the_assignment
, get_reason, get_decision_level, get_assigned, get_assignment
, positive_clauses_for, negative_clauses_for, empty_clauses
, units, variables, size, satisfied, contradictory
, initial, assign, descend_from
, drop_variable, add_clauses
, Reason (..), Origin (..), Time, Level
, get_clause, get_unit_clause
, V, C, CNF, literals, without, smallest_clauses, Clause
, emptyC, insertC, sizeC, unionC, compatibleC, get_value
, variable, positive, Literal
)
  
where

import Satchmo.Form
   hiding (assign, drop_variable, add_clauses)
import qualified Satchmo.Form.Model as F

import qualified Data.EnumMap as M

-- | clock ticks at each assignment (decide or propagate)
newtype Time = Time Int deriving (Enum, Show, Eq, Ord)

-- | decision level (ticks only at decisions)
newtype Level = Level Int deriving (Enum, Show, Eq, Ord)

data State =
     State { root :: ! CNF
           , current :: ! CNF
           , assignment :: ! (M.Map V Bool)
           , reason :: ! (M.Map V Reason)
           , time :: ! Time
           , level :: ! Level
           , assigned :: ! (M.Map V Time)
           , decision_level :: ! (M.Map V Level)
           }
  deriving Show

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

initial cnf = State { root = cnf, current = cnf
                  , assignment = M.empty, reason = M.empty
                  , time = Time 0
                  , level = Level 0
                  , assigned = M.empty
                  , decision_level = M.empty
                  }

drop_variable v s =
  s { current = F.drop_variable v $ current s }

add_clauses cls s =
  s { current = F.add_clauses cls $ current s }

descend_from _ s = s

assign re (v,b) s =
  let this_level = case re of
        Decided -> succ $ level s
        Propagated {} -> level s
  in  s { current = F.assign (v,b) $ current s
        , assignment = M.insert v b $ assignment s
        , reason = M.insert v re $ reason s
        , assigned = M.insert v (time s) $ assigned s
        , time = succ $ time s
        , decision_level =
             M.insert v this_level $ decision_level s
        , level = this_level
        }

