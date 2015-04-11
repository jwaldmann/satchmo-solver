-- | Propositional Logic Formulas in Conjunctive Normal Form.
-- This module is a model implementation of the API
-- (obviously correct, but also obviously non-efficient)

module Satchmo.Form.Model

( module Satchmo.Form.Types 
, CNF, cnf, C
, size
, variables, clauses, clausesL
, smallest_clauses
, empty_clauses
, get_clause, get_unit_clause

, units
-- , positive_units, negative_units

, clauses_for, positive_clauses_for, negative_clauses_for
-- , literals_for, positive_literals_for, negative_literals_for

, satisfied, contradictory

-- , add_clauses, add_clause, add_clause'
-- , drop_variable, add_variable

, empty
, assign
, drop_variable
, add_clauses

, check_asserts, using_model
)
  
where

import Satchmo.Form.Types

import qualified Data.Set as DS
import qualified Data.EnumSet as S
import qualified Data.Map as M

import Control.Monad ( mzero )
import Data.Function (on)
import Data.List ( sortBy )

check_asserts = False
using_model = True

data CNF = CNF { clauses :: DS.Set Clause }
  deriving Show

cnf cls = CNF { clauses = DS.fromList cls }

type C = Clause

get_clause _ cl = cl
get_unit_clause f cl = case literals (get_clause f cl) of
  [l] -> (variable l,positive l)

clausesL = DS.toList . clauses

smallest_clauses n cnf = take n
  $ sortBy (compare `on` sizeC )
  $ clausesL cnf

empty_clauses cnf = filter nullC
  $ clausesL cnf

empty :: CNF
empty = CNF { clauses = DS.empty }

size :: CNF -> Int
size cnf = DS.size $ clauses cnf

variables :: CNF -> [ V ]
variables cnf = S.toList $ S.fromList $ do
  c <- clausesL cnf
  map variable $ literals c
  
clauses_for :: V -> CNF -> M.Map C Bool
clauses_for v cnf = M.fromList $ do
  cl <- clausesL cnf
  case get_value cl v of
    Nothing -> mzero
    Just b -> return (cl,b)

positive_clauses_for v cnf =
  M.filter id  $ clauses_for v cnf
negative_clauses_for v cnf =
  M.filter not $ clauses_for v cnf


units :: CNF -> [ Clause ]
units cnf = filter unit $ clausesL cnf

satisfied :: CNF -> Bool
satisfied cnf = 0 == size cnf

contradictory :: CNF -> Bool
contradictory cnf = any nullC $ clausesL cnf

add_clauses cls (CNF s) = CNF $ DS.union (DS.fromList cls) s

drop_variable :: V -> CNF -> CNF
drop_variable v cnf = CNF $ DS.fromList $ do
   cl <- clausesL cnf
   case get_value cl v of
     Nothing -> return cl
     Just b' -> mzero

assign (v,b) cnf = CNF $ DS.fromList $ do
   cl <- clausesL cnf
   case get_value cl v of
     Nothing -> return cl
     Just b' -> if b == b' then mzero
                else return $ cl `without` v
     
     
   
