{-# language TypeFamilies #-}
{-# language FlexibleInstances #-}
{-# language LambdaCase #-}
{-# language BangPatterns #-}
{-# language GeneralizedNewtypeDeriving #-}

module Satchmo.Form

( Form, V, C -- abstract
, empty
, size
, variables, clauses, smallest_clauses, empty_clauses
, get_clause

, units, positive_units, negative_units
, clauses_for, positive_clauses_for, negative_clauses_for
, literals_for, positive_literals_for, negative_literals_for

, satisfied, contradictory
, add_clauses, add_clause
, drop_variable, add_variable
, assign
, descend_from
, Reason (..), Origin (..)

-- * clauses
, without, literals


, check_asserts
)

where

import Prelude 

import Satchmo.Data (literal, variable,positive, Literal,Clause)

import qualified Data.EnumMap as M
import qualified Data.EnumSet as S
import Data.List ( sortBy )
import Data.Function (on)
import Control.Monad ( guard )

-- this is only needed for testing the invariant
import qualified Data.Set as DS
import qualified Data.Map as DM

-- * performance critical (DON'T FORGET)

check_asserts = False


-- * data type and elementary ops

newtype V = V Int deriving (Enum, Show, Eq, Ord)
newtype C = C Int deriving (Enum, Show, Eq, Ord)

-- | should allow for efficient execution of these ops:
-- for variable p:
-- find the clauses where p occurs, with given polarity
-- for clause c:
-- find all variables that occur in c, with given polarity.
-- FIXME: there is too much data here (some components of this record type
-- contain the "(current) state" of the solver,
-- which is more than just a formula (as the name suggests).
-- TODO: document invariants for these extra components.
data Form  =
    Form { fore :: ! (M.Map V ( M.Map C Bool ))
         , next_var :: V
         , back :: ! (M.Map C ( M.Map V Bool ))
         , next_clause :: C
         , by_size :: ! (M.Map Int (S.Set C))
         , assignment :: ! (M.Map V Bool)
         , origin :: ! (M.Map C Origin) -- ^ why is the clause in the formula?
                     -- see @Origin@ for possible values.
             -- the default value is @Input@ (so we can start with an empty map)
         , reason :: ! (M.Map V Reason) -- ^ why is the variable assigned?
         , parent :: Maybe Form -- ^ immediate predecessor
         , root :: Form -- ^ ultimate ancestor.
           -- this is needed (?) for clause learning
           -- (we do resolution using clause from the root formula)
           -- FIXME: not exactly true if we do elimination in between.
           -- note: call @root@ exactly once. there is
           -- danger of infinite recursion since "root (root f) == root f)"
         }
  -- deriving Show

descend_from f g = g { parent = Just f , root = root f }

-- | the origin of clauses. Note: each clause has a number (of type @C@),
-- these numbers don't change. (new clauses get fresh numbers).
-- for each time: the current meaning (set of literals) in clause with nr. c
-- is a substitution instance (a subset of literals) of c's meaning at time of creation.
--  TODO: expect to add arguments to constructors
data Origin = Input -- ^ this clause is an element of the input CNF
            | Resolved C C -- ^ this clause appeared by resolution (elimination)
            | Learnt -- ^ this clause was learnt
    deriving ( Eq, Ord, Show )

-- | the reason for the current value of a variable.
data Reason = Decided -- ^ the value was assigned when entering a subtree
            | Propagated C -- ^ the value was computed by unit propagation, using clause c
    deriving ( Eq, Ord, Show )
             

-- | this function should never be called because it walks the complete formula
variables :: Form -> M.Map V ()
variables f = M.map (const ()) $ fore f

-- | this function should never be called because it walks the complete formula
clauses :: Form -> M.Map C ()
clauses f = M.map (const ()) $ back f

smallest_clauses :: Int -> Form -> M.Map C ()
smallest_clauses s f = M.fromList $ take s $ do
  let (lo,hi) = M.split (s+1) $ by_size f
  m <- M.elems lo
  c <- S.toList m
  return (c, ())

get_clause f c =
  M.findWithDefault (error "get_clause") c $ back f 

-- | check the structural invariants.
-- raise error (with msg) if they do not hold.
checked :: Show a
  => String -> (a -> Form -> Form) -> (a -> Form -> Form)
checked =  if check_asserts then checked_ else unchecked_
       
unchecked_ msg fun arg f = fun arg f

checked_ msg fun arg f = id
  $ invariant (unwords [ msg, show arg, "(output)" ]) 
  $ fun arg
  $ invariant (unwords [ msg, show arg, "(input)" ]) 
  $ f 

invariant :: String -> Form -> Form
invariant msg = invariant_by_size msg
              . invariant_back_and_fore msg
              . invariant_for_assignment msg


invariant_for_assignment :: String -> Form -> Form
invariant_for_assignment msg f =
  let whine s = error $ unlines [ msg
         , "invariant_for_assignment violated. " ++ s
         , "variables " ++ show (fore f)
         , "assigned " ++ show (assignment f)
         , "reason " ++ show (reason f)
         , "formula " ++ show (toList f)           
         ]
      both = M.intersection (fore f) (assignment f)
  in  if not $ M.null both
      then whine "assigned variables occur in formula"
      else if M.keys (assignment f) /= M.keys ( reason f)
           then whine "M.keys assigned /= M.keys reason"
           else f

invariant_by_size msg f =   
  let actual = DM.filter (not . DS.null)
             $ DM.fromListWith DS.union $ do
        (c,m) <- M.toList $ back f
        return (M.size m, DS.singleton c)
      indexed = DM.filter (not . DS.null)
              $ DM.fromListWith DS.union $ do
        (s,cs) <- M.toList $ by_size f
        return (s, DS.fromList $ S.toList cs)
      whine = unlines [ msg
          , "invariant_by_size violated"
          , "actual " ++ show actual
          , "indexed " ++ show indexed
          , "formula " ++ show (toList f)
          ]
  in  if actual == indexed 
      then f else error whine

invariant_back_and_fore msg f =   
  let forward = DS.fromList $ do
        (v,m) <- M.toList $ fore f
        (c,b) <- M.toList m
        return (v,b,c)
      backward = DS.fromList $ do
        (c,m) <- M.toList $ back f
        (v,b) <- M.toList m
        return (v,b,c)
      f_not_b = DS.difference forward backward
      b_not_f = DS.difference backward forward
      whine = unlines [ msg
                      , "invariant_back_and_fore violated"
          , "missing clauses " ++ show f_not_b
          , "missing variabl " ++ show b_not_f
          , "fore " ++ show (fore f)
          , "back " ++ show (back f)
          , "formula " ++ show (toList f)
          ]
  in  if DS.null f_not_b && DS.null b_not_f
      then f else error whine

instance Show Form where
  show f = unlines [ show $ fore f, show $ back f
                   , show $ toList f ]

size f = M.size $ back f -- number of clauses

toList f = -- sortBy (compare `on` map abs) $
           do
  (k,cl) <- M.toList $ back f
  return $ (k, do
    (V v,b) <- M.toList cl
    return $ if b then v else negate v )

empty :: Form
empty = f where f = Form {
    fore = M.empty
  , next_var = V 1
  , back = M.empty
  , next_clause = C 1
  , by_size = M.empty
  , assignment = M.empty
  , reason = M.empty
  , origin = M.empty
  , parent = Nothing
  , root = f
  }

descend f g = g { parent = Just f, root = root f }

-- * ops that are useful for the solver

clauses_for :: V -> Form -> M.Map C Bool
clauses_for v f = M.findWithDefault M.empty v $ fore f

-- | FIXME: calling M.filter here is bad for performance
positive_clauses_for v f = M.filter id  $ clauses_for v f
negative_clauses_for v f = M.filter not $ clauses_for v f

literals_for :: C -> Form -> M.Map V Bool
literals_for c f = M.findWithDefault M.empty c $ back f

positive_literals_for c f = M.filter id  $ literals_for c f
negative_literals_for c f = M.filter not $ literals_for c f

units f = M.findWithDefault S.empty 1 $ by_size f

polar_units :: Bool -> Form -> M.Map V (Bool, C)
polar_units p f = M.fromList $ do
  c <- S.toList $ units f
  let m = back f M.! c
  let (v,b) = M.findMin m
  guard $ p == b
  return (v,(b,c))

-- | for the unit clauses with positive literals, compute the clause numbers
positive_units = M.map snd . polar_units True

-- | for the unit clauses with negative literals, compute the clause numbers
negative_units = M.map snd . polar_units False

without clause  v = M.delete v clause

literals cl = map (\(V v,b) -> literal b v ) $ M.toList cl

-- | some empty clause
contradictory :: Form -> Bool
contradictory f = not $ S.null $ empty_clauses f

empty_clauses :: Form -> S.Set C
empty_clauses f =  M.findWithDefault S.empty 0 $ by_size f

-- | no clauses at all
satisfied :: Form -> Bool
satisfied f = M.null $ back f

-- | note: for efficiency, should return the set of
-- clauses that were changed (instead of all)
assign :: Reason -> (V, Bool) -> Form -> Form
assign re = checked ( unwords [ "assign", show re ] ) $ \ (v, b) f ->
  let cpos = M.filter (==b) $ fore f M.! v
      cneg = M.filter (/=b) $ fore f M.! v
      g = foldr drop_clause f (M.keys cpos)
      back' = foldr ( \ c m -> M.adjust (M.delete v) c m ) (back g) (M.keys cneg)
  in  g { fore = M.delete v $ fore g
        , back = back'
        , by_size = foldr ( \ c b ->
              let new = M.size $ back' M.! c
                  old = succ new
              in M.alter ( Just . \ case
                      Nothing -> S.singleton c
                      Just s -> S.insert c s ) new
                 $ M.adjust ( S.delete c ) old
                 $ b
                 ) (by_size g) (M.keys cneg)
        , assignment = M.insert v b $ assignment g
        , reason = M.insert v re $ reason g
        }


-- | new clauses that refer to existing variables
add_clauses :: [ (M.Map V Bool, Origin) ] -> Form -> Form
add_clauses = checked "add_clauses" $ \ cls f ->
  foldr ( \ (cl,o) f -> add_clause o
          ( map (\(V v,b) -> literal b v) $ M.toList cl ) f )
        f cls

-- | drop this clause (and all refs to it)
drop_clause :: C -> Form -> Form
drop_clause = checked "drop_clause" $
   \ c f ->
   let m = back f M.! c in
  f { fore = foldr ( \ v m -> M.adjust (M.delete c) v m )
        (fore f) (M.keys m )
    , back = M.delete c $ back f
    , by_size = M.adjust ( S.delete c ) (M.size m) $ by_size f
    }

-- | drop this variable and all clauses where it occurs.
drop_variable :: V -> Form -> Form
drop_variable = checked "drop_variable" $ \ v f ->
  drop_variable_only v 
  $ foldr drop_clause f ( M.keys $ fore f M.! v )
    
drop_variable_only =  checked "drop_variable_only" $
  \ v f ->
      f { fore = M.delete v $ fore f }


-- * ops for building the formula

add_variable :: Form -> (Form, V)
add_variable f =
  let V v = next_var f
  in  ( f { fore = M.insert v M.empty $ fore f
          , next_var = succ $ next_var f
          } , V v )

-- | clause and variable must already exist
add_edge :: (V,Bool,C) -> Form -> Form
add_edge = checked "add_edge" $ \ (v,b,c) f ->
  let m = back f M.! c in
  f { fore = M.adjust ( M.insert c b ) v $ fore f
    , back = M.adjust ( M.insert v b ) c $ back f
    , by_size = M.alter ( Just . \ case
         Nothing -> S.singleton c
         Just s -> S.insert c s ) (succ $ M.size m)
                $ M.adjust (S.delete c) (M.size m)
                $ by_size f
    }

add_clause :: Origin -> [Literal] -> Form -> Form
add_clause orig = checked (unwords [ "add_clause", show orig ]) $ \ cl f ->
  let c = next_clause f
      g = foldr ( \ l f ->
            add_edge (V $ variable l,positive l,c) f)
          -- following is important for adding the empty clause
          -- FIXME which should be handled specially
          ( f { back = M.insert c M.empty $ back f
              , by_size = M.alter ( \ m -> Just $ case m of
                                       Nothing -> S.singleton c
                                       Just s -> S.insert c s ) 0 $ by_size f
              } )
          cl
  in  g { next_clause = succ $ next_clause g
        , origin = case orig of
            Input -> origin g
            _ -> M.insert c orig $ origin g
        }
    
