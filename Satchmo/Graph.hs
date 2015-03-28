{-# language TypeFamilies #-}
{-# language FlexibleInstances #-}
{-# language LambdaCase #-}
{-# language BangPatterns #-}
{-# language GeneralizedNewtypeDeriving #-}

module Satchmo.Graph

where

import Prelude 

import Satchmo.Data (literal, variable,positive, Literal)

import qualified Data.EnumMap as M
import Data.List ( sortBy )
import Data.Function (on)

-- * data type and elementary ops

newtype V = V Int deriving (Enum, Show, Eq, Ord)
newtype C = C Int deriving (Enum, Show, Eq, Ord)

-- | should allow for efficient execution of these ops:
-- for variable p:
-- find the clauses where p occurs, with given polarity
-- for clause c:
-- find all variables that occur in c, with given polarity.
data Form  =
    Form { fore :: ! (M.Map V ( M.Map C Bool ))
         , next_var :: V
         , back :: ! (M.Map C ( M.Map V Bool ))
         , next_clause :: C
         }
  -- deriving Show

instance Show Form where
  show f = unlines [ show $ fore f, show $ back f
                   , show $ dimacs f ]

size f = M.size $ back f -- number of clauses

dimacs f = -- sortBy (compare `on` map abs) $
           do
  (k,cl) <- M.toList $ back f
  return $ (k, do
    (V v,b) <- M.toList cl
    return $ if b then v else negate v )

cnf0 :: Form
cnf0 = Form
  { fore = M.empty
  , next_var = V 1
  , back = M.empty
  , next_clause = C 1
  }

-- * ops that are useful for the solver

without clause  v = M.delete v clause

clauses f = M.elems $ back f
literals cl =
  map (\(v,b) -> literal b v ) $ M.toList cl

-- | some empty clause
contradictory :: Form -> Bool
contradictory f =
  M.fold ( \ v m -> M.null v || m ) False $ back f

-- | no clauses at all
satisfied :: Form -> Bool
satisfied f = M.null $ back f

-- | all unit clauses
unit_clauses :: Form -> [(V,Bool)]
unit_clauses f = M.fold
   ( \ v m -> case M.toList v of
        [ (k,b) ] -> (k,b) : m
        _ -> m ) [] $ back f

-- | note: for efficiency, should return the set of
-- clauses that were changed (instead of all)
assign :: (V, Bool) -> Form -> Form
assign (V v, b) f =
  f { fore = M.delete v $ fore f
    , back =
       let cls = M.findWithDefault M.empty v $ fore f
           drop_sat = M.difference (back f)
                    $ M.filter id cls
       in  foldr ( \ (c,False) b ->
                    M.adjust (M.delete v) c b )
           drop_sat
           ( filter (Prelude.not . snd) $ M.toList cls )
    }


-- | new clauses that refer to existing variables
add_clauses cls f =
  foldr ( \ cl f -> add_clause f
                    $ map (\(v,b) -> literal b v)
                    $ M.toList cl ) f cls

-- | drop this clause (and all refs to it)
drop_clause c f =
  f { fore = foldr ( \ (v,b) m -> M.delete v m )
        (fore f)
        (M.toList $ M.findWithDefault M.empty c $ back f)
    , back = M.delete c $ back f
    }

-- | drop this variable and all clauses where it occurs.
drop_variable v f =
  foldr drop_clause 
    ( f { fore = M.delete v $ fore f
        , back =
          let occ = fore f M.! v
          in  M.difference (back f) occ
        }
    ) ( M.keys $ fore f M.! v )
    


-- * ops for building the formula


add_variable :: Form -> (Form, V)
add_variable f =
  let V v = next_var f
  in  ( f { fore = M.insert v M.empty $ fore f
          , next_var = succ $ next_var f
          } , V v )

add_edge :: Form -> (V,Bool,C) -> Form
add_edge f (v, b, c) =
  f { fore = M.alter ( \ case 
         Nothing -> Just $ M.singleton c b
         Just m -> Just $ M.insert c b m ) v $ fore f
    , back = M.alter ( \ case
         Nothing -> Just $ M.singleton v b
         Just m -> Just $ M.insert v b m ) c $ back f
    }

add_clause :: Form -> [Literal] -> Form
add_clause f cl =
  let c = next_clause f
      g = foldl ( \ f l ->
            add_edge f (V $ variable l,positive l,c)) f cl
  in  g { next_clause = succ $ next_clause g }
    

{-

instance Monoid CNF where
  mempty = CNF S.empty
  mappend (CNF a) (CNF b) = CNF $ S.delete CTrue $ S.union a b

foldr f x (CNF s) = F.foldr f x s
filter p (CNF s) = CNF $ S.filter p s

size (CNF s) = S.size s
                   
clauses (CNF s) = F.toList s

instance Show CNF  where
    show cnf = unlines $ map show $ clauses cnf

cnf :: [ Clause ] -> CNF 
cnf cs = CNF $ S.fromList $ Prelude.filter ( /= CTrue) cs

singleton c = CNF $ S.singleton c

assign :: Variable -> Bool -> CNF -> CNF
assign v p (CNF s) = ( F.foldMap $ \ c -> singleton $ case c of
       CTrue -> CTrue
       Clause m -> case M.lookup v m of
         Nothing -> Clause m
         Just q ->
           if p == q then CTrue
           else Clause $ M.delete v m ) s

data Clause = Clause  ! ( M.Map Variable Bool )  | CTrue
   deriving ( Eq, Ord )

literals :: Clause ->  [ Literal ]
literals c = case c of
  Clause m -> map ( \ (v,p) -> literal p v ) $ M.toList m

instance Monoid Clause where
  mempty = Clause M.empty
  mappend c1 c2 = case c1 of
    CTrue -> CTrue
    Clause m1 -> case c2 of
      CTrue -> CTrue
      Clause m2 ->
        let common = M.intersection m1 m2
        in  if M.isSubmapOf common m1 && M.isSubmapOf common m2
            then Clause $ M.union m1 m2
            else CTrue

instance Show ( Clause ) where
  show c = case c of
    CTrue -> "# True"
    Clause m -> unwords ( map show (literals c) ++ [ "0" ] )

clause ::  [ Literal ] -> Clause 
clause ls = Prelude.foldr
            ( \ l c -> case c of
                 CTrue -> CTrue           
                 Clause m -> case M.lookup (variable l) m of
                   Nothing -> Clause $ M.insert (variable l) (positive l) m
                   Just p -> if p == positive l then Clause m else CTrue
            ) mempty ls

without c w = case c of
  -- CTrue -> CTrue -- ?
  Clause m -> Clause $ M.filterWithKey ( \ v p -> w /= v ) m

-}
