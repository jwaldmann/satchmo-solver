{-# language TypeFamilies #-}
{-# language FlexibleInstances #-}
{-# language LambdaCase #-}
{-# language BangPatterns #-}

module Satchmo.Graph

where

import Prelude 

import Satchmo.Data (literal, variable,positive, Literal)

import qualified Data.IntMap as IM
import Data.List ( sortBy )
import Data.Function (on)

-- * data type and elementary ops
  
-- | should allow for efficient execution of these ops:
-- for variable p:
-- find the clauses where p occurs, with given polarity
-- for clause c:
-- find all variables that occur in c, with given polarity.
data Form  =
    Form { fore :: ! (IM.IntMap ( IM.IntMap Bool ))
        , back :: ! (IM.IntMap ( IM.IntMap Bool ))
        }
  -- deriving Show

instance Show Form where show = show . dimacs

size f = IM.size $ back f -- number of clauses

dimacs f = sortBy (compare `on` map abs) $ do
  (_,cl) <- IM.toList $ back f
  return $ do
    (v,b) <- IM.toList cl
    return $ if b then v else negate v

cnf0 :: Form
cnf0 = Form
  { fore = IM.empty
  , back = IM.empty
  }

-- * ops that are useful for the solver

without clause  v = IM.delete v clause

clauses f = IM.elems $ back f
literals cl =
  map (\(v,b) -> literal b v ) $ IM.toList cl

-- | some empty clause
contradictory :: Form -> Bool
contradictory f =
  IM.fold ( \ v m -> IM.null v || m ) False $ back f

-- | no clauses at all
satisfied :: Form -> Bool
satisfied f = IM.null $ back f

-- | all unit clauses
unit_clauses :: Form -> [(V,Bool)]
unit_clauses f = IM.fold
   ( \ v m -> case IM.toList v of
        [ (k,b) ] -> (V k,b) : m
        _ -> m ) [] $ back f

-- | note: for efficiency, should return the set of
-- clauses that were changed (instead of all)
assign :: (V, Bool) -> Form -> Form
assign (V v, b) f =
  f { fore = IM.delete v $ fore f
    , back =
       let cls = IM.findWithDefault IM.empty v $ fore f
           drop_sat = IM.difference (back f)
                    $ IM.filter id cls
       in  foldr ( \ (c,False) b ->
                    IM.adjust (IM.delete v) c b )
           drop_sat
           ( filter (Prelude.not . snd) $ IM.toList cls )
    }


-- | new clauses that refer to existing variables
add_clauses cls f =
  foldr ( \ cl f -> add_clause f
                    $ map (\(v,b) -> literal b v)
                    $ IM.toList cl ) f cls

-- | drop this variable and all clauses where it occurs
drop_variable (V v) f = 
  f { fore = IM.delete v $ fore f
    , back =
         let occ = fore f IM.! v
         in  IM.difference (back f) occ
    }

-- * ops for building the formula

newtype V = V Int
newtype C = C Int

add_variable :: Form -> (Form, V)
add_variable f =
  let v = IM.size $ fore f
  in  ( f { fore = IM.insert v IM.empty $ fore f } , V v )

fresh_clause :: Form -> C
fresh_clause f = C $ IM.size $ back f

add_edge :: Form -> (V,Bool,C) -> Form
add_edge f (V v, b, C c) =
  f { fore = IM.alter ( \ case 
         Nothing -> Just $ IM.singleton c b
         Just m -> Just $ IM.insert c b m ) v $ fore f
    , back = IM.alter ( \ case
         Nothing -> Just $ IM.singleton v b
         Just m -> Just $ IM.insert v b m ) c $ back f
    }

add_clause :: Form -> [Literal] -> Form
add_clause f cl =
  let c = fresh_clause f
  in  foldl ( \ f l ->
            add_edge f (V $ variable l,positive l,c)) f cl

    

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
