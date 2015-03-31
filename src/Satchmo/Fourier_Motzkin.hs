{-# language TupleSections #-}
{-# language BangPatterns #-}

module Satchmo.Fourier_Motzkin where

import Satchmo.Form
import Satchmo.Data (Variable,variable,positive)

import qualified Data.Map.Strict as M
import qualified Data.EnumMap as E

import Control.Monad ( guard, when )
import Data.Monoid
import Data.List ( maximumBy, minimumBy )
import Data.Function (on)
import System.IO

type Solver = Form -> IO (Maybe (E.Map V Bool))

fomo :: Solver
fomo cnf = do
  -- hPutStr stderr $ show (size cnf) ++ ","
  -- print_info "fomo" cnf
  (   trivial
    $ unitprop
    $ eliminate 10
    $ branch ) cnf

print_info msg cnf = do
  hPutStrLn stderr $ unwords [ msg, show $ size cnf, "\n" ]
  -- hPutStrLn stderr $ show cnf ++ "\n"


trivial :: Solver -> Solver
trivial cont cnf = do
  -- print_info "trivial" cnf
  if satisfied cnf
     then return $ Just E.empty
     else if contradictory cnf
          then return $ Nothing
          else cont cnf

unitprop :: Solver -> Solver
unitprop cont f = do
  -- print_info "unitprop" f
  let punits = positive_units f
      nunits = negative_units f
      conflicting = not $ E.null $ E.intersection punits nunits
      units = E.union punits nunits
  if E.null units
    then cont f
    else do
      -- print ("units", units :: M.Map V Bool )
      if conflicting
         then do
           -- hPutStrLn stderr "conflict"
           return Nothing
         else do
           later <- fomo $ foldr assign f $ E.toList units
           return $ fmap ( E.union units ) later

eliminate :: Int -> Solver -> Solver
eliminate bound cont nf = do
  -- print_info "eliminate" nf
  let reductions = E.mapWithKey ( \ v () ->
        let pos = E.size $ positive_clauses_for v nf
            neg = E.size $ negative_clauses_for v nf
        in pos*neg - pos - neg ) $ variables nf 
      (v,c) = minimumBy (compare `on` snd)
            $ E.toList reductions
      pos = E.keys $ positive_clauses_for v nf
      neg = E.keys $ negative_clauses_for v nf
      -- TODO:check for duplicate clauses
      resolved = do
        cp <- map (get_clause nf) pos
        let cpv = cp `without` v
        cn <- map (get_clause nf) neg
        let cnv = cn `without` v
        guard $ E.intersection cpv cnv
             == E.intersection cnv cpv
        return $ E.union cpv cnv
  -- print ("v/c", v,c)
  -- print ("pos/neg", pos, neg)
  -- print ("resolved", resolved :: [M.Map V Bool ])

  if c > bound
    then cont nf
    else do
  
      let res = add_clauses resolved $ drop_variable v nf
      -- print res
      let reconstruct v m = Prelude.or $ do
            cp <- map (get_clause nf) pos 
            return $ Prelude.not $ Prelude.or $ do
              lit <- literals $ cp `without` v
              let v = E.findWithDefault False ( variable lit ) m
              return $ if positive lit then v else Prelude.not v 
      when False $ hPutStrLn stderr $ unwords
          [ "best resolution:", show v, "count", show c ]
      when False $ hPutStr stderr $ unwords
          [ "R", show v , show (size nf, size res) ]
   
      later <- fomo res
      return $ fmap
                    ( \ m -> E.insert v (reconstruct v m) m)
                    later

islongerthan k xs = not $ null $ drop k xs

branch cnf = do
  -- print_info "branch" cnf

  -- this gives nice results, but is costly:
  let stat :: M.Map (V,Bool) Double
      stat = M.fromListWith (+) $ do
        (c,()) <- E.toList $ clauses cnf
        let m = get_clause cnf c
        let w = -- 2 ^^ negate (M.size m)
              1 / fromIntegral (E.size m)
        (v,b) <- E.toList m        
        return ((v,b), w)
      ((v,p),w) = maximumBy (compare `on` snd)
                  $ M.toList stat
{-

  let (v,m) = maximumBy (compare `on` (M.size.snd)) 
        $ M.toList $ fore cnf
      p = M.size (M.filter id m) > M.size (M.filter not m)
-}

  -- hPutStr stderr $ unwords [ "D", show v, show p ]
  a <- fomo $ assign (v, p) cnf
  case a of
    Just m -> return $ Just $ E.insert v p m
    Nothing -> do
      -- hPutStr stderr $ unwords [ "D", show v, show $ not p ]
      b <- fomo $ assign (v, not p) cnf
      return $ fmap (E.insert v $ not p) b
