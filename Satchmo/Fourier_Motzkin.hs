{-# language TupleSections #-}

module Satchmo.Fourier_Motzkin where

import Satchmo.Graph
import Satchmo.Data (Variable,variable,positive)

import qualified Data.IntMap as IM
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Control.Monad ( guard )
import Data.Monoid
import Data.List ( maximumBy, minimumBy )
import Data.Function (on)
import System.IO

type Solver = Form -> IO (Maybe (M.Map Variable Bool))

fomo :: Solver
fomo cnf = do
  print_info "fomo" cnf
  ( trivial $  eliminate $ branch ) cnf

print_info msg cnf = do
  hPutStrLn stderr $ unwords [ msg, show $ size cnf, "\n" ]
  hPutStrLn stderr $ show cnf ++ "\n"


trivial :: Solver -> Solver
trivial cont cnf = do
  print_info "trivial" cnf
  if satisfied cnf
     then return $ Just M.empty
     else if contradictory cnf
          then return $ Nothing
          else cont cnf

disjoint s t = S.null $ S.intersection s t

eliminate :: Solver -> Solver
eliminate cont nf = do
  print_info "eliminate" nf
  let reductions = IM.map ( \ m ->
        let pos = length $ filter snd $ IM.toList m
            neg = IM.size m - pos
        in pos*neg - pos - neg ) $ fore nf
      (v,c) = minimumBy (compare `on` snd)
            $ IM.toList reductions
      m = fore nf IM.! v
      pos = map fst $ filter snd       $ IM.toList m
      neg = map fst $ filter (not.snd) $ IM.toList m
      -- TODO:check for duplicate clauses
      resolved = do
        cp <- map (back nf IM.! ) pos
        let cpv = cp `without` v
        cn <- map (back nf IM.! ) neg
        let cnv = cn `without` v
        guard $ IM.intersection cpv cnv
             == IM.intersection cnv cpv
        return $ IM.union cpv cnv

  let res = add_clauses resolved $ drop_variable (V v) nf

  let reconstruct v m = Prelude.or $ do
        cp <- map (back nf IM.!) pos 
        return $ Prelude.not $ Prelude.or $ do
          lit <- literals $ cp `without` v
          let v = M.findWithDefault False ( variable lit ) m
          return $ if positive lit then v else Prelude.not v 

  hPutStrLn stderr $ unwords
    [ "best resolution:", show v, "count", show c ]
  hPutStr stderr $ unwords
    [ "R", show v , show (size nf, size res) ]
   
  later <- fomo res
  return $ fmap
                    ( \ m -> M.insert v (reconstruct v m) m)
                    later

branch cnf = do
  print_info "branch" cnf
  let stat = M.fromListWith (+) $ do
        c <- clauses cnf
        let ls = literals c
        let w = 1 / fromIntegral (length ls)
        l <- ls
        return ((variable l,positive l), w)
      ((v,p),w) = maximumBy (compare `on` snd) $ M.toList stat
  hPutStr stderr $ unwords [ "D", show v, show p ]
  a <- fomo $ assign (V v, p) cnf
  case a of
    Just m -> return $ Just $ M.insert v p m
    Nothing -> do
      hPutStr stderr $ unwords [ "D", show v, show $ not p ]
      b <- fomo $ assign (V v, not p) cnf
      return $ fmap (M.insert v $ not p) b
        
