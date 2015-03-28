{-# language TupleSections #-}

module Satchmo.Fourier_Motzkin where

import Satchmo.Graph
import Satchmo.Data (Variable,variable,positive)

import qualified Data.EnumMap as M
import qualified Data.Map.Strict as DM

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

getm msg m k = M.findWithDefault (error msg) k m

eliminate :: Solver -> Solver
eliminate cont nf = do
  print_info "eliminate" nf
  let reductions = M.map ( \ m ->
        let pos = length $ filter snd $ M.toList m
            neg = M.size m - pos
        in pos*neg - pos - neg ) $ fore nf
      (v,c) = minimumBy (compare `on` snd)
            $ M.toList reductions
      m = fore nf M.! v
      pos = map fst $ filter snd       $ M.toList m
      neg = map fst $ filter (not.snd) $ M.toList m
      -- TODO:check for duplicate clauses
      resolved = do
        cp <- map (back nf M.! ) pos
        let cpv = cp `without` v
        cn <- map (back nf M.! ) neg
        let cnv = cn `without` v
        guard $ M.intersection cpv cnv
             == M.intersection cnv cpv
        return $ M.union cpv cnv
  print ("v/c", v,c)
  print ("pos/neg", pos, neg)
  print ("resolved", resolved :: [M.Map V Bool ])
  let res = add_clauses resolved
          $ drop_variable v nf
  print res
  
  let reconstruct v m = Prelude.or $ do
        cp <- map (back nf M.!) pos 
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
  let stat = DM.fromListWith (+) $ do
        c <- clauses cnf
        let s = M.size c
        let w = 1 / fromIntegral s
        (v,p) <- M.toList c
        return ((v,p), w)
      ((v,p),w) = maximumBy (compare `on` snd)
                  $ DM.toList stat
  hPutStr stderr $ unwords [ "D", show v, show p ]
  a <- fomo $ assign (v, p) cnf
  case a of
    Just m -> return $ Just $ M.insert v p m
    Nothing -> do
      hPutStr stderr $ unwords [ "D", show v, show $ not p ]
      b <- fomo $ assign (v, not p) cnf
      return $ fmap (M.insert v $ not p) b
