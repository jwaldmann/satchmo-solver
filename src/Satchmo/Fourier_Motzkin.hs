-- | this module contains building blocks for a solver
-- that does variable elimination (Fourier-Motzkin),
-- DPLL and CDCL. For a satisfiable formula,
-- the solver  will produce an assignment.
-- For an unsatisfiable formula,
-- the solver will produce a proof
-- by reverse unit propagation (?)

{-# language TupleSections #-}
{-# language BangPatterns #-}

module Satchmo.Fourier_Motzkin where

import Satchmo.Form 
import Satchmo.Data (Variable,variable,positive)

import qualified Data.Map.Strict as M
import qualified Data.EnumMap as E
import qualified Data.EnumSet as S

import Control.Monad ( guard, when, void, forM )
import Data.Monoid
import Data.List ( maximumBy, minimumBy )
import Data.Function (on)
import System.IO

type Assignment = E.Map V Bool
type RUP = [Clause]

data Unsat =
     Unsat { rup :: RUP
           , learnt :: [Clause]
           }
     deriving Show

type Result = Either Unsat Assignment
type Solver = Form -> IO Result

fomo :: Solver
fomo cnf = do
  print_info "fomo" cnf
  (   trivial
    $ unitprop
    --  $ eliminate 10
    $ branch ) cnf

logging = True
conflict_logging = True

print_info msg cnf = when logging $ do
  hPutStrLn stderr $ unwords [ msg, show $ size cnf, "\n" ]
  hPutStrLn stderr $ show cnf ++ "\n"

trivial :: Solver -> Solver
trivial cont cnf = do
  print_info "trivial" cnf
  if satisfied cnf
     then return $ Right E.empty
     else if contradictory cnf
          then do
            when conflict_logging $ do
              hPutStrLn stderr $ unlines [ "empty clauses", show (empty_clauses cnf) ]
            void $ forM ( S.toList $ empty_clauses cnf ) $ \ c ->
              learn_from cnf c
            error "abort here (for debugging)"  
            return $ Left
               $ Unsat { rup = [E.empty], learnt = [] }
          else cont cnf

-- | start with conflict clause. repeatedly resolve
-- with the clause that lead (by unit propagation)
-- to the most recent assignment (to a literal in the clause).
learn_from :: Form -> C -> IO Clause
learn_from f c = do
  let start = get_clause (root f) c
      -- invariant: all the variables in the clause are currently assigned.
      -- proof: we start with a conflict clause,
      -- we only use clauses that were used in unit prop.
      most_recently_assigned_variable cl =
        maximumBy (compare `on` (get_assigned f)) $ E.keys cl
      go cl = do
        let mora = most_recently_assigned_variable cl
        hPutStrLn stderr $ unlines
          [ unwords [ "current clause", show cl ]
          , unwords [ "mora", show mora, show $ get_reason f mora ]
          ]
        case get_reason f mora of
              Decided -> do
                hPutStrLn stderr "done"
                return cl
              Propagated ucl -> do  
                let cl' = get_clause (root f) ucl
                hPutStrLn stderr $ unwords
                   [ "propagating clause was" , show cl' ]
                go $ resolve mora cl cl'
  go start

-- | resolve for variable v.
resolve v ncl pcl =
  let ncl' = ncl `without` v
      pcl' = pcl `without` v
  in  if ncl E.! v /= pcl E.! v
      then E.unionWith (\ l r -> if l /= r then error "conflict in resolve?" else l ) ncl' pcl'
      else  error $ unlines [ "resolve", show v, show ncl, show pcl ]

unitprop :: Solver -> Solver
unitprop cont f = do
  print_info "unitprop" f
  case S.toList $ units f of
    [] -> cont f
    c : _ -> do
      let [(v,b)] = E.toList $ get_clause f c
      when logging $ print ("unit:", c, (v,b))
      later <- fomo $ descend_from f
                    $ assign (Propagated c) (v,b) f
      return $ case later of
             Left u -> Left u
             Right m -> Right $ E.insert v b m

eliminate :: Int -> Solver -> Solver
eliminate bound cont nf = do
  print_info "eliminate" nf
  let -- this is expensive (visits all variables and clauses) :
      reductions = E.mapWithKey ( \ v () ->
        let pos = E.size $ positive_clauses_for v nf
            neg = E.size $ negative_clauses_for v nf
        in pos*neg - pos - neg ) $ variables nf 
      (v,c) = minimumBy (compare `on` snd)
            $ E.toList reductions
      pos = E.keys $ positive_clauses_for v nf
      neg = E.keys $ negative_clauses_for v nf

      resolved = M.fromList $ do
        p <- pos
        let cp = get_clause nf p
        let cpv = cp `without` v
        n <- neg
        let cn = get_clause nf n
        let cnv = cn `without` v
        guard $ E.intersection cpv cnv
             == E.intersection cnv cpv
        return ( E.union cpv cnv, Resolved p n )
  -- print ("v/c", v,c)
  -- print ("pos/neg", pos, neg)
  when logging $ do print ("resolved", resolved :: M.Map (E.Map V Bool) Origin )

  if c > bound
    then cont nf
    else do

      -- FIXME: need to add info on the origin of the fresh clauses
      let res = add_clauses (M.toList resolved) $ drop_variable v nf
      -- print res
      let reconstruct v m = Prelude.or $ do
            cp <- map (get_clause nf) pos 
            return $ Prelude.not $ Prelude.or $ do
              lit <- literals $ cp `without` v
              let v = E.findWithDefault False ( variable lit ) m
              return $ if positive lit then v else Prelude.not v 
      when logging $ hPutStrLn stderr $ unwords
          [ "best resolution:", show v, "count", show c ]
      when logging $ hPutStr stderr $ unwords
          [ "R", show v , show (size nf, size res) ]
   
      later <- fomo res
      return $ case later of
        Left rup -> Left rup -- FIXME
        Right m -> Right $ E.insert v (reconstruct v m) m

islongerthan k xs = not $ null $ drop k xs

branch cnf = do
  print_info "branch" cnf

  let stat :: M.Map (V,Bool) Double
      stat = M.fromListWith (+) $ do
        
        (c,()) <- E.toList $ smallest_clauses 1000 cnf
        let m = get_clause cnf c
        let w = -- 2 ^^ negate (M.size m)
              1 / fromIntegral (E.size m)
        (v,b) <- E.toList m        
        return ((v,b), w)
      ((v,p),w) = maximumBy (compare `on` snd)
                  $ M.toList stat


  when logging $ do hPutStr stderr $ unwords [ "D", show v, show p ]
  a <- fomo $ descend_from cnf $ assign Decided (v, p) cnf
  case a of
    Right m -> return $ Right $ E.insert v p m
    Left ul -> do
      when logging $ do hPutStr stderr $ unwords [ "D", show v, show $ not p ]
      b <- fomo $ descend_from cnf $ assign Decided (v, not p) cnf
      case b of
        Right m -> return $ Right $ E.insert v (not p) m
        Left ur -> return $ Left
          $ Unsat { rup =  E.empty
                         : map (E.insert v       p) (rup ul)
                        ++ map (E.insert v $ not p) (rup ur)
                  , learnt = []
                  }
