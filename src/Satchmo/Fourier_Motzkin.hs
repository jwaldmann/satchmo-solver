-- | this module contains building blocks for a solver
-- that does variable elimination (Fourier-Motzkin),
-- DPLL and CDCL. For a satisfiable formula,
-- the solver  will produce an assignment.
-- For an unsatisfiable formula,
-- the solver will produce a proof
-- by reverse unit propagation (?)

{-# language TupleSections #-}
{-# language BangPatterns #-}

module Satchmo.Fourier_Motzkin

( fomo, initial, Unsat (..) )

where

import Satchmo.State

-- import Satchmo.Data (Variable,variable,positive)

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
type Solver = State -> IO Result

fomo :: Solver
fomo s = do
  print_info "fomo" s
  (   check_sat
    -- $ backtrack_if_unsat
    $ backjump_if_unsat   
    $ unitprop
    --  $ eliminate 10
    -- $ branch
    $ nobranch
    ) s

logging = False
conflict_logging = True
nobranch_logging = False

print_info msg s = when logging $ do
  hPutStrLn stderr $ unlines [ msg, show s ]

check_sat cont s = do
  print_info "check_sat" s
  if satisfied $ current s
     then return $ Right $ the_assignment s
     else cont s

backtrack_if_unsat cont s = do
  print_info "backtrack_if_unsat" s
  if contradictory $ current s
    then do
      return $ Left $ Unsat { rup = [emptyC], learnt = [] }
    else cont s
  
backjump_if_unsat :: Solver -> Solver
backjump_if_unsat cont s = do
  print_info "backjump_if_unsat" s
  case empty_clauses s of
       [] -> cont s
       e : _ -> do
         when conflict_logging $ do
           hPutStrLn stderr $ show s
         (cl,lvl,mora) <- learn_from s e
         let b = not $ get_assignment s mora
         when conflict_logging $ hPutStrLn stderr $ unlines
             [ "backjump from " ++ show (get_level s)
             , "         to   " ++ show lvl
             , "    and learn " ++ show cl
             ]
         fomo $ learn_and_backjump s (cl,lvl)


-- | start with conflict clause. repeatedly resolve
-- with the clause that lead (by unit propagation)
-- to the most recent assignment (to a literal in the clause).
-- return the second highest decision level
-- of the learnt clause (this is the target for the backjump)
-- and the most recently assigned variable in the learnt clause
-- (the opposite assignment would be asserted by
-- unit propagation)
learn_from :: State -> C -> IO (Clause, Level, V)
learn_from s c = do
  let start = get_clause (root s) c
      -- invariant: all the variables in the clause are currently assigned.
      -- proof: we start with a conflict clause,
      -- we only use clauses that were used in unit prop.
      most_recently_assigned_variable cl =
        maximumBy (compare `on` (get_assigned s))
         $ map variable $ literals cl
      go cl = do
        let mora = most_recently_assigned_variable cl
        when logging $ hPutStrLn stderr $ unlines
          [ unwords [ "current clause", show cl ]
          , unwords [ "mora", show mora, show $ get_reason s mora ]
          ]
        case get_reason s mora of
              Decided -> do
                let lvl = maximum $ do
                      l <- literals cl
                      let v = variable l
                      guard $ v /= mora
                      return $ get_decision_level s v
                when logging $ hPutStrLn stderr $ unwords
                  [ "done", "mora", show mora, show lvl ]
                return (cl, lvl, mora)
              Propagated ucl -> do  
                let cl' = get_clause (root s) ucl
                when logging $ hPutStrLn stderr $ unwords
                   [ "propagating clause was" , show cl' ]
                go $ resolve mora cl cl'
  go start

-- | resolve for variable v.
resolve v ncl pcl =
  let ncl' = ncl `without` v
      pcl' = pcl `without` v
  in  if get_value ncl v /= get_value pcl v
      then unionC ncl' pcl'
      else  error $ unlines [ "resolve", show v, show ncl, show pcl ]

unitprop :: Solver -> Solver
unitprop cont s = do
  print_info "unitprop" s
  let f = current s
  case unit_clauses s of
    [] -> cont s
    c : _ -> do
      let (v,b) = get_unit_clause s c
      when logging $ print ("unit:", c, (v,b))
      fomo $ descend_from s
                    $ assign (Propagated c) (v,b) s

eliminate :: Int -> Solver -> Solver
eliminate bound cont s = do
  print_info "eliminate" s  
  let nf = current s
      -- this is expensive (visits all variables and clauses) :
      reductions = map ( \ v  ->
        let pos = M.size $ positive_clauses_for v nf
            neg = M.size $ negative_clauses_for v nf
        in (v,pos*neg - pos - neg ) ) $ variables nf 
      (v,c) = minimumBy (compare `on` snd) reductions
      pos :: [C]        
      pos = M.keys $ positive_clauses_for v nf
      neg :: [C]
      neg = M.keys $ negative_clauses_for v nf

      resolved :: M.Map Clause Origin
      resolved = M.fromList $ do
        p <- pos
        let cp = get_clause nf p
        let cpv = cp `without` v
        n <- neg
        let cn = get_clause nf n
        let cnv = cn `without` v
        guard $ compatibleC cpv cnv
        return ( unionC cpv cnv, Resolved p n )
  -- print ("v/c", v,c)
  -- print ("pos/neg", pos, neg)
  when logging $ do print ("resolved", resolved)

  if c > bound
    then cont s
    else do

      -- FIXME: need to add info on the origin of the fresh clauses
      let res = add_clauses (M.keys resolved)
              $ drop_variable v s
      -- print res
      let reconstruct v m = Prelude.or $ do
            cp <- map (get_clause nf) pos 
            return $ Prelude.not $ Prelude.or $ do
              lit <- literals $ cp `without` v
              let v = E.findWithDefault False ( variable lit ) m
              return $ if positive lit then v else Prelude.not v 
      when logging $ hPutStrLn stderr $ unwords
          [ "best resolution:", show v, "count", show c ]
   
      later <- fomo res
      return $ case later of
        Left rup -> Left rup -- FIXME
        Right m -> Right $ E.insert v (reconstruct v m) m

islongerthan k xs = not $ null $ drop k xs

nobranch :: Solver
nobranch s = do
  print_info "nobranch" s
  let cnf :: CNF
      cnf = current s

  let stat :: M.Map Literal Double
      stat = M.fromListWith (+) $ do
        
        c <- smallest_clauses 1000 cnf
        let cl = get_clause cnf c
        let w = -- 2 ^^ negate (M.size m)
              1 / fromIntegral (sizeC cl)
        l <- literals cl
        return (l, w)
      (l,w) = maximumBy (compare `on` snd) $ M.toList stat
      v = variable l ; p = positive l

  when nobranch_logging $ hPutStr stderr $ unlines
      [ "nobranch", show s, "decide " ++ show v ++ show p ]
  fomo $ descend_from s $ assign Decided (v, p) s

  
branch :: Solver
branch s = do
  print_info "branch" s
  let cnf :: CNF
      cnf = current s

  let stat :: M.Map Literal Double
      stat = M.fromListWith (+) $ do
        
        c <- smallest_clauses 1000 cnf
        let cl = get_clause cnf c
        let w = -- 2 ^^ negate (M.size m)
              1 / fromIntegral (sizeC cl)
        l <- literals cl
        return (l, w)
      (l,w) = maximumBy (compare `on` snd) $ M.toList stat
      v = variable l ; p = positive l

  when logging $ do hPutStr stderr $ unwords [ "D", show v, show p ]
  a <- fomo $ descend_from s $ assign Decided (v, p) s
  case a of
    Right m -> return $ Right $ E.insert v p m
    Left ul -> do
      when logging $ do hPutStr stderr $ unwords [ "D", show v, show $ not p ]
      b <- fomo $ descend_from s $ assign Decided (v, not p) s
      case b of
        Right m -> return $ Right $ E.insert v (not p) m
        Left ur -> return $ Left
          $ Unsat { rup =  emptyC
                         : map (insertC v       p) (rup ul)
                        ++ map (insertC v $ not p) (rup ur)
                  , learnt = []
                  }
