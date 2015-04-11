-- | this module implements the interface to 'MonadSAT' from satchmo.
-- This allows to build the formula in satchmo, then call the solver.

{-# language GeneralizedNewtypeDeriving #-}
{-# language MultiParamTypeClasses #-}
{-# language TypeSynonymInstances #-}
{-# language FlexibleInstances #-}


module Satchmo.Connect where

import Satchmo.Form
import qualified Data.EnumMap as E
import Satchmo.Fourier_Motzkin

import Satchmo.MonadSAT
import Satchmo.Code
import Satchmo.Boolean ( Boolean(..) )

import qualified Satchmo.Data as SD

import Control.Monad.State.Strict
import Control.Monad.Reader
import Control.Applicative
import System.IO

newtype S a = S (State (CNF,V) a) deriving
  ( Monad, MonadFix , MonadState (CNF,V)
  , Applicative, Functor)

instance MonadSAT S where
  fresh = do
    (f,top) <- get
    put (f,succ top)
    return $ SD.literal True $ fromEnum top
  
  emit cl = do
    modify $ \(f,v)
             -> (add_clauses [clause $ map (\l ->
                (toEnum $ SD.variable l,SD.positive l) ) $ SD.literals cl] f, v)


solve :: S (Reader (E.Map V Bool) a) -> IO (Maybe a)
solve (S ff) = do
  when check_asserts $ hPutStrLn stderr $ unlines
    [ "!!!!!!!! Satchmo.Form.check_asserts == True (solver will be SLOW) !!!!!!!" ]
  when using_model $ hPutStrLn stderr $ unlines
    [ "!!!!!!!! Satchmo.Form.using_model == True (solver will be SLOW) !!!!!!!" ]
  let (r,(s1,_)) = runState ff (Satchmo.Form.empty, toEnum 1)
  res <- fomo $ initial s1 
  case res of
    Left u -> do
      hPutStrLn stderr $ unlines $ "not satisfiable, RUP:"
        : map show (reverse $ rup u)
      return Nothing
    Right m -> return $ Just $ runReader r m

instance Decode (Reader (E.Map V Bool)) Boolean Bool where 
  decode b = case b of
    Constant c -> return c
    Boolean l -> do
      m <- ask
      let v = E.findWithDefault False ( SD.variable l ) m
      return $ if SD.positive l then v else not v

