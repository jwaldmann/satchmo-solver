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

import Satchmo.Data (literal, variable,positive, Literal)
import qualified Satchmo.Data as SD

import Control.Monad.State.Strict
import Control.Monad.Reader
import Control.Applicative
import System.IO

newtype S a = S (State Form a) deriving
  ( Monad, MonadFix, MonadState Form , Applicative, Functor)

instance MonadSAT S where
  fresh = do
    f <- get
    let (g, v) = add_variable f
    put g
    return $ literal True $ fromEnum v
  
  emit cl = do
    modify $ add_clause Input (SD.literals cl)


solve :: S (Reader (E.Map V Bool) a) -> IO (Maybe a)
solve (S ff) = do
  when check_asserts $ hPutStrLn stderr $ unlines
    [ "!!!!!!!! Satchmo.Form.check_asserts == True (solver will be SLOW) !!!!!!!" ]
  let (r,s1) = runState ff Satchmo.Form.empty
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
      let v = E.findWithDefault False ( variable l ) m
      return $ if positive l then v else not v

