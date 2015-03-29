{-# language GeneralizedNewtypeDeriving #-}
{-# language MultiParamTypeClasses #-}
{-# language TypeSynonymInstances #-}
{-# language FlexibleInstances #-}


module Satchmo.Connect where

import Satchmo.Graph
import qualified Data.EnumMap as M
import Satchmo.Fourier_Motzkin

import Satchmo.MonadSAT
import Satchmo.Code
import Satchmo.Boolean ( Boolean(..) )

import Satchmo.Data (literal, variable,positive, Literal)
import qualified Satchmo.Data as SD

import Control.Monad.State.Strict
import Control.Monad.Reader
import Control.Applicative

newtype S a = S (State Form a) deriving
  ( Monad, MonadFix, MonadState Form , Applicative, Functor)

instance MonadSAT S where
  fresh = do
    f <- get
    let (g, V v) = add_variable f
    put g
    return $ literal True v
  
  emit cl = do
    modify $ add_clause (SD.literals cl)


solve :: S (Reader (M.Map V Bool) a) -> IO (Maybe a)
solve (S ff) = do
  let (r,s1) = runState ff cnf0
  -- print s1
  res <- fomo s1
  return $ case res of
    Nothing -> Nothing
    Just m -> Just $ runReader r m 
  
instance Decode (Reader (M.Map V Bool)) Boolean Bool where 
  decode b = case b of
    Constant c -> return c
    Boolean l -> do
      m <- ask
      let v = M.findWithDefault False ( variable l ) m
      return $ if positive l then v else not v

