{-# language GeneralizedNewtypeDeriving #-}
{-# language MultiParamTypeClasses #-}


module Satchmo.Connect where

import Satchmo.Graph
import Satchmo.Fourier_Motzkin

import Satchmo.MonadSAT
import Satchmo.Code
import Satchmo.Boolean ( Boolean )

import Satchmo.Data (literal, variable,positive, Literal)
import qualified Satchmo.Data as SD

import Control.Monad.State.Strict
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
    f <- get
    put $ add_clause f $ SD.literals cl


solve :: S (S a) -> IO (Maybe a)
solve (S ff) = do
  let (S a,s1) = runState ff cnf0
  print s1
  res <- fomo s1
  case res of
    Nothing -> return Nothing
    Just m -> do
      let (b,s2) = runState a s1
      return $ Just b
  
instance Decode S Boolean Bool where 
