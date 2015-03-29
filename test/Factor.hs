{-# language PatternSignatures #-}
{-# language FlexibleContexts #-}

import Prelude hiding ( not )

import Satchmo.Binary.Op.Fixed 
import qualified Satchmo.Binary.Op.Flexible 
import Satchmo.Boolean hiding ( equals )
import Satchmo.Code

-- import Satchmo.SAT.Mini
import Satchmo.Connect (solve)

import System.Environment

main :: IO ()
main = do
    args <- getArgs
    let n = case args of
          [] -> 1001
          [s] -> read s
    res :: Maybe [ Integer ] <- solve $ factor n
    print res

factor n = do
        x <- Satchmo.Binary.Op.Flexible.constant n
        a <- number $ width x 
        notone a
        b <- number $ width x  
        notone b
        ab <- times a b
        monadic assert [ equals ab x ]
        return $ decode [ a, b ]

notone f = do
    one <- Satchmo.Binary.Op.Flexible.constant 1
    e <- equals f one
    assert [ not e ]
