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
    [ n ] <- getArgs
    res :: Maybe [ Integer ] <- solve $ factor $ read n
    print res

factor :: (Decode m Boolean Bool,  MonadSAT m )
       => Integer -> m (m [Integer])
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
