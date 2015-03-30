import Satchmo.Parse
import Satchmo.Fourier_Motzkin

import System.Environment
import qualified Data.ByteString.Lazy.Char8 as BSC

main = do
  argv <- getArgs
  s <- case argv of
    [] -> BSC.getContents
    [f] -> BSC.readFile f
  let f = Satchmo.Parse.form s
  -- print f
  res <- fomo f
  case res of
    Nothing -> do
      putStrLn "UNSAT"
    Just m -> do
      putStrLn "SAT"
      print m
      
