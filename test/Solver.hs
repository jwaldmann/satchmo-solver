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
  res <- fomo $ initial f
  case res of
    Left u -> do
      putStrLn $ unlines $ "UNSAT" : map show (reverse $ rup u)
    Right m -> do
      putStrLn "SAT"
      print m
      
