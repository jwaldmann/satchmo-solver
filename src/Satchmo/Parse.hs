-- | parse DIMACS format.
-- Declarations of no. of variables and clauses are ignored.

module Satchmo.Parse where

import Satchmo.Form
-- import Satchmo.Data

import qualified Data.ByteString.Lazy as BS
import qualified Data.ByteString.Lazy.Char8 as BSC

import qualified Data.Attoparsec.ByteString.Char8 as A

import Data.Foldable ( foldl' )
import Control.Applicative

form :: BS.ByteString -> CNF
form s = foldl' ( \ f line ->
   case A.parseOnly ( pline <* A.endOfInput ) $ BSC.toStrict line of
     Left msg -> f
     Right ns ->
       let cl = clause $ map (\ n -> (toEnum $ abs n, n>0) )
              $ takeWhile (/= 0) ns
       in  add_clauses [cl] f 
                ) Satchmo.Form.empty
   $ BSC.lines s

pline :: A.Parser [Int]
pline = A.many1 $ ( A.signed A.decimal
                    <* A.many' (A.satisfy A.isSpace )
                  )
