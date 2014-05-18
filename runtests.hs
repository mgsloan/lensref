module Main where

import qualified Data.LensRef.Pure as Pure
import qualified Data.LensRef.Fast as Fast

main :: IO ()
main = do
    Pure.runTests
    Fast.runTests

