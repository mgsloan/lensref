module Main where

import qualified Data.LensRef.Pure as Pure
import qualified Data.LensRef.Fast as Fast

main :: IO ()
main = do
    putStrLn "running tests for pure implementation"
    Pure.runTests
    putStrLn "running tests for fast implementation"
    Fast.runTests

