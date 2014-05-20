module Main where

import Data.LensRef.Pure
import Data.LensRef.Fast

main :: IO ()
main = do
    putStrLn "running tests for the pure implementation"
    Data.LensRef.Pure.runTests
    putStrLn "running tests for the fast implementation"
    Data.LensRef.Fast.runTests

