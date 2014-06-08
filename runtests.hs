{-# LANGUAGE CPP #-}
module Main where

#ifndef __TESTS__
main :: IO ()
main = fail "enable the tests flag like \'cabal configure --enable-tests -ftests; cabal build; cabal test\'"
#else
import Data.LensRef.Test

main :: IO ()
main = do
    putStrLn "running tests for the pure implementation"
    runTestsPure
    putStrLn "running tests for the fast implementation"
    runTests
#endif

