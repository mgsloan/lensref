{-# LANGUAGE CPP #-}

#ifndef __TESTS__
main :: IO ()
main = fail "enable the tests flag"
#else
import Numeric
import Data.IORef
import Control.Monad
import Criterion.Main
import Criterion.Config

import Data.LensRef.Test

------------------

myConfig = defaultConfig
              -- Always GC between runs.
            { cfgPerformGC = ljust True
            , cfgReport    = ljust "lensref-performance-report.html"
            }

main = defaultMainWith myConfig (return ()) $
    [ bench ("ioref " ++ show i) $ ioRefTest i | i <- range]
 ++ [ bench ("lensref fast " ++ show i) $ runPerformanceTests i | i <- map (`div` 10) $ range]
 ++ [ bench ("lensref pure " ++ show i) $ runPerformanceTestsPure i | i <- map (`div` 100) $ range]
  where
--    range = takeWhile (<50000) [2^n | n <- [4..]]
    range = [1000,2000..9000] ++ [10000,20000..60000]

-- for comparison
ioRefTest n = do
    rs <- replicateM n $ newIORef 'x'
    forM_ rs $ \r -> r ==> 'x'
    forM_ rs $ \r -> writeIORef r 'y'
    forM_ rs $ \r -> r ==> 'y'
  where
    r ==> v = readIORef r >>= (==? v)

    a ==? b | a == b = return ()
    a ==? b = fail $ show a ++ " /= " ++ show b
#endif
