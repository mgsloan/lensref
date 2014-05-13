{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
-- | Tests for the @MonadRefCreator@ interface.
module Data.LensRef.Test
    ( -- * Tests for the interface
      mkTests
    , tests
    ) where

import Data.Maybe
import Control.Monad.State
import Control.Arrow ((***))
import Control.Lens

import Data.LensRef
import Data.LensRef.TestEnv

-----------------------------------------------------------------

{- | 
@mkTests@ generates a list of error messages which should be emtpy.

Look inside the sources for the tests.
-}
mkTests :: (MonadRegisterRun m, MonadRefWriter m, EffectM m ~ Prog (AsocT m), Monad n)
    => (m () -> n ())
    -> n ()

mkTests runTest = do
    newRefTest
    writeRefsTest
    extRefTest
    joinTest
    joinTest2
    chainTest0
    forkTest
    forkTest2
    chainTest
    chainTest'
    undoTest
    undoTest2
    undoTest3

--    writeRefTest
  where

    newRefTest = runTest $ do
        r <- newRef (3 :: Int)
        r ==> 3


    writeRefsTest = runTest $ do
        r1 <- newRef (3 :: Int)
        r2 <- newRef (13 :: Int)
        r1 ==> 3
        r2 ==> 13
        writeRef r1 4
        r1 ==> 4
        r2 ==> 13
        writeRef r2 0
        r1 ==> 4
        r2 ==> 0

    extRefTest = runTest $ do
        r <- newRef $ Just (3 :: Int)
        q <- extRef r maybeLens (False, 0)
        let q1 = _1 `lensMap` q
            q2 = _2 `lensMap` q
        r ==> Just 3
        q ==> (True, 3)
        writeRef r Nothing
        r ==> Nothing
        q ==> (False, 3)
        q1 ==> False
        writeRef q1 True
        r ==> Just 3
        writeRef q2 1
        r ==> Just 1

    joinTest = runTest $ do
        r2 <- newRef (5 :: Int)
        r1 <- newRef 3
        rr <- newRef r1
        r1 ==> 3
        let r = join $ readRef rr
        r ==> 3
        writeRef r1 4
        r ==> 4
        writeRef rr r2
        r ==> 5
        writeRef r1 4
        r ==> 5
        writeRef r2 14
        r ==> 14

    joinTest2 = runTest $ do
        r1 <- newRef (3 :: Int)
        rr <- newRef r1
        r2 <- newRef 5
        writeRef rr r2
        join (readRef rr) ==> 5

    chainTest0 = runTest $ do
        r <- newRef (1 :: Int)
        q <- extRef r id 0
        s <- extRef q id 0
        r ==> 1
        q ==> 1
        s ==> 1
        writeRef r 2
        r ==> 2
        q ==> 2
        s ==> 2
        writeRef q 3
        r ==> 3
        q ==> 3
        s ==> 3
        writeRef s 4
        r ==> 4
        q ==> 4
        s ==> 4

    forkTest = runTest $ do
        r <- newRef (1 :: Int)
        q <- extRef r id 0
        s <- extRef r id 0
        r ==> 1
        q ==> 1
        s ==> 1
        writeRef r 2
        r ==> 2
        q ==> 2
        s ==> 2
        writeRef q 3
        r ==> 3
        q ==> 3
        s ==> 3
        writeRef s 4
        r ==> 4
        q ==> 4
        s ==> 4

    forkTest2 = runTest $ do
        r <- newRef $ Just (1 :: Int)
        q <- extRef r maybeLens (False, 0)
        s <- extRef r maybeLens (False, 0)
        r ==> Just 1
        q ==> (True, 1)
        s ==> (True, 1)
        writeRef r $ Just 2
        r ==> Just 2
        q ==> (True, 2)
        s ==> (True, 2)
        writeRef r Nothing
        r ==> Nothing
        q ==> (False, 2)
        s ==> (False, 2)
        writeRef (_1 `lensMap` q) True
        r ==> Just 2
        q ==> (True, 2)
        s ==> (True, 2)
        writeRef (_2 `lensMap` q) 3
        r ==> Just 3
        q ==> (True, 3)
        s ==> (True, 3)
        writeRef (_1 `lensMap` q) False
        r ==> Nothing
        q ==> (False, 3)
        s ==> (False, 3)
        writeRef (_2 `lensMap` q) 4
        r ==> Nothing
        q ==> (False, 4)
        s ==> (False, 3)
        writeRef (_1 `lensMap` q) True
        r ==> Just 4
        q ==> (True, 4)
        s ==> (True, 4)
        writeRef q (False, 5)
        r ==> Nothing
        q ==> (False, 5)
        s ==> (False, 4)
        writeRef (_1 `lensMap` s) True
        r ==> Just 4
        q ==> (True, 4)
        s ==> (True, 4)

    chainTest = runTest $ do
        r <- newRef $ Just Nothing
        q <- extRef r maybeLens (False, Nothing)
        s <- extRef (_2 `lensMap` q) maybeLens (False, 3 :: Int)
        writeRef (_1 `lensMap` s) False
        r ==> Just Nothing
        q ==> (True, Nothing)
        s ==> (False, 3)
        writeRef (_1 `lensMap` q) False
        r ==> Nothing
        q ==> (False, Nothing)
        s ==> (False, 3)

    chainTest' = runTest $ do
        r <- newRef $ Just $ Just (3 :: Int)
        q <- extRef r maybeLens (False, Nothing)
        s <- extRef (_2 `lensMap` q) maybeLens (False, 0 :: Int)
        r ==> Just (Just 3)
        q ==> (True, Just 3)
        s ==> (True, 3)
        writeRef (_1 `lensMap` s) False
        r ==> Just Nothing
        q ==> (True, Nothing)
        s ==> (False, 3)
        writeRef (_1 `lensMap` q) False
        r ==> Nothing
        q ==> (False, Nothing)
        s ==> (False, 3)
        writeRef (_1 `lensMap` s) True
        r ==> Nothing
        q ==> (False, Just 3)
        s ==> (True, 3)
        writeRef (_1 `lensMap` q) True
        r ==> Just (Just 3)
        q ==> (True, Just 3)
        s ==> (True, 3)

    undoTest = runTest $ do
        r <- newRef (3 :: Int)
        q <- extRef r (lens head $ flip (:)) []
        writeRef r 4
        q ==> [4, 3]

    undoTest2 = runTest $ do
        r <- newRef (3 :: Int)
        q <- extRef r (lens head $ flip (:)) []
        q ==> [3]

    undoTest3 = runTest $ do
        r <- newRef (3 :: Int)
        (undo, redo) <- liftM (liftRefReader *** liftRefReader) $ undoTr (==) r
        r ==> 3
        redo === False
        undo === False
        writeRef r 4
        r ==> 4
        redo === False
        undo === True
        writeRef r 5
        r ==> 5
        redo === False
        undo === True
        push undo
        r ==> 4
        redo === True
        undo === True
        push undo
        r ==> 3
        redo === True
        undo === False
        push redo
        r ==> 4
        redo === True
        undo === True
        writeRef r 6
        r ==> 6
        redo === False
        undo === True
      where
        push m = m >>= \x -> maybe (return ()) liftRefWriter x
        m === t = m >>= \x -> isJust x ==? t

--------------------------

maybeLens :: Lens' (Bool, a) (Maybe a)
maybeLens = lens (\(b,a) -> if b then Just a else Nothing)
              (\(_,a) x -> maybe (False, a) (\a' -> (True, a')) x)


-- | Undo-redo state transformation.
undoTr
    :: MonadRegister m =>
       (a -> a -> Bool)     -- ^ equality on state
    -> Ref m a             -- ^ reference of state
    ->   m ( RefReader m (Maybe (RefWriter m ()))
           , RefReader m (Maybe (RefWriter m ()))
           )  -- ^ undo and redo actions
undoTr eq r = do
    ku <- extRef r (undoLens eq) ([], [])
    let try f = liftM (liftM (writeRefSimple ku) . f) $ readRef ku
    return (try undo, try redo)
  where
    undo (x: xs@(_:_), ys) = Just (xs, x: ys)
    undo _ = Nothing

    redo (xs, y: ys) = Just (y: xs, ys)
    redo _ = Nothing

undoLens :: (a -> a -> Bool) -> Lens' ([a],[a]) a
undoLens eq = lens get set where
    get = head . fst
    set (x' : xs, ys) x | eq x x' = (x: xs, ys)
    set (xs, _) x = (x : xs, [])


----------------------------------------------------------------------------

tests :: (MonadRegisterRun m, EffectM m ~ Prog (AsocT m), Monad n)
    => (forall a . (Eq a, Show a) => m a -> Prog' (a, Prog' ()) -> n ())
    -> n ()
tests runTest = do
    test0
    test1
    test2
    test3
    test4
    extRefTest
  where

    extRefTest = runTest (do
        r <- newRef $ Just (3 :: Int)
        q <- extRef r maybeLens (False, 0)
        let q1 = _1 `lensMap` q
            q2 = _2 `lensMap` q
        _ <- onChange (readRef r) $ \r -> return $ message $ show r
        _ <- onChange (readRef q) $ \r -> return $ message $ show r
        iReallyWantToModify $ writeRef r Nothing
        iReallyWantToModify $ writeRef q1 True
        iReallyWantToModify $ writeRef q2 1
        ) $ do
        message' "Just 3"
        message' "(True,3)"
        return $ (,) () $ do
            message' "Nothing"
            message' "(False,3)"
            message' "Just 3"
            message' "(True,3)"
            message' "Just 1"
            message' "(True,1)"
            return ()

    maybeLens :: Lens' (Bool, a) (Maybe a)
    maybeLens = lens (\(b,a) -> if b then Just a else Nothing)
              (\(_,a) x -> maybe (False, a) (\a' -> (True, a')) x)


    test0 = runTest (return ()) $ do
        return ((), return ())

    test1 = runTest (message "Hello") $ do
        message' "Hello"
        return ((), return ())

    test2 = runTest (listen 1 $ \s -> liftModifier $ message $ "Hello " ++ s) $ do
        message' "listener #0"
        return $ (,) () $ do
            send 1 "d"
            message' "Hello d"
            send 1 "f"
            message' "Hello f"
    --                send 2 "f"

    test3 = runTest (do
        listen 1 $ \s -> liftModifier $ message $ "Hello " ++ s
        listen 2 $ \s -> liftModifier $ message $ "Hi " ++ s
        listen 3 $ \s -> liftModifier $ do
            message $ "H_ " ++ s
            listen 4 $ \s' -> liftModifier $ 
                message $ "H " ++ s'
      ) $ do
        message' "listener #0"
        message' "listener #1"
        message' "listener #2"
        return $ (,) () $ do
            send 1 "d"
            message' "Hello d"
            send 1 "f"
            message' "Hello f"
            send 2 "f"
            message' "Hi f"
            send 3 "f"
            message' "H_ f"
            message' "listener #3"
            send 4 "f"
            message' "H f"

    test4 = runTest (do
        r <- newRef (0 :: Int)
        _ <- onChange (readRef r) $ \i -> case i of
            0 -> return $ do
                listen 1 $ \s -> do
                    when (s == "f") $ do
                        writeRef r 1
                        rv <- readRef r
                        liftModifier $ message $ show rv
                    liftModifier $ message $ "Hello " ++ s

            1 -> do
                listen 2 $ \s -> do
                    when (s == "g") $ writeRef r 0
                    liftModifier $ message $ "Hi " ++ s
                return $ return ()

        return ()
              ) $ do

        message' "listener #0"
        return $ (,) () $ do
            send 1 "d"
            message' "Hello d"
            send 1 "f"
            message' "1"
            message' "Hello f"
            message' "Kill #0"
            message' "listener #1"
            send 1 "f"
            error' "message is not received: 1 \"f\""
            send 2 "f"
            message' "Hi f"
            send 2 "g"
            message' "Hi g"
            message' "listener #2"
            send 2 "g"
            error' "message is not received: 2 \"g\""
            send 3 "f"
            error' "message is not received: 3 \"f\""
            send 1 "f"
            message' "1"
            message' "Hello f"
            message' "Kill #2"
            send 2 "f"
            message' "Hi f"



