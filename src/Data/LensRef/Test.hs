{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
-- | Tests for the lens references interface.
module Data.LensRef.Test
    ( -- * Tests for the interface
      tests
    ) where

import Data.Maybe
import Control.Applicative
import Control.Monad
import Control.Arrow ((***))
import Control.Lens

import Data.LensRef
import Data.LensRef.Class
import Data.LensRef.TestEnv

-----------------------------------------------------------------

-- | Look inside the sources for the tests.
tests :: (MonadRegister m, MonadRefWriter m, EffectM m ~ Prog k, {- MonadRegister (Modifier m), -} Monad n)
    => (forall a . (Eq a, Show a) => String -> m a -> Prog' (a, Prog' ()) -> n ())
    -> n ()

tests runTest = do

    let runTestSimple name t = runTest name t $ pure ((), pure ())

    let r ==> v = readRef r >>= (==? v)

    runTestSimple "newRefTest" $ do
        r <- newRef (3 :: Int)
        r ==> 3

    runTestSimple "writeRefsTest" $ do
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

    runTestSimple "extRefTest" $ do
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

    runTestSimple "joinTest" $ do
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

    runTestSimple "joinTest2" $ do
        r1 <- newRef (3 :: Int)
        rr <- newRef r1
        r2 <- newRef 5
        writeRef rr r2
        join (readRef rr) ==> 5

    runTestSimple "chainTest0" $ do
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

    runTestSimple "forkTest" $ do
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

    runTestSimple "forkTest2" $ do
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

    runTestSimple "chainTest" $ do
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

    runTestSimple "chainTest1" $ do
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

    runTestSimple "undoTest" $ do
        r <- newRef (3 :: Int)
        q <- extRef r (lens head $ flip (:)) []
        writeRef r 4
        q ==> [4, 3]

    runTestSimple "undoTest2" $ do
        r <- newRef (3 :: Int)
        q <- extRef r (lens head $ flip (:)) []
        q ==> [3]

    let
        perform m = m >>= maybe (pure ()) liftRefWriter
        m === t = m >>= \x -> isJust x ==? t

    runTestSimple "undoTest3" $ do
        r <- newRef (3 :: Int)
        (undo, redo) <- fmap (liftRefReader *** liftRefReader) $ undoTr (==) r
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
        perform undo
        r ==> 4
        redo === True
        undo === True
        perform undo
        r ==> 3
        redo === True
        undo === False
        perform redo
        r ==> 4
        redo === True
        undo === True
        writeRef r 6
        r ==> 6
        redo === False
        undo === True


    runTest "trivial" (pure ()) $ do
        pure ((), pure ())

    runTest "message" (message "Hello") $ do
        message' "Hello"
        pure ((), pure ())

    runTest "listener" (listen 1 $ \s -> message $ "Hello " ++ s) $ do
        message' "listener #0"
        pure $ (,) () $ do
            send 1 "d"
            message' "Hello d"
            send 1 "f"
            message' "Hello f"
    --                send 2 "f"
{-
    runTest "listeners" (do
        listen 1 $ \s -> message $ "Hello " ++ s
        listen 2 $ \s -> message $ "Hi " ++ s
        listen 3 $ \s -> do
            message $ "H_ " ++ s
            listen 4 $ \s' ->
                message $ "H " ++ s'
      ) $ do
        message' "listener #0"
        message' "listener #1"
        message' "listener #2"
        pure $ (,) () $ do
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
-}
    runTest "postponed0" (postponeModification $ message "hello") $ do
        pure $ (,) () $ do
            message' "hello"

    runTest "postponed-write" (do
        r <- newRef "x"
        _ <- onChange (readRef r) message
        postponeModification $ writeRef r "y"
            ) $ do
        message' "x"
        pure $ (,) () $ do
            message' "y"

    runTest "postponed" (do
        r <- newRef "x"
        _ <- onChange (readRef r) message
        postponeModification $ writeRef r "x"
        postponeModification $ writeRef r "y"
        pure ()
            ) $ do
        message' "x"
        pure $ (,) () $ do
            message' "y"

    runTest "onChange" (do
        r <- newRef "x"
        listen 1 $ writeRef r
        _ <- onChange (readRef r) message
        pure ()
            ) $ do
        message' "listener #0"
        message' "x"
        pure $ (,) () $ do
            send 1 "x"
            send 1 "y"
            message' "y"

    runTest "onChange + listener" (do
        r1 <- newRef "x"
        r2 <- newRef "y"
        listen 1 $ writeRef r1
        listen 2 $ writeRef r2
        _ <- onChange (liftA2 (++) (readRef r1) (readRef r2)) message
        pure ()
            ) $ do
        message' "listener #0"
        message' "listener #1"
        message' "xy"
        pure $ (,) () $ do
            send 1 "x"
            send 2 "y"
            send 1 "y"
            message' "yy"
            send 2 "y"
            send 2 "x"
            message' "yx"

    runTest "onChange + join" (do
        r1 <- newRef "x"
        r2 <- newRef "y"
        rr <- newRef r1
        listen 1 $ writeRef r1
        listen 2 $ writeRef r2
        listen 3 $ \i -> case i of
            True  -> writeRef rr r1
            False -> writeRef rr r2
        _ <- onChange (readRef $ join $ readRef rr) message
        pure ()
            ) $ do
        message' "listener #0"
        message' "listener #1"
        message' "listener #2"
        message' "x"
        pure $ (,) () $ do
            send 1 "x"
            send 2 "y"
            send 1 "y"
            message' "y"
            send 2 "y"
            send 2 "x"
            send 3 False
            message' "x"
            send 1 "a"
            send 2 "b"
            message' "b"


    runTest "bla" (do
        r <- newRef (0 :: Int)
        _ <- onChangeMemo (readRef r) $ \i -> case i of
            0 -> pure $ do
                listen 1 $ \s -> do
                    when (s == "f") $ do
                        writeRef r 1
                        rv <- readRef r
                        message $ show rv
                    message $ "Hello " ++ s

            1 -> do
                listen 2 $ \s -> do
                    when (s == "g") $ writeRef r 0
                    message $ "Hi " ++ s
                pure $ pure ()

        pure ()
              ) $ do

        message' "listener #0"
        pure $ (,) () $ do
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

    runTest "bla2" (do
        r <- newRef $ Just (3 :: Int)
        q <- extRef r maybeLens (False, 0)
        let q1 = _1 `lensMap` q
            q2 = _2 `lensMap` q
        _ <- onChangeMemo (readRef r) $ \r -> pure $ message $ show r
        _ <- onChangeMemo (readRef q) $ \r -> pure $ message $ show r
        postponeModification $ writeRef r Nothing
        postponeModification $ writeRef q1 True
        postponeModification $ writeRef q2 1
        ) $ do
        message' "Just 3"
        message' "(True,3)"
        pure $ (,) () $ do
            message' "Nothing"
            message' "(False,3)"
            message' "Just 3"
            message' "(True,3)"
            message' "Just 1"
            message' "(True,1)"

--    let r ===> v = liftRefReader r >>= (==? v)

    runTest "onChange value" (do
        r <- newRef (0 :: Int)
        q <- onChange (readRef r) pure
        _ <- onChange q $ message . show
        postponeModification $ message "a" >> writeRef r 1
        postponeModification $ message "b" >> writeRef r 2
        postponeModification $ message "c" >> writeRef r 3
        postponeModification $ message "d" >> writeRef r 3
        postponeModification $ message "e" >> writeRef r 4
        ) $ do
        message' "0"
        pure $ (,) () $ do
            message' "a"
            message' "1"
            message' "b"
            message' "2"
            message' "c"
            message' "3"
            message' "d"
            message' "e"
            message' "4"

    runTest "schedule" (do
        r <- newRef "a"
        q <- newRef "b"
        _ <- onChange (readRef r) message
        _ <- onChange (readRef q) message
        postponeModification $ message "." >> writeRef r "x" >> writeRef q "y"
        postponeModification $ message ".." >> writeRef q "1" >> writeRef r "2"
        ) $ do
        message' "a"
        message' "b"
        pure $ (,) () $ do
            message' "."
            message' "x"
            message' "y"
            message' ".."
            message' "2"
            message' "1"

    runTest "diamond" (do
        r <- newRef "a"
        q <- newRef "b"
        rq <- onChange (liftA2 (++) (readRef r) (readRef q)) $ pure . pure
        _ <- onChange (join rq) message
        postponeModification $ message "." >> writeRef r "x" >> writeRef q "y"
        postponeModification $ message ".." >> writeRef q "1" >> writeRef r "2"
        ) $ do
        message' "ab"
        pure $ (,) () $ do
            message' "."
            message' "xy"
            message' ".."
            message' "21"

{-
    runTest "listen-listen" (do
        listen 1 $ \s -> case s of
            "x" -> listen 2 message
            _ -> pure ()
        ) $ do
        message' "listener #0"
        pure $ (,) () $ do
            send 1 "d"
            send 2 "hi"
            error' "message is not received: 2 \"hi\""
            send 1 "d"
            send 1 "x"
            message' "listener #1"
            send 2 "hi"
            message' "hi"
            send 1 "x"
            message' "listener #2"
            send 2 "hi"
            message' "hi"
            message' "hi"
            send 2 "hi"
            message' "hi"
            message' "hi"
            send 1 "d"
            send 2 "hi"
            message' "hi"
            message' "hi"
            send 1 "x"
            message' "listener #3"
            send 2 "hi"
            message' "hi"
            message' "hi"
            message' "hi"

    runTest "listen-onChange" (do
        r <- newRef "k"
        listen 1 $ \s -> case s of
            "x" -> onChange (readRef r) message >> pure ()
            _ -> writeRef r s
        ) $ do
        message' "listener #0"
        pure $ (,) () $ do
            send 1 "d"
            send 1 "x"
            message' "d"
            send 1 "d"
            send 1 "e"
            send 1 "x"
            message' "e"
--            message' "x"
            send 1 "f"
--            message' "f"
-}        

-------------------------- auxiliary definitions

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
    let try f = fmap (fmap (writeRefSimple ku) . f) $ readRef ku
    pure (try undo, try redo)
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



