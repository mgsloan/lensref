{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE CPP #-}
--{-# OPTIONS_HADDOCK hide #-}
{- |
Fast implementation for the @MonadRefCreator@ interface.

TODO
- elim mem leak: registered events don't allow to release unused refs
- optimiziation: do not remember values
- optimiziation: equality check
-}
module Data.LensRef.Fast
    ( Register
    , runRegister
#ifdef __TESTS__
    , runTests
#endif
    ) where

import Data.Monoid
import Control.Applicative hiding (empty)
import Control.Monad.State
import Control.Monad.Reader
import Control.Lens

import Data.LensRef
import Data.LensRef.Common
#ifdef __TESTS__
import Data.LensRef.TestEnv
import Data.LensRef.Test
#endif

----------------------

newtype Wrap m a
    = Wrap {unWrap :: m a}
        deriving (Monad, Functor, Applicative, MonadFix)

instance NewRef m => NewRef (Wrap m) where
    newRef' x = Wrap $ liftM (\(Morph f) -> Morph $ \g -> Wrap $ f $ mapStateT unWrap g) $ newRef' x

instance MonadTrans Wrap where
    lift = Wrap

newtype instance RefWriterOf (Wrap m) a
    = RefWriterOfIO { runRefWriterOfIO :: Wrap m a }
        deriving (Monad, Applicative, Functor)

----------------------

data Lens__ (m :: * -> *) a = Lens_ 
    { readPart :: m a
    , writePart :: a -> m ()
    , register :: m () -> m ()
    }

type Lens_ m = Lens__ (Wrap m)

joinLens :: Monad m => Wrap m (Lens_ m a) -> Lens_ m a
joinLens m = Lens_
    { readPart = m >>= readPart
    , writePart = \a -> m >>= \r -> writePart r a
    , register = \e -> m >>= \r -> register r e
    }

instance NewRef m => RefClass (Lens_ m) where
    type RefReaderSimple (Lens_ m) = Wrap m

    readRefSimple = readPart . joinLens
    writeRefSimple m = RefWriterOfIO . writePart (joinLens m)
    lensMap l m = do
        Lens_ r w t <- m
        return Lens_
            { readPart = r >>= \a -> return $ a ^. l
            , writePart = \b -> r >>= \a -> w $ set l b a
            , register = t
            }
    unitRef = return Lens_
                { readPart = return ()
                , writePart = const $ return ()
                , register = \_ -> return ()
                }

instance NewRef m => MonadRefReader (Wrap m) where

    type BaseRef (Wrap m) = Lens_ m

    liftRefReader = id

instance NewRef m => MonadRefReader (RefWriterOf (Wrap m)) where

    type BaseRef (RefWriterOf (Wrap m)) = Lens_ m

    liftRefReader = RefWriterOfIO

instance NewRef m => MonadRefWriter (RefWriterOf (Wrap m)) where
    liftRefWriter = id -- RefWriterOfIO . runRefWriterOfIO

{-
wrap :: NewRef m => IO a -> Wrap m a
wrap m = Wrap $ liftBaseWith $ const m
-}
instance NewRef m => MonadRefCreator (Wrap m) where

    extRef r r2 a0 = do
        Lens_ rb wb tb <- r
        b0 <- rb
        va <- newRef' $ set r2 b0 a0
        reg <- newRef' $ return ()
        status <- newRef' True -- True: normal; False:
        tb $ do
            s <- runMorph status get
            when s $ do
                b <- rb
                runMorph va $ modify (set r2 b)
                join $ runMorph reg get
        return $
            return Lens_
                { readPart = runMorph va get
                , writePart = \a -> do
                    runMorph va $ put a
                    runMorph status $ put False
                    wb $ a ^. r2
                    runMorph status $ put True
                    join $ runMorph reg get
                , register = \m -> runMorph reg $ modify (>> m)
                }

    newRef a0 = do
        va <- newRef' a0
        reg <- newRef' $ return ()
        return $ return Lens_
                { readPart = runMorph va get
                , writePart = \a -> do
                    runMorph va $ put a
                    join $ runMorph reg get
                , register = \m -> runMorph reg $ modify (>> m)
                }

instance NewRef m => MonadMemo (Wrap m) where
    memoRead = memoRead_
{-
    memoWrite = memoWrite_

    future = future_
-}


instance NewRef m => MonadRefWriter (Wrap m) where
    liftRefWriter = runRefWriterOfIO


---------------------------------

type Register_ m = ReaderT (Ref m (MonadMonoid m, RegionStatusChange -> MonadMonoid m)) m

newtype Reg n a = Reg { unReg :: ReaderT (SLSt n () -> n ()) (Register_ (SLSt n)) a } deriving (Monad, Applicative, Functor)

type SLSt (m :: * -> *) = m

type Register m = Reg (Wrap m)
{-
mapReg :: (forall a . m a -> n a) -> Reg m a -> Reg n a
mapReg ff (Reg m) = Reg $ ReaderT $ \f -> ReaderT $ \r -> StateT $ \s -> 
    ff $ flip runStateT s $ flip runReaderT (iso undefined undefined `lensMap` r) $ runReaderT m $ undefined f

instance MonadTrans Reg where
    lift = Reg . lift . lift . lift
-}

instance MonadFix m => MonadFix (Register m) where
    mfix f = Reg $ mfix $ unReg . f

instance NewRef m => MonadRefReader (Register m) where

    type BaseRef (Register m) = Lens_ m

    liftRefReader = Reg . lift . lift . liftRefReader

instance NewRef m => MonadRefCreator (Register m) where
    extRef r l = Reg . lift . lift . extRef r l
    newRef = Reg . lift . lift . newRef

instance NewRef m => MonadMemo (Register m) where
    memoRead = memoRead_
{-
    memoWrite = memoWrite_
    future = future_
-}
instance NewRef m => MonadRefWriter (Register m) where
    liftRefWriter = Reg . lift . lift . liftRefWriter

instance NewRef m => MonadRegister (Register m) where

    type EffectM (Register m) = m

    type Modifier (Register m) = Register m

    liftEffectM = Reg . lift . lift . lift

    liftToModifier = id

    onChange r f = onChangeAcc r undefined undefined $ \b _ _ -> liftM const $ f b

    onChangeSimple r f = Reg $ ReaderT $ \ff ->
        toSend False r undefined undefined $ \b _ _ -> return $ \_ -> evalRegister ff $ f b

    registerCallback f = Reg $ ReaderT $ \ff -> do
        writerstate <- ask
        return $ fmap (unWrap . ff . flip runReaderT writerstate . evalRegister ff) f

    onRegionStatusChange g = Reg $ ReaderT $ \ff -> do
        writerstate <- ask
        tell' (mempty, MonadMonoid . flip runReaderT writerstate . evalRegister ff . g)


evalRegister ff (Reg m) = runReaderT m ff

runRegister :: NewRef m => (forall a . m (m a, a -> m ())) -> Register m a -> m (a, m ())
runRegister newChan (Reg m) = unWrap $ do
    (read, write) <- Wrap newChan
    (a, tick) <- do
        (a, r) <- runRefWriterT $ runReaderT m $ Wrap . write
        (w, _) <- readRef r
        return (a, runMonadMonoid w)
    return $ (,) a $ unWrap $ forever $ do
        join $ Wrap read
        tick

runRegister_ :: NewRef m => (m (Wrap m ())) -> (Wrap m () -> m ()) -> Register m a -> m (a, m ())
runRegister_ read write (Reg m) = unWrap $ do
    (a, tick) <- do
        (a, r) <- runRefWriterT $ runReaderT m $ Wrap . write
        (w, _) <- readRef r
        return (a, runMonadMonoid w)
    return $ (,) a $ unWrap $ forever $ do
        join $ Wrap read
        tick


onChangeAcc r b0 c0 f = Reg $ ReaderT $ \ff ->
    toSend True r b0 c0 $ \b b' c' -> liftM (\x -> evalRegister ff . x) $ evalRegister ff $ f b b' c'

toSend
    :: (Eq b, MonadRefCreator m, MonadRefWriter m)
    => Bool
    -> RefReader m b
    -> b -> (b -> c)
    -> (b -> b -> c -> {-Either (Register m c)-} Register_ m (c -> Register_ m c))
    -> Register_ m (RefReader m c)
toSend memoize rb b0 c0 fb = do
    let doit st = readRef st >>= runMonadMonoid . fst
        reg st msg = readRef st >>= runMonadMonoid . ($ msg) . snd

    memoref <- lift $ do
        b <- liftRefReader rb
        (c, st1) <- runRefWriterT $ fb b b0 $ c0 b0
        (val, st2) <- runRefWriterT $ c $ c0 b0
        doit st1
        doit st2
        newRef ((b, (c, val, st1, st2)), [])      -- memo table

    let act = MonadMonoid $ do
            b <- liftRefReader rb
            (last@(b', cc@(_, oldval, st1, st2)), memo) <- readRef memoref
            (_, _, st1, st2) <- if b' == b
              then
                return cc
              else do
                reg st1 Block
                reg st2 Kill
                (c, oldval', st1, _) <- case lookup b memo of
                  Nothing -> do
                    (c, st1) <- runRefWriterT $ fb b b' oldval
                    return (c, c0 b, st1, undefined)
                  Just cc'@(_, _, st1, _) -> do
                    reg st1 Unblock
                    return cc'
                (val, st2) <- runRefWriterT $ c oldval'
                let cc = (c, val, st1, st2)
                writeRef memoref ((b, cc), if memoize then filter ((/= b) . fst) (last:memo) else [])
                return cc
            doit st1
            doit st2

    tell' (act, mempty)
    return $ readRef $ (_1 . _2 . _2) `lensMap` memoref

--------------------------

#ifdef __TESTS__
instance MonadRegisterRun (Register (Prog TP)) where

    type AsocT (Register (Prog TP)) = TP

    runReg r w m = runRegister_ (liftM unTP r) (w . TP) m

newtype TP = TP { unTP :: Wrap (Prog TP) () }

runTests = do
    mkTests runTestSimple
    tests runTest


runTest :: (Eq a, Show a) => String -> Register (Prog TP) a -> Prog' (a, Prog' ()) -> IO ()
runTest name = runTest_ name (TP . lift) runReg

runTestSimple :: Register (Prog TP) () -> IO ()
runTestSimple m = runTest "" m $ return ((), return ())
#endif

