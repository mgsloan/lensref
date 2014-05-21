{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE CPP #-}
-- {-# OPTIONS_HADDOCK hide #-}
{- |
Register reference implementation for the @MonadRefCreator@ interface.

The implementation uses @unsafeCoerce@ internally, but its effect cannot escape.
-}
module Data.LensRef.Pure
    ( Register
    , runRegister
    , runTests
    ) where

import Data.Monoid
import Control.Applicative
import Control.Monad.State
import Control.Monad.Reader
import Control.Lens.Simple

import Unsafe.Coerce

import Data.LensRef.Class
import Data.LensRef.Common
#ifdef __TESTS__
import Data.LensRef.TestEnv
import Data.LensRef.Test
#endif

----------------------

newtype instance RefWriterOf (ReaderT s m) a
    = RefWriterOfReaderT { runRefWriterOfReaderT :: StateT s m a }
        deriving (Monad, Applicative, Functor, MonadReader s, MonadState s)

----------------------

newtype WrappedLens a b = WrappedLens {unwrapLens :: Lens' a b}

joinLens :: Reader a (WrappedLens a b) -> Lens' a b
joinLens r f a = unwrapLens (runReader r a) f a

type AllReferenceState = [ReferenceState]

data ReferenceState where
    ReferenceState :: (AllReferenceState -> a -> a) -> a -> ReferenceState

initAllReferenceState :: AllReferenceState
initAllReferenceState = []

instance MonadRefReader (Reader AllReferenceState) where
    type BaseRef (Reader AllReferenceState) = WrappedLens AllReferenceState
    liftRefReader = id

instance Monad m => MonadRefReader (RefWriterOf (ReaderT AllReferenceState m)) where
    type BaseRef (RefWriterOf (ReaderT AllReferenceState m)) = WrappedLens AllReferenceState
    liftRefReader = RefWriterOfReaderT . gets . runReader

instance MonadRefWriter (RefWriterOf (Reader AllReferenceState)) where
    liftRefWriter = id

instance RefClass (WrappedLens AllReferenceState) where
    type RefReaderSimple (WrappedLens AllReferenceState) = Reader AllReferenceState

    readRefSimple r = view $ joinLens r
    writeRefSimple r a = joinLens r .= a
    lensMap l r = return $ WrappedLens $ joinLens r . l
    unitRef = return $ WrappedLens united

instance Monad m => MonadRefReader (StateT AllReferenceState m) where
    type BaseRef (StateT AllReferenceState m) = WrappedLens AllReferenceState

    liftRefReader = gets . runReader

instance Monad m => MonadRefCreator (StateT AllReferenceState m) where
    extRef r r2 a0 = state extend
      where
        rk = set (joinLens r) . (^. r2)
        kr = set r2 . (^. joinLens r)

        extend x0 = (return $ WrappedLens $ lens get set, x0 ++ [ReferenceState kr (kr x0 a0)])
          where
            limit = splitAt (length x0)

            get = unsafeData . head . snd . limit

            set x a = foldl (\x -> (x++) . (:[]) . ap_ x) (rk a zs ++ [ReferenceState kr a]) ys where
                (zs, _ : ys) = limit x

        ap_ :: AllReferenceState -> ReferenceState -> ReferenceState
        ap_ x (ReferenceState f a) = ReferenceState f (f x a)

        unsafeData :: ReferenceState -> a
        unsafeData (ReferenceState _ a) = unsafeCoerce a


instance Monad m => MonadMemo (StateT AllReferenceState m) where
    memoRead = memoRead_

--instance MonadMemo (RefWriterOf (Reader AllReferenceState)) where
--    memoRead = memoRead_

instance Monad m => MonadRefWriter (StateT AllReferenceState m) where
    liftRefWriter = state . runState . runRefWriterOfReaderT


----------------

-- Ref-based WriterT
type RefWriterT w m = ReaderT (Ref m w) m

runRefWriterT :: (MonadRefCreator m, Monoid w) => RefWriterT w m a -> m (a, Ref m w)
runRefWriterT m = do
    r <- newRef mempty
    a <- runReaderT m r
    return (a, r)

tell' :: (Monoid w, MonadRefCreator m, MonadRefWriter m) => w -> RefWriterT w m ()
tell' w = ReaderT $ \m -> readRef m >>= writeRef m . (`mappend` w)

---------------------------------

type RegRef m
    = Ref m (MonadMonoid m (), RegionStatusChange -> MonadMonoid m ())

newtype Register n a
    = Register { unRegister :: ReaderT (SLSt n () -> n (), RegRef (SLSt n)) (SLSt n) a }
        deriving (Monad, Applicative, Functor, MonadFix)

type SLSt = StateT AllReferenceState
{-
mapReg :: (forall a . m a -> n a) -> Register m a -> Register n a
mapReg ff (Register m) = Register $ ReaderT $ \f -> ReaderT $ \r -> StateT $ \s -> 
    ff $ flip runStateT s $ flip runReaderT (iso undefined undefined `lensMap` r) $ runReaderT m $ undefined f
-}
instance MonadTrans Register where
    lift = Register . lift . lift

instance Monad m => MonadRefReader (Register m) where

    type BaseRef (Register m) = WrappedLens AllReferenceState

    liftRefReader = Register . lift . liftRefReader

instance Monad n => MonadRefCreator (Register n) where
    extRef r l = Register . lift . extRef r l
    newRef = Register . lift . newRef

instance Monad m => MonadMemo (Register m) where
    memoRead = memoRead_
{-
    memoWrite = memoWrite_
    future = future_
-}
instance Monad n => MonadRefWriter (Register n) where
    liftRefWriter = Register . lift . liftRefWriter

instance Monad n => MonadEffect (Register n) where

    type EffectM (Register n) = n

    liftEffectM = lift

instance Monad n => MonadRegister (Register n) where

    type Modifier (Register n) = Register n

--    liftToModifier = id

    onChangeMemo r f = onChangeAcc r undefined undefined $ \b _ _ -> liftM const $ f b

    registerCallback f = Register $ do
        st <- ask
        return $ fmap (fst st . evalRegister st) f

    onRegionStatusChange g = Register $ do
        magnify _2 $ tell' (mempty, MonadMonoid . lift . g)

evalRegister' ff (Register m) = ReaderT $ \s -> runReaderT m (ff, s)

evalRegister ff (Register m) = runReaderT m ff

runRegister :: Monad m => (forall a . m (m a, a -> m ())) -> Register m a -> m (a, m ())
runRegister newChan m = do
    (read, write) <- newChan
    runRegister_ read write m


runRegister_ :: Monad m => m (SLSt m ()) -> (SLSt m () -> m ()) -> Register m a -> m (a, m ())
runRegister_ read write (Register m) = do
    ((a, tick), s) <- flip runStateT initAllReferenceState $ do
        r <- newRef mempty
        a <- runReaderT m (write, r)
        (w, _) <- readRef r
        return (a, runMonadMonoid w)
    let eval s = flip evalStateT s $ forever $ do
            join $ lift read
            tick
    return $ (,) a $ eval s

------------------------------------

onChangeAcc r b0 c0 f = Register $ do
    ff <- asks fst
    magnify _2 $ toSend r b0 c0 $ \b b' c' -> liftM (\x -> evalRegister' ff . x) $ evalRegister' ff $ f b b' c'

type Register_ m
    = ReaderT (RegRef m) m

toSend
    :: (Eq b, MonadRefCreator m, MonadRefWriter m)
    => RefReader m b
    -> b -> (b -> c)
    -> (b -> b -> c -> {-Either (Register m c)-} Register_ m (c -> Register_ m c))
    -> Register_ m (RefReader m c)
toSend rb b0 c0 fb = do
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
                writeRef memoref ((b, cc), filter ((/= b) . fst) (last:memo))
                return cc
            doit st1
            doit st2

    tell' (act, mempty)
    return $ readRef $ (_1 . _2 . _2) `lensMap` memoref

------------------------

runTests :: IO ()
#ifdef __TESTS__
runTests = tests runTest

runTest :: (Eq a, Show a) => String -> Register (Prog TP) a -> Prog' (a, Prog' ()) -> IO ()
runTest name = runTest_ name (TP . lift) $ \r w -> runRegister_ (liftM unTP r) (w . TP)

newtype TP = TP { unTP :: SLSt (Prog TP) () }
#else
runTests = fail "enable the tests flag like \'cabal configure --enable-tests -ftests; cabal build; cabal test\'"
#endif

