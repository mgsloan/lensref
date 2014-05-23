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
import Control.Monad.Writer
import Control.Monad.Reader
import Control.Monad.Identity
import Control.Lens.Simple

import Unsafe.Coerce

import Data.LensRef.Class
import Data.LensRef.Common
#ifdef __TESTS__
import Data.LensRef.TestEnv
import Data.LensRef.Test
#endif

----------------------

newtype instance RefWriterOf (RefReaderT m) a
    = RefWriterOfReaderT { runRefWriterOfReaderT :: RefWriterT m a }
        deriving (Monad, Applicative, Functor)

----------------------

newtype Reference b = Reference {unwrapLens :: Lens' AllReferenceState b}

joinLens :: RefReaderT Identity (Reference b) -> Lens' AllReferenceState b
joinLens r f a = unwrapLens (runReader r a) f a

type AllReferenceState = [ReferenceState]

data ReferenceState where
    ReferenceState :: (AllReferenceState -> a -> a) -> a -> ReferenceState

type RefWriterT = StateT AllReferenceState
type RefReaderT = ReaderT AllReferenceState

initAllReferenceState :: AllReferenceState
initAllReferenceState = []

instance MonadRefReader (RefReaderT Identity) where
    type BaseRef (RefReaderT Identity) = Reference
    liftRefReader = id

instance (Monad m, Applicative m) => MonadRefReader (RefWriterOf (RefReaderT m)) where
    type BaseRef (RefWriterOf (RefReaderT m)) = Reference
    liftRefReader = RefWriterOfReaderT . gets . runReader

instance (Monad m, Applicative m) => MonadRefWriter (RefWriterOf (RefReaderT m)) where
    liftRefWriter = RefWriterOfReaderT . mapStateT (pure . runIdentity) . runRefWriterOfReaderT

instance RefClass (Reference) where
    type RefReaderSimple (Reference) = (RefReaderT Identity)

    readRefSimple r = view $ joinLens r
    writeRefSimple r a = RefWriterOfReaderT $ joinLens r .= a
    lensMap l r = pure $ Reference $ joinLens r . l
    unitRef = pure $ Reference united

instance (Monad m, Applicative m) => MonadRefReader (RefWriterT m) where
    type BaseRef (RefWriterT m) = Reference

    liftRefReader = gets . runReader

instance (Monad m, Applicative m) => MonadRefCreator (RefWriterT m) where
    extRef r r2 a0 = state extend
      where
        rk = set (joinLens r) . (^. r2)
        kr = set r2 . (^. joinLens r)

        extend x0 = (pure $ Reference $ lens get set, x0 ++ [ReferenceState kr (kr x0 a0)])
          where
            limit = splitAt (length x0)

            get = unsafeData . head . snd . limit

            set x a = foldl (\x -> (x++) . (:[]) . ap_ x) (rk a zs ++ [ReferenceState kr a]) ys where
                (zs, _ : ys) = limit x

        ap_ :: AllReferenceState -> ReferenceState -> ReferenceState
        ap_ x (ReferenceState f a) = ReferenceState f (f x a)

        unsafeData :: ReferenceState -> a
        unsafeData (ReferenceState _ a) = unsafeCoerce a


instance (Monad m, Applicative m) => MonadMemo (RefWriterT m) where
    memoRead = memoRead_

instance (Monad m, Applicative m) => MonadRefWriter (RefWriterT m) where
    liftRefWriter = state . runState . runRefWriterOfReaderT


---------------------------------

type ISt m
    = (MonadMonoid m (), RegionStatusChange -> MonadMonoid m ())

newtype Register m a
    = Register { unRegister :: ReaderT (RefWriterT m () -> m ()) (WriterT (ISt (RefWriterT m)) (RefWriterT m)) a }
        deriving (Monad, Applicative, Functor, MonadFix)

instance (Monad m, Applicative m) => MonadRefReader (Register m) where
    type BaseRef (Register m) = Reference
    liftRefReader = Register . lift . lift . liftRefReader

instance (Monad m, Applicative m) => MonadRefCreator (Register m) where
    extRef r l = Register . lift . lift . extRef r l
    newRef = Register . lift . lift . newRef

instance (Monad m, Applicative m) => MonadMemo (Register m) where
    memoRead = memoRead_

instance (Monad m, Applicative m) => MonadRefWriter (Register m) where
    liftRefWriter = Register . lift . lift . liftRefWriter

instance (Monad m, Applicative m) => MonadEffect (RefWriterOf (RefReaderT m)) where
    type EffectM (RefWriterOf (RefReaderT m)) = m
    liftEffectM = RefWriterOfReaderT . lift

instance (Monad m, Applicative m) => MonadEffect (Register m) where
    type EffectM (Register m) = m
    liftEffectM = Register . lift . lift . lift

instance (Monad m, Applicative m) => MonadRegister (Register m) where

    type Modifier (Register m) = RefWriterOf (RefReaderT m)

    onChangeMemo r f = onChangeAcc r undefined undefined $ \b _ _ -> fmap const $ f b

    askPostpone = fmap (\f -> f . runRefWriterOfReaderT) $ Register ask

    onRegionStatusChange g = Register $ tell (mempty, MonadMonoid . lift . g)

runRegister :: (Monad m, Applicative m) => (forall a . m (m a, a -> m ())) -> Register m a -> m (a, m ())
runRegister newChan m = do
    (read, write) <- newChan
    runRegister_ read write m


runRegister_ :: (Monad m, Applicative m) => m (RefWriterT m ()) -> (RefWriterT m () -> m ()) -> Register m a -> m (a, m ())
runRegister_ read write (Register m) = do
    ((a, tick), s) <- flip runStateT initAllReferenceState $ do
        (a, (w, _)) <- runWriterT $ runReaderT m write
        pure (a, runMonadMonoid w)
    let eval s = flip evalStateT s $ forever $ do
            join $ lift read
            tick
    pure $ (,) a $ eval s

------------------------------------

onChangeAcc r b0 c0 f = Register $ ReaderT $ \ff -> 
    toSend r b0 c0 $ \b b' c' -> fmap (\x -> evalRegister' ff . x) $ evalRegister' ff $ f b b' c'
  where
    evalRegister' ff (Register m) = runReaderT m ff


type Register_ m
    = WriterT (ISt m) m

toSend
    :: (Eq b, MonadRefCreator m, MonadRefWriter m)
    => RefReader m b
    -> b -> (b -> c)
    -> (b -> b -> c -> {-Either (Register m c)-} Register_ m (c -> Register_ m c))
    -> Register_ m (RefReader m c)
toSend rb b0 c0 fb = do
    let doit = runMonadMonoid . fst
        reg (_, st) = runMonadMonoid . st

    memoref <- lift $ do
        b <- liftRefReader rb
        (c, st1) <- runWriterT $ fb b b0 $ c0 b0
        (val, st2) <- runWriterT $ c $ c0 b0
        doit st1
        doit st2
        newRef ((b, (c, val, st1, st2)), [])      -- memo table

    let act = MonadMonoid $ do
            b <- liftRefReader rb
            (last@(b', cc@(_, oldval, st1, st2)), memo) <- readRef memoref
            (_, _, st1, st2) <- if b' == b
              then
                pure cc
              else do
                reg st1 Block
                reg st2 Kill
                (c, oldval', st1, _) <- case lookup b memo of
                  Nothing -> do
                    (c, st1) <- runWriterT $ fb b b' oldval
                    pure (c, c0 b, st1, undefined)
                  Just cc'@(_, _, st1, _) -> do
                    reg st1 Unblock
                    pure cc'
                (val, st2) <- runWriterT $ c oldval'
                let cc = (c, val, st1, st2)
                writeRef memoref ((b, cc), filter ((/= b) . fst) (last:memo))
                pure cc
            doit st1
            doit st2

    tell (act, mempty)
    pure $ readRef $ (_1 . _2 . _2) `lensMap` memoref

------------------------

runTests :: IO ()
#ifdef __TESTS__
runTests = tests runTest

runTest :: (Eq a, Show a) => String -> Register (Prog TP) a -> Prog' (a, Prog' ()) -> IO ()
runTest name = runTest_ name (TP . lift) $ \r w -> runRegister_ (fmap unTP r) (w . TP)

newtype TP = TP { unTP :: RefWriterT (Prog TP) () }
#else
runTests = fail "enable the tests flag like \'cabal configure --enable-tests -ftests; cabal build; cabal test\'"
#endif

