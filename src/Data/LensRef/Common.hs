{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}
-- {-# OPTIONS_HADDOCK hide #-}
module Data.LensRef.Common where

import Data.Monoid
import Control.Applicative
import Control.Concurrent
import Control.Monad.State
import Control.Monad.Writer
import Control.Monad.Reader

import System.IO.Unsafe

import Data.LensRef.Class

-------------

newtype MonadMonoid m a = MonadMonoid
    { runMonadMonoid :: m a }
        deriving (Monad, Applicative, Functor)

instance MonadTrans MonadMonoid where
    lift = MonadMonoid

-- Applicative would be enough
instance (Monad m, Monoid a) => Monoid (MonadMonoid m a) where
    mempty = MonadMonoid $ return mempty
    MonadMonoid a `mappend` MonadMonoid b = MonadMonoid $ liftM2 mappend a b


------------------------

newtype Morph m n = Morph { runMorph :: forall a . m a -> n a }

type SRef m a = Morph (StateT a m) m

class (Monad m, Applicative m) => NewRef m where
    newRef' :: a -> m (SRef m a)
    newId   :: m Int
{-
instance Monad m => NewRef (StateT LSt m) where
    newRef' x = do
        v <- newRef x
        pure $ Morph $ \m -> do
            x <- readRef v
            (y, x) <- runStateT m x
            writeRef v x
            pure y
-}
counter = unsafePerformIO $ newMVar (0 :: Int)

instance NewRef IO where
    newRef' x = do
        vx <- liftIO $ newMVar x
        pure $ Morph $ \m -> modifyMVar vx $ fmap swap . runStateT m
      where
        swap (a, b) = (b, a)
    newId = modifyMVar counter $ \c -> return (succ c, c)

instance NewRef m => NewRef (StateT s m) where
    newRef' x = lift $ flip fmap (newRef' x) $ \r ->
        Morph $ \m -> StateT $ \s -> runMorph r $ flip mapStateT m $ \k -> flip fmap (runStateT k s) $ \((x, w), s) -> ((x, s), w)
    newId = lift newId

instance (Monoid w, NewRef m) => NewRef (WriterT w m) where
    newRef' x = lift $ flip fmap (newRef' x) $ \r ->
        Morph $ \m -> WriterT $ runMorph r $ flip mapStateT m $ \k -> flip fmap (runWriterT k) $ \((x, s), w) -> ((x, w), s)
    newId = lift newId

instance NewRef m => NewRef (ReaderT r m) where
    newRef' x = lift $ flip fmap (newRef' x) $ \r ->
        Morph $ \m -> ReaderT $ \st -> runMorph r $ flip mapStateT m $ flip runReaderT st
    newId = lift newId

---------------------------

{-
    memoWrite = memoWrite_

    future = future_

future_ :: (MonadRefCreator m, MonadRefWriter m) => (RefReader m a -> m a) -> m a
future_ f = do
    s <- newRef $ error "can't see the future"
    a <- f $ readRef s
    writeRef s a
    pure a
-}
memoRead_ :: (MonadRefWriter m, MonadRefCreator m) => m a -> m (m a) 
memoRead_ g = do
    s <- newRef Nothing
    pure $ readRef s >>= \x -> case x of
        Just a -> pure a
        _ -> g >>= \a -> do
            writeRef s $ Just a
            pure a

{-
memoWrite_ g = do
    s <- newRef Nothing
    pure $ \b -> readRef s >>= \x -> case x of
        Just (b', a) | b' == b -> pure a
        _ -> g b >>= \a -> do
            writeRef s $ Just (b, a)
            pure a
-}


