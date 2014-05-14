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
{-# OPTIONS_HADDOCK hide #-}
module Data.LensRef.Common where

import Data.Monoid
import Control.Concurrent
import Control.Monad.State
import Control.Monad.Writer
import Control.Monad.Reader
import Control.Monad.Identity

import Data.LensRef

----------------

-- Ref-based WriterT
type RefWriterT w m = ReaderT (Ref m w) m

runRefWriterT :: (MonadRefCreator m, Monoid w) => RefWriterT w m a -> m (a, Ref m w)
runRefWriterT m = do
    r <- newRef mempty
    a <- runReaderT m r
    return (a, r)

tell' :: (Monoid w, MonadRefCreator m, MonadRefWriter m) => w -> RefWriterT w m ()
tell' w = ReaderT $ \m -> modRef m (`mappend` w)

-------------

newtype MonadMonoid a = MonadMonoid { runMonadMonoid :: a () }

instance Monad m => Monoid (MonadMonoid m) where
    mempty = MonadMonoid $ return ()
    MonadMonoid a `mappend` MonadMonoid b = MonadMonoid $ a >> b


------------------------

newtype Morph m n = Morph { runMorph :: forall a . m a -> n a }

type SRef m a = Morph (StateT a m) m

class Monad m => NewRef m where
    newRef' :: a -> m (SRef m a)
{-
instance Monad m => NewRef (StateT LSt m) where
    newRef' x = do
        v <- newRef x
        return $ Morph $ \m -> do
            x <- readRef v
            (y, x) <- runStateT m x
            writeRef v x
            return y
-}
instance NewRef IO where
    newRef' x = do
        vx <- liftIO $ newMVar x
        return $ Morph $ \m -> modifyMVar vx $ liftM swap . runStateT m
      where
        swap (a, b) = (b, a)

instance NewRef m => NewRef (StateT s m) where
    newRef' x = lift $ flip liftM (newRef' x) $ \r ->
        Morph $ \m -> StateT $ \s -> runMorph r $ flip mapStateT m $ \k -> flip liftM (runStateT k s) $ \((x, w), s) -> ((x, s), w)

instance (Monoid w, NewRef m) => NewRef (WriterT w m) where
    newRef' x = lift $ flip liftM (newRef' x) $ \r ->
        Morph $ \m -> WriterT $ runMorph r $ flip mapStateT m $ \k -> flip liftM (runWriterT k) $ \((x, s), w) -> ((x, w), s)

instance NewRef m => NewRef (ReaderT r m) where
    newRef' x = lift $ flip liftM (newRef' x) $ \r ->
        Morph $ \m -> ReaderT $ \st -> runMorph r $ flip mapStateT m $ flip runReaderT st

---------------------------

{-
    memoWrite = memoWrite_

    future = future_

future_ :: (MonadRefCreator m, MonadRefWriter m) => (RefReader m a -> m a) -> m a
future_ f = do
    s <- newRef $ error "can't see the future"
    a <- f $ readRef s
    writeRef s a
    return a
-}
memoRead_ :: (MonadRefWriter m, MonadRefCreator m) => m a -> m (m a) 
memoRead_ g = do
    s <- newRef Nothing
    return $ readRef s >>= \x -> case x of
        Just a -> return a
        _ -> g >>= \a -> do
            writeRef s $ Just a
            return a

{-
memoWrite_ g = do
    s <- newRef Nothing
    return $ \b -> readRef s >>= \x -> case x of
        Just (b', a) | b' == b -> return a
        _ -> g b >>= \a -> do
            writeRef s $ Just (b, a)
            return a
-}


