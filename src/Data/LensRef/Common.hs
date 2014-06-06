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
import Data.Maybe
import Data.List
import qualified Data.IntSet as IntSet
import qualified Data.IntMap as IntMap
import Control.Applicative
import Control.Concurrent
import Control.Monad.State
import Control.Monad.Writer
import Control.Monad.Reader
--import Control.Lens.Simple

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

type SRef m a = Morph (StateT a m) m

data OrdRef m a = OrdRef
    { ordRefId :: Int
    , ordRefRef :: SRef m a
    }

instance Eq (OrdRef m a) where
    OrdRef i _ == OrdRef j _ = i == j

instance Ord (OrdRef m a) where
    OrdRef i _ `compare` OrdRef j _ = i `compare` j

newOrdRef :: NewRef m => a -> m (OrdRef m a)
newOrdRef a = liftA2 OrdRef newId (newRef' a)

runOrdRef :: NewRef m => OrdRef m a -> StateT a m b -> m b
runOrdRef (OrdRef _ r) f = runMorph r f

type OrdRefSet m a = IntMap.IntMap (SRef m a)

insertOrdRef, deleteOrdRef :: OrdRef m a -> OrdRefSet m a -> OrdRefSet m a
insertOrdRef (OrdRef i r) = IntMap.insert i r
deleteOrdRef (OrdRef i _) = IntMap.delete i

ordRefToList :: OrdRefSet m a -> [OrdRef m a]
ordRefToList = map (uncurry OrdRef) . IntMap.toList

ordRefMember :: OrdRef m a -> OrdRefSet m a -> Bool
ordRefMember (OrdRef i _) = IntMap.member i

ordRefDifference = IntMap.difference

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
memoRead_ :: MonadRefCreator m => (Ref m (Maybe a) -> Maybe a -> m ()) -> m a -> m (m a) 
memoRead_ writeRef g = do
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

---------------------------------

-- | topological sorting on component
topSortComponent
    :: (Int -> [Int])   -- ^ children
    -> Int              -- ^ starting point
    -> Maybe [Int]
topSortComponent ch a = topSort (walk a) [a]
  where
    topSort par []
        | IntMap.null par = Just []
        | otherwise = Nothing
    topSort par (p:ps) = fmap (p:) $ topSort par' $ merge ps ys
      where
        xs = ch p
        par' = foldr (IntMap.adjust $ filter (/= p)) (IntMap.delete p par) xs
        ys = sort $ filter (null . (par' IntMap.!)) xs    -- TODO: eliminate sort

    walk v = execState (collects v) $ IntMap.singleton v []

    collects v = mapM_ (collect v) $ ch v
    collect p v = do
        visited <- gets $ IntMap.member v
        modify $ IntMap.alter (Just . (p:) . fromMaybe []) v
        when (not visited) $ collects v

topSortComponentM
    :: (Monad m, Applicative m, a ~ OrdRef m b)
    => (a -> SRef m (IntMap.IntMap (SRef m b)))    -- ^ howto store values in a
    -> (a -> m [a])   -- ^ children; should be ordered
    -> [a]            -- ^ starting points
    -> m (Maybe [a])
topSortComponentM store ch as = mapM_ collects as >> topSort as
  where
    topSort [] = pure $ Just []
--        | Map.null par = pure $ Just []
--        | otherwise = pure $ Nothing
    topSort (p:ps) = do
        xs <- ch p
        runMorph (store p) $ put mempty
        forM_ xs $ \x -> runMorph (store x) $ modify $ deleteOrdRef p
        ys <- filterM (flip runMorph (gets IntMap.null) . store) xs
        fmap (fmap (p:)) $ topSort $ merge ps ys

    collects v = mapM_ (collect v) =<< ch v
    collect p v = do
        notvisited <- runMorph (store v) $ gets IntMap.null
        runMorph (store v) $ modify $ insertOrdRef p
        when notvisited $ collects v

merge :: Ord a => [a] -> [a] -> [a]
merge [] xs = xs
merge xs [] = xs
merge (x:xs) (y:ys) = case compare x y of
    LT -> x: merge xs (y:ys)
    GT -> y: merge (x:xs) ys
    EQ -> x: merge xs ys

allUnique :: [Int] -> Bool
allUnique = and . flip evalState mempty . mapM f where
    f x = state $ \s -> (IntSet.notMember x s, IntSet.insert x s)

readerToState :: (Monad m, Applicative m) => (s -> r) -> ReaderT r m a -> StateT s m a
readerToState g (ReaderT f) = StateT $ \s -> fmap (flip (,) s) $ f $ g s

nextKey :: IntMap.IntMap a -> Int
nextKey = maybe 0 ((+1) . fst . fst) . IntMap.maxViewWithKey


