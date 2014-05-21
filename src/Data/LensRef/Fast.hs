{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE CPP #-}
-- {-# OPTIONS_HADDOCK hide #-}
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
    , runTests
    ) where

import Data.Monoid
import Control.Applicative hiding (empty)
import Control.Monad.State
import Control.Monad.Writer
import Control.Monad.Reader
import Control.Arrow ((***))
import Control.Lens.Simple

import Data.LensRef.Class
import Data.LensRef.Common
#ifdef __TESTS__
import Data.LensRef.TestEnv hiding (listen)
import Data.LensRef.Test
#endif

----------------------

data RefReaderT m a = RefReaderT
    { value :: m a
    , registerOnChange :: m () -> WriterT (RegionStatusChangeHandler (MonadMonoid m)) m ()
        -- the action will be executed after each value change
    }

refReaderT m = RefReaderT
    { value = m
    , registerOnChange = firstTime $ const $ return $ const $ return ()
    }

firstTime f y = do
    _ <- lift y
    h <- lift $ f y
    tell h


instance Functor m => Functor (RefReaderT m) where
    fmap f mr = RefReaderT
        { value = fmap f $ value mr
        , registerOnChange = registerOnChange mr
        }

instance NewRef m => Applicative (RefReaderT m) where
    pure a = refReaderT $ return a
    mf <*> ma = liftM2 ($) mf ma -- TODO: optimize this

instance NewRef m => Monad (RefReaderT m) where

    return a = pure a

    mr >>= f = RefReaderT
        { value = value mr >>= value . f
        , registerOnChange = \action -> do
            r <- lift $ newRef' $ const $ return ()
            registerOnChange mr $ do
                v <- value mr
                runMorph r $ StateT $ \innerhandler -> do
                    runMonadMonoid $ innerhandler Kill
                    newinnerhandler <- execWriterT $ registerOnChange (f v) action
                    return ((), newinnerhandler)
            tell $ \inst -> do
                innerhandler <- lift $ runMorph r get
                innerhandler inst
        }

newtype instance RefWriterOf (RefReaderT m) a = RefWriterT
    { runRefWriterT :: m a
    }
        deriving (Monad, MonadFix, Applicative, Functor)

type RefWriterT m = RefWriterOf (RefReaderT m)

data RefCore_ (m :: * -> *) a = RefCore_ 
    { readPart  :: RefReaderT m a
    , writePart :: a -> RefWriterT m ()
    }

instance NewRef m => MonadRefReader (RefReaderT m) where

    type BaseRef (RefReaderT m) = RefCore_ m

    liftRefReader = id

instance NewRef m => MonadRefReader (RefWriterOf (RefReaderT m)) where

    type BaseRef (RefWriterOf (RefReaderT m)) = RefCore_ m

    liftRefReader = RefWriterT . value


newtype RefCreatorT m a = RefCreatorT
    { runRefCreatorT :: WriterT (RegionStatusChangeHandler (MonadMonoid m)) m a
    }
        deriving (Monad, MonadFix, Applicative, Functor)

refCreatorT m = RefCreatorT
    { runRefCreatorT = lift m
    }

instance NewRef m => MonadRefReader (RefCreatorT m) where

    type BaseRef (RefCreatorT m) = RefCore_ m

    liftRefReader = refCreatorT . value


instance NewRef m => RefClass (RefCore_ m) where

    type RefReaderSimple (RefCore_ m) = RefReaderT m

    readRefSimple = join . fmap readPart

    writeRefSimple mr a
        = liftRefReader mr >>= flip writePart a

    lensMap k = fmap $ \(RefCore_ r w) -> RefCore_
            { readPart  = fmap (^. k) r
            , writePart = \b -> liftRefReader r >>= w . set k b
            }

    unitRef = return RefCore_
                { readPart  = return ()
                , writePart = const $ return ()
                }


instance NewRef m => MonadRefWriter (RefWriterOf (RefReaderT m)) where
    liftRefWriter = id

instance NewRef m => MonadRefWriter (RefCreatorT m) where
    liftRefWriter = RefCreatorT . lift . runRefWriterT

instance NewRef m => MonadRefCreator (RefCreatorT m) where

    extRef mr r2 a0 = RefCreatorT $ do
        ra <- lift $ newRef' a0
        rqueue <- lift $ newRef' emptyQueue
        status <- lift $ newRef' True -- True: normal; False:

        registerOnChange (readRefSimple mr) $ do
            s <- runMorph status get
            when s $ do
                b <- value $ readRefSimple mr
                runMorph ra $ modify $ set r2 b
                runMorph status $ put False
                join $ runMorph rqueue $ gets $ sequence_ . queueElems
                runMorph status $ put True

        return $
            return RefCore_
                { readPart = RefReaderT
                    { value = runMorph ra get
                    , registerOnChange = firstTime $ runMorph rqueue . state . addElem' rqueue
                    }
                , writePart = \a -> RefWriterT $ do
                    runMorph ra $ put a
                    runMorph status $ put False
                    runRefWriterT $ writeRefSimple mr $ a ^. r2
                    join $ runMorph rqueue $ gets $ sequence_ . queueElems
                    runMorph status $ put True
                }

    newRef = RefCreatorT . lift . newRef_

newRef_ a0 = do
    ra <- newRef' a0
    rqueue <- newRef' emptyQueue
    return $ return RefCore_
            { readPart = RefReaderT
                { value = runMorph ra get
                , registerOnChange = firstTime $ runMorph rqueue . state . addElem' rqueue
                }
            , writePart = \a -> RefWriterT $ do
                runMorph ra $ put a
                join $ runMorph rqueue $ gets $ sequence_ . queueElems
            }

addElem' r a q = f *** id $ addElem a q where
    f (_, del) inst = MonadMonoid $ do
        as <- runMorph r $ StateT $ \s -> return $ del inst s
        sequence_ as


type Queue a = (Int, [(Int, (Bool{-False: blocked-}, a))])

emptyQueue :: Queue a
emptyQueue = (0, [])

queueElems :: Queue a -> [a]
queueElems = map snd . filter fst . map snd . snd
{-
mapMQueue :: (Monad m) => (a -> m b) -> Queue a -> m (Queue b)
mapMQueue f (j, xs) = do
    vs <- mapM (f . snd) xs
    return (j, zip (map fst xs) vs)
-}
addElem :: a -> Queue a -> ((Queue a -> a, RegionStatusChange -> Queue a -> ([a], Queue a)), Queue a)
addElem a (i, as) = ((getElem i, delElem i), (i+1, (i,(True,a)):as))
  where
    getElem i = snd . snd . head . filter ((==i) . fst) . snd
    delElem i inst (j, is) = (concat as, (j, concat is')) where
        (as, is') = unzip $ map f is
        f (i', (_, a)) | i' == i = case inst of
            Kill -> ([], [])
            Block -> ([], [(i, (False, a))])
            Unblock -> ([a], [(i, (True, a))])
        f x = ([], [x])
{-
sumQueue :: Monoid a => Queue a -> a
sumQueue = mconcat . queueElems
-}

instance NewRef m => MonadMemo (RefCreatorT m) where
    memoRead = memoRead_

instance NewRef m => MonadRefWriter (RefReaderT m) where
    liftRefWriter (RefWriterT m) = refReaderT m

---------------------------------

newtype Register m a
    = Reg { unReg :: ReaderT ( m () -> m ()         -- postpone to next cycle
                             , SRef m ( MonadMonoid m ()         -- postponed onChange events
--                                      , RegionStatusChange -> MonadMonoid (Register m) ()        -- ??
                                      )
                             )
                             (RefCreatorT m)
                             a
          }
        deriving (Monad, Applicative, Functor, MonadFix)

instance NewRef m => MonadRefReader (Register m) where
    type BaseRef (Register m) = RefCore_ m
    liftRefReader = Reg . lift . liftRefReader

instance NewRef m => MonadRefWriter (Register m) where
    liftRefWriter = Reg . lift . liftRefWriter

instance NewRef m => MonadMemo (Register m) where
    memoRead = memoRead_

instance NewRef m => MonadRefCreator (Register m) where
    extRef r l = Reg . lift . extRef r l
    newRef = Reg . lift . newRef

instance NewRef m => MonadEffect (Register m) where
    type EffectM (Register m) = m
    liftEffectM = Reg . lift . refCreatorT

instance NewRef m => MonadEffect (RefWriterOf (RefReaderT m)) where
    type EffectM (RefWriterOf (RefReaderT m)) = m
    liftEffectM = RefWriterT

instance NewRef m => MonadRegister (Register m) where

    type Modifier (Register m) = RefWriterT  m

    onChange mr f = Reg $ ReaderT $ \st -> RefCreatorT $ do
        v <- lift $ value mr
        (y, h1) <- lift $ runWriterT $ runRefCreatorT $ flip runReaderT st $ unReg $ f v
        nr <- lift $ newRef_ (v, (h1, y))

        let ev = do
                v <- value mr
                (vold, (h1_, _)) <- value $ readRefSimple nr
                if v == vold
                  then return ()
                  else do
                    runMonadMonoid $ h1_ Kill
                    (y, h1) <- runWriterT $ runRefCreatorT $ flip runReaderT st $ unReg $ f v
                    runRefWriterT $ writeRef nr (v, (h1, y))

        registerOnChange mr $ do
            runMorph (snd st) $ modify (`mappend` MonadMonoid ev)

        return $ readRef $ (_2 . _2) `lensMap` nr

    onChangeMemo mr f = Reg $ ReaderT $ \st -> RefCreatorT $ do
        v <- lift $ value mr
        (my, h1) <- lift $ runWriterT $ runRefCreatorT $ flip runReaderT st $ unReg $ f v
        (y, h2) <- lift $ runWriterT $ runRefCreatorT $ flip runReaderT st $ unReg $ my
        nr <- lift $ newRef_ ((v, ((my, h1, h2), y)), [])

        let ev = do
                v <- value mr
                (la@(vold, ((_, h1_, h2_), _)), others) <- value $ readRefSimple nr
                let others' = la: others
                if v == vold
                  then return ()
                  else do
                    runMonadMonoid $ h1_ Block
                    runMonadMonoid $ h2_ Kill
                    case lookup v others of
                      Just ((my, h1, _), _) -> do
                        runMonadMonoid $ h1 Unblock
                        (y, h2) <- runWriterT $ runRefCreatorT $ flip runReaderT st $ unReg $ my
                        runRefWriterT $ writeRef nr ((v, ((my, h1, h2), y)), filter ((/=v) . fst) $ others')
                      Nothing -> do
                        (my, h1) <- runWriterT $ runRefCreatorT $ flip runReaderT st $ unReg $ f v
                        (y, h2) <- runWriterT $ runRefCreatorT $ flip runReaderT st $ unReg $ my
                        runRefWriterT $ writeRef nr ((v, ((my, h1, h2), y)), others')

        registerOnChange mr $ do
            runMorph (snd st) $ modify (`mappend` MonadMonoid ev)

        return $ readRef $ (_1 . _2 . _2) `lensMap` nr

    registerCallback f = Reg $ ReaderT $ \(st, _) -> do
        let g = st . runRefWriterT
        return $ fmap g f

    onRegionStatusChange g = Reg $ ReaderT $ \_ -> do
        RefCreatorT $ tell $ MonadMonoid . g


runRegister :: NewRef m => (forall a . m (m a, a -> m ())) -> Register m a -> m (a, m ())
runRegister newChan m = do
    (read, write) <- newChan
    runRegister_ read write m


runRegister_ :: NewRef m => (m (m ())) -> (m () -> m ()) -> Register m a -> m (a, m ())
runRegister_ read write (Reg m) = do
    (a, tick) <- do
        r <- newRef' mempty
        a <- fmap fst $ runWriterT $ runRefCreatorT $ runReaderT m (write, r)        -- fmap fst!!!
        return (a, r)
    return $ (,) a $ forever $ do
        join read
        k <- runMorph tick $ state $ \s -> (s, mempty)
        runMonadMonoid k

--------------------------

runTests :: IO ()
#ifdef __TESTS__
runTests = tests runTest

runTest :: (Eq a, Show a) => String -> Register (Prog TP) a -> Prog' (a, Prog' ()) -> IO ()
runTest name = runTest_ name TP $ \r w -> runRegister_ (liftM unTP r) (w . TP)

newtype TP = TP { unTP :: Prog TP () }
#else
runTests = fail "enable the tests flag like \'cabal configure --enable-tests -ftests; cabal build; cabal test\'"
#endif

