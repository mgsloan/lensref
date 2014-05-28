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

import Data.Maybe
import Data.Monoid
import Data.Function
import Data.List
import qualified Data.IntMap as IMap
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

data RefReaderT m a
    = RefReaderT
        { value_ :: m a
        , registerOnChange_ :: m () -> WriterT (RegionStatusChangeHandler (MonadMonoid m)) m ()
            -- the action will be executed after each value change
        }
    | RefReaderTPure a

value (RefReaderTPure a) = pure a
value x = value_ x

registerOnChange (RefReaderTPure _) = firstTime $ const $ pure $ const $ pure ()
registerOnChange x = registerOnChange_ x

firstTime f y = do
    _ <- lift y
    h <- lift $ f y
    tell h


instance (Monad m, Applicative m) => Functor (RefReaderT m) where
    fmap f (RefReaderTPure x) = RefReaderTPure $ f x
    fmap f mr = RefReaderT
        { value_ = fmap f $ value mr
        , registerOnChange_ = registerOnChange mr
        }

instance NewRef m => Applicative (RefReaderT m) where
    pure a = RefReaderTPure a
    RefReaderTPure f <*> RefReaderTPure a = RefReaderTPure $ f a
    mf <*> ma = RefReaderT
        { value_ = value mf <*> value ma
        , registerOnChange_ = liftA2 f (registerOnChange mf) (registerOnChange ma)
        }
      where
        f (WriterT m1) (WriterT m2) = WriterT $ liftA2 mappend m1 m2

instance NewRef m => Monad (RefReaderT m) where

    return a = pure a

    RefReaderTPure r >>= f = f r
    mr >>= f = RefReaderT
        { value_ = value mr >>= value . f
        , registerOnChange_ = \action -> do
            r <- lift $ newRef' $ const $ pure ()
            registerOnChange mr $ do
                runMorph r $ StateT $ \innerhandler -> do
                    runMonadMonoid $ innerhandler Kill
                    v <- value mr
                    newinnerhandler <- execWriterT $ registerOnChange (f v) action
                    pure ((), newinnerhandler)
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


join_ = join   

instance NewRef m => RefClass (RefCore_ m) where

    type RefReaderSimple (RefCore_ m) = RefReaderT m

    readRefSimple = join_ . fmap readPart

    writeRefSimple mr a
        = liftRefReader mr >>= flip writePart a

    lensMap k = fmap $ \(RefCore_ r w) -> RefCore_
            { readPart  = fmap (^. k) r
            , writePart = \b -> liftRefReader r >>= w . set k b
            }

    unitRef = pure RefCore_
                { readPart  = pure ()
                , writePart = const $ pure ()
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

        lift $ fmap fst $ runWriterT $ registerOnChange (readRefSimple mr) $ do
            s <- runMorph status get
            when s $ do
                b <- value $ readRefSimple mr
                runMorph ra $ modify $ set r2 b
                runMorph status $ put False
                join $ runMorph rqueue $ gets $ sequence_ . queueElems
                runMorph status $ put True

        pure $
            pure RefCore_
                { readPart = RefReaderT
                    { value_ = runMorph ra get
                    , registerOnChange_ = firstTime $ runMorph rqueue . state . addElem' rqueue
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
    pure $ pure RefCore_
            { readPart = RefReaderT
                { value_ = runMorph ra get
                , registerOnChange_ = firstTime $ runMorph rqueue . state . addElem' rqueue
                }
            , writePart = \a -> RefWriterT $ do
                runMorph ra $ put a
                join $ runMorph rqueue $ gets $ sequence_ . queueElems
            }

addElem' r a q = f *** id $ addElem a q where
    f (_, del) inst = MonadMonoid $ do
        as <- runMorph r $ StateT $ \s -> pure $ del inst s
        sequence_ as


type Queue a = IMap.IntMap (Bool{-False: blocked-}, a)

emptyQueue :: Queue a
emptyQueue = IMap.empty

queueElems :: Queue a -> [a]
queueElems = map snd . filter fst . IMap.elems
{-
mapMQueue :: (Monad m) => (a -> m b) -> Queue a -> m (Queue b)
mapMQueue f (j, xs) = do
    vs <- mapM (f . snd) xs
    pure (j, zip (map fst xs) vs)
-}
addElem :: a -> Queue a -> ((Queue a -> a, RegionStatusChange -> Queue a -> ([a], Queue a)), Queue a)
addElem a as = ((getElem, delElem), IMap.insert i (True,a) as)
  where
    i = maybe 0 ((+1) . fst . fst) $ IMap.maxViewWithKey as

    getElem is = snd $ is IMap.! i
--    delElem _ is = ([], is)  -- !!!
    delElem Kill is = ([], IMap.delete i is)
    delElem Block is = ([], IMap.adjust ((set _1) False) i is)
    delElem Unblock is = (map snd $ maybeToList $ IMap.lookup i is, IMap.adjust ((set _1) True) i is)
{-
sumQueue :: Monoid a => Queue a -> a
sumQueue = mconcat . queueElems
-}

instance NewRef m => MonadMemo (RefCreatorT m) where
    memoRead = memoRead_

---------------------------------

newtype Register m a
    = Reg { unReg :: ReaderT ( m () -> m ()         -- postpone to next cycle
                             , SRef m ( [(Int, m ())]         -- postponed onChange events
--                                      , RegionStatusChange -> MonadMonoid (Register m) ()        -- ??
                                      )
                             , SRef m Int -- ticker
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

    onChange (RefReaderTPure x) f = fmap pure $ f x
    onChange mr f = Reg $ ReaderT $ \st@(_, st2, ticker) -> RefCreatorT $ do
        v <- lift $ value mr
        (y, h1) <- lift $ runWriterT $ runRefCreatorT $ flip runReaderT st $ unReg $ f v
        ti <- lift $ runMorph ticker $ state $ \s -> (s, succ s)
        nr <- lift $ newRef' (v, (h1, y))

        let ev = do
              (vold, (h1_, _)) <- runMorph nr get
              v <- value mr
              if v == vold
                  then pure ()
                  else do
                    runMonadMonoid $ h1_ Kill
                    (y, h1) <- runWriterT $ runRefCreatorT $ flip runReaderT st $ unReg $ f v
                    runMorph nr $ put (v, (h1, y))

        registerOnChange mr $ do
            runMorph st2 $ modify (`mappend` [(ti,ev)])

        pure $ RefReaderT
                { value_ = runMorph nr $ gets $ snd . snd
                , registerOnChange_ = registerOnChange mr
                }

    onChangeMemo (RefReaderTPure x) f = fmap pure $ join $ f x
    onChangeMemo mr f = Reg $ ReaderT $ \st@(_, st2, ticker) -> RefCreatorT $ do
        v <- lift $ value mr
        (my, h1) <- lift $ runWriterT $ runRefCreatorT $ flip runReaderT st $ unReg $ f v
        (y, h2) <- lift $ runWriterT $ runRefCreatorT $ flip runReaderT st $ unReg $ my
        ti <- lift $ runMorph ticker $ state $ \s -> (s, succ s)
        nr <- lift $ newRef' ((v, ((my, h1, h2), y)), [])

        let ev = do
              ((vold, dat@((_, h1_, h2_), _)), others) <- runMorph nr get
              v <- value mr
              let others' = la: others
                  la = (vold, dat)
              if v == vold
                  then pure ()
                  else do
                    runMonadMonoid $ h1_ Block
                    runMonadMonoid $ h2_ Kill
                    case lookup v others of
                      Just ((my, h1, _), _) -> do
                        runMonadMonoid $ h1 Unblock
                        (y, h2) <- runWriterT $ runRefCreatorT $ flip runReaderT st $ unReg $ my
                        runMorph nr $ put ((v, ((my, h1, h2), y)), filter ((/=v) . fst) $ others')
                      Nothing -> do
                        (my, h1) <- runWriterT $ runRefCreatorT $ flip runReaderT st $ unReg $ f v
                        (y, h2) <- runWriterT $ runRefCreatorT $ flip runReaderT st $ unReg $ my
                        runMorph nr $ put ((v, ((my, h1, h2), y)), others')

        registerOnChange mr $ do
            runMorph st2 $ modify (`mappend` [(ti,ev)])

        pure $ RefReaderT
                { value_ = runMorph nr $ gets $ snd . snd . fst
                , registerOnChange_ = registerOnChange mr
                }

    askPostpone = Reg $ ReaderT $ \(st, _, _) -> pure $ st . runRefWriterT

    onRegionStatusChange g = Reg $ ReaderT $ \_ -> do
        RefCreatorT $ tell $ MonadMonoid . g


runRegister :: NewRef m => (forall a . m (m a, a -> m ())) -> Register m a -> m (a, m ())
runRegister newChan m = do
    (read, write) <- newChan
    runRegister_ read write m


runRegister_ :: NewRef m => (m (m ())) -> (m () -> m ()) -> Register m a -> m (a, m ())
runRegister_ read write (Reg m) = do
    tick <- newRef' mempty
    ticker <- newRef' 0
    a <- fmap fst $ runWriterT $ runRefCreatorT $ runReaderT m (write, tick, ticker)
    pure $ (,) a $ forever $ do
        join read
        k <- runMorph tick $ state $ \s -> (s, mempty)
        sequence_ $ map snd $ nubBy ((==) `on` fst) $ sortBy (compare `on` fst) k
--        runMorph ticker $ modify succ

--------------------------

runTests :: IO ()
#ifdef __TESTS__
runTests = tests runTest

runTest :: (Eq a, Show a) => String -> Register (Prog TP) a -> Prog' (a, Prog' ()) -> IO ()
runTest name = runTest_ name TP $ \r w -> runRegister_ (fmap unTP r) (w . TP)

newtype TP = TP { unTP :: Prog TP () }
#else
runTests = fail "enable the tests flag like \'cabal configure --enable-tests -ftests; cabal build; cabal test\'"
#endif

