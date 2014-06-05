{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE CPP #-}
{- |
Fast implementation for the @MonadRefCreator@ interface.

TODO
- optimiziation: do not remember values
- optimiziation: equality check
-}
module Data.LensRef.Fast
    ( Register
    , runRegister
    , runTests
    ) where

-- import Data.Monoid
import Data.Maybe
import qualified Data.Set as Set
--import qualified Data.Map as Map
import Control.Applicative hiding (empty)
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer
--import Control.Monad.Identity
import Control.Lens.Simple


import Unsafe.Coerce

import Data.LensRef.Class
import Data.LensRef.Common
#ifdef __TESTS__
import Data.LensRef.TestEnv hiding (listen, Id)
import Data.LensRef.Test
#endif

----------------------

-- dynamic value
data Dyn where Dyn :: a -> Dyn

-- Each atomic reference has a unique identifier
type Id m = OrdRef m (Dyn, TIds m)   -- (value, reverse deps)

-- trigger id
type TId m = OrdRef m (UpdateFunState m)

-- set of identifiers
type Ids m = Set.Set (Id m)
type TIds m = Set.Set (TId m)

-- collecting identifiers of references on whose values the return runRefReaderT depends on
type TrackedT m = WriterT (Ids m)

-- Handlers are added on trigger registration.
-- The registered triggers may be killed, blocked and unblocked via the handler.
-- invariant property: in the St state the ... is changed only
type Handler m = RegionStatusChangeHandler (MonadMonoid m)

-- collecting handlers
type HandlerT n m = WriterT (Handler n) m

data RefReaderT m a
    = RefReaderT { runRefReaderT_ :: TrackedT m m a }
    | RefReaderTPure a


type HandT m = TrackedT m m

newtype instance RefWriterOf (RefReaderT m) a
    = RefWriterT { runRefWriterT :: m a }
        deriving (Monad, Applicative, Functor, MonadFix)

type RefWriterT m = RefWriterOf (RefReaderT m)


type RefCreatorT m = HandlerT m m













data UpdateFunState m = UpdateFunState
    { _alive :: Bool
    , _dependencies :: (Id m, Ids m)       -- (i, dependencies of i)
    , _updateFun :: RefWriterT m ()    -- what to run if at least one of the dependency changes
    }

data Reference m a = Reference
    { readRef_  :: RefReaderT m a        
    , writeRef_ :: a -> RefWriterT m ()
    , register
        :: Bool                 -- True: run the following function initially
        -> (a -> HandT m a)     -- trigger to be registered
        -> RefCreatorT m ()         -- emits a handler
    }

-- postpone function
type Inner m n = ReaderT (RefWriterT m () -> m ()) n

newtype Register m a = Register { unRegister :: Inner m (RefCreatorT m) a }
    deriving (Functor, Applicative, Monad, MonadFix)

-------------------------

instance NewRef m => Functor (RefReaderT m) where
    fmap f (RefReaderTPure x) = RefReaderTPure $ f x
    fmap f mr = RefReaderT
        { runRefReaderT_ = fmap f $ runRefReaderT mr
        }

instance NewRef m => Applicative (RefReaderT m) where
    pure a = RefReaderTPure a
    RefReaderTPure f <*> RefReaderTPure a = RefReaderTPure $ f a
    mf <*> ma = RefReaderT
        { runRefReaderT_ = runRefReaderT mf <*> runRefReaderT ma
        }

instance NewRef m => Monad (RefReaderT m) where
    return a = pure a
    RefReaderTPure r >>= f = f r
    mr >>= f = RefReaderT
        { runRefReaderT_ = runRefReaderT mr >>= runRefReaderT . f
        }

runRefReaderT (RefReaderTPure a) = pure a
runRefReaderT x = runRefReaderT_ x

------------------------------

newReference :: forall m a . NewRef m => a -> RefCreatorT m (Reference m a)
newReference a = do
    ir <- lift $ newOrdRef (Dyn a, mempty)






    let getVal :: m a
        getVal = runOrdRef ir $ gets $ unsafeGet . (^. _1)
        setVal :: a -> m ()
        setVal = runOrdRef ir . modify . set _1 . Dyn



    pure Reference
        { readRef_ = RefReaderT $ do
            tell $ Set.singleton ir
            lift getVal

        , writeRef_ = \a -> RefWriterT $ do


            -- TODO: elim this
            m1 <- newOrdRef $ UpdateFunState True (ir, mempty) $ RefWriterT $ setVal a

            let gr :: TId m -> m [TId m]
                gr n = children =<< runOrdRef n (gets _dependencies)

                children :: (Id m, Ids m) -> m [TId m]
                children (b, db) = do
                    nas <- runOrdRef b $ gets snd
                    fmap concat $ forM (Set.toList nas) $ \na -> do
                        UpdateFunState alive (a, _) _ <- runOrdRef na get
                        pure $ if alive && a `Set.notMember` db
                            then [na]
                            else []

            l <- maybe (fail "cycle") pure =<< topSortComponentM gr m1

            forM_ l $ \n -> join $ fmap runRefWriterT $ runOrdRef n $ gets $ _updateFun

        , register = \init upd -> do

            let gv = runWriterT $ lift getVal >>= upd


            (a, ih) <- lift gv
            when init $ lift $ setVal a

            ri <- lift $ newOrdRef $ UpdateFunState True (ir, ih) undefined

            let addRev, delRev :: Id m -> m ()
                addRev x = runOrdRef x $ modify $ over _2 $ Set.insert ri
                delRev x = runOrdRef x $ modify $ over _2 $ Set.delete ri

            let modReg = do
                    (a, ih) <- gv
                    setVal a


                    ih' <- runOrdRef ri $ gets $ (^. _2) . (^. dependencies)
                    mapM_ delRev $ Set.toList $ ih' `Set.difference` ih
                    mapM_ addRev $ Set.toList $ ih `Set.difference` ih'

                    runOrdRef ri $ modify $ set dependencies (ir, ih)

            lift $ runOrdRef ri $ modify $ set updateFun $ RefWriterT modReg


            lift $ mapM_ addRev $ Set.toList ih

            let f Kill    = id
                f Block   = set alive False
                f Unblock = set alive True

            tell $ \msg -> MonadMonoid $ do


                    when (msg == Kill) $ do
                        ih' <- runOrdRef ri $ gets $ (^. _2) . (^. dependencies)
                        mapM_ delRev $ Set.toList ih'

                    runOrdRef ri $ modify $ f msg
        }


joinReg :: NewRef m => RefReaderT m (Reference m a) -> Bool -> (a -> HandT m a) -> RefCreatorT m ()
joinReg m init a = do
    r <- newReference mempty
    register r True $ \kill -> do
        runHandler $ kill Kill
        ref <- liftRefReader' m
        fmap fst $ getHandler $ register ref init a
    tell $ \msg -> MonadMonoid $ do
        h <- runRefWriterT $ liftRefReader $ readRef_ r
        runMonadMonoid $ h msg

instance NewRef m => RefClass (Reference m) where
    type RefReaderSimple (Reference m) = RefReaderT m

    unitRef = pure $ Reference
        { readRef_  = pure ()
        , writeRef_ = const $ pure ()
        , register  = const $ const $ pure ()
        }

    readRefSimple = join . fmap readRef_

    writeRefSimple mr a = do
        r <- liftRefReader mr
        writeRef_ r a

    lensMap k mr = pure $ Reference
        { readRef_  = fmap (^. k) $ readRefSimple mr
        , writeRef_ = \b -> do
            r <- liftRefReader mr
            a <- liftRefReader $ readRef_ r
            writeRef_ r $ set k b a
        , register = \init f -> joinReg mr init $ \a -> fmap (\b -> set k b a) $ f (a ^. k)
        }

instance NewRef m => MonadRefCreator (RefCreatorT m) where

    newRef = fmap pure . newReference

    extRef m k a0 = do
        r <- newReference a0
        -- TODO: remove dropHandler?
        dropHandler $ joinReg m False $ \_ -> liftRefReader' $ fmap (^. k) $ readRef_ r
        dropHandler $ register r True $ \a -> liftRefReader' $ fmap (\b -> set k b a) $ readRefSimple m
        return $ pure r

    onChange m f = do
        r <- newReference (mempty, error "impossible #4")
        register r True $ \(h, _) -> do
            runHandler $ h Kill
            getHandler $ liftRefReader m >>= f
        return $ fmap snd $ readRef $ pure r

    onChangeEq m f = do
        r <- newReference (const False, (mempty, error "impossible #3"))
        register r True $ \it@(p, (h', _)) -> do
            a <- liftRefReader' m
            if p a
              then return it
              else do
                runHandler $ h' Kill
                (h, b) <- getHandler $ f a
                return ((== a), (h, b))

        return $ fmap (snd . snd) $ readRef_ r

    onChangeMemo mr f = do
        r <- newReference ((const False, ((error "impossible #2", mempty, mempty) , error "impossible #1")), [])
        register r True upd
        return $ fmap (snd . snd . fst) $ readRef_ r
      where
        upd st@((p, ((m'',h1'',h2''), _)), memo) = do
            let it = (p, (m'', h1''))
            a <- liftRefReader' mr
            if p a
              then return st
              else case listToMaybe [ b | (p, b) <- memo, p a] of
                Just (m',h1') -> do
                    runHandler $ h2'' Kill
                    runHandler $ h1'' Block
                    runHandler $ h1' Unblock
                    (h2, b') <- getHandler m'
                    return (((== a), ((m',h1',h2), b')), it: filter (not . ($ a) . fst) memo)
                Nothing -> do
                    runHandler $ h2'' Kill
                    (h1, m') <- getHandler $ f a
                    (h2, b') <- getHandler m'
                    return (((== a), ((m',h1,h2), b')), it: memo)

    onRegionStatusChange h
        = tell $ MonadMonoid . runRefWriterT . liftEffectM . h


-------------------- aux

liftRefReader' :: NewRef m => RefReaderT m a -> HandT m a
liftRefReader' = runRefReaderT

dropHandler :: NewRef m => RefCreatorT m a -> RefCreatorT m a
dropHandler = lift . fmap fst . runWriterT

getHandler :: NewRef m => RefCreatorT m a -> HandT m (Handler m, a)
getHandler = lift . fmap (\(a,h)->(h,a)) . runWriterT

unsafeGet :: Dyn -> a
unsafeGet (Dyn a) = unsafeCoerce a

runHandler :: NewRef m => MonadMonoid m () -> HandT m ()
runHandler = lift . runMonadMonoid

-------------- lenses

dependencies :: Lens' (UpdateFunState m) (Id m, Ids m)
dependencies k (UpdateFunState a b c) = k b <&> \b' -> UpdateFunState a b' c

alive :: Lens' (UpdateFunState m) Bool
alive k (UpdateFunState a b c) = k a <&> \a' -> UpdateFunState a' b c

updateFun :: Lens' (UpdateFunState m) (RefWriterT m ())
updateFun k (UpdateFunState a b c) = k c <&> \c' -> UpdateFunState a b c'

-------------------------------------------------------

instance NewRef m => MonadRefReader (RefCreatorT m) where
    type BaseRef (RefCreatorT m) = Reference m
    liftRefReader = lift . fmap fst . runWriterT . runRefReaderT

instance NewRef m => MonadRefReader (RefReaderT m) where
    type BaseRef (RefReaderT m) = Reference m
    liftRefReader = id

instance NewRef m => MonadRefReader (RefWriterOf (RefReaderT m)) where
    type BaseRef (RefWriterOf (RefReaderT m)) = Reference m
    liftRefReader = RefWriterT . fmap fst . runWriterT . runRefReaderT

instance NewRef m => MonadRefWriter (RefWriterOf (RefReaderT m)) where
    liftRefWriter = id

instance NewRef m => MonadMemo (RefCreatorT m) where
    memoRead = memoRead_ $ \r -> lift . runRefWriterT . writeRefSimple r

instance NewRef m => MonadRefWriter (RefCreatorT m) where
    liftRefWriter = lift . runRefWriterT

instance MonadTrans Register where
    lift = Register . lift . lift

instance NewRef m => MonadEffect (RefWriterOf (RefReaderT m)) where
    type EffectM (RefWriterOf (RefReaderT m)) = m
    liftEffectM = RefWriterT

instance NewRef m => MonadEffect (RefCreatorT m) where
    type EffectM (RefCreatorT m) = m
    liftEffectM = lift

instance NewRef m => MonadEffect (Register m) where
    type EffectM (Register m) = m
    liftEffectM = lift

instance NewRef m => MonadRefReader (Register m) where
    type BaseRef (Register m) = Reference m
    liftRefReader = Register . lift . liftRefReader

instance NewRef m => MonadRefCreator (Register m) where
    extRef r l       = Register . lift . extRef r l
    newRef           = Register . lift . newRef
    onChange r f     = Register $ ReaderT $ \st -> onChange r $ fmap (flip runReaderT st . unRegister) f
    onChangeEq r f   = Register $ ReaderT $ \st -> onChangeEq r $ fmap (flip runReaderT st . unRegister) f
    onChangeMemo r f = Register $ ReaderT $ \st -> onChangeMemo r $ fmap (fmap (flip runReaderT st . unRegister) . flip runReaderT st . unRegister) f
    onRegionStatusChange = Register . lift . onRegionStatusChange

instance NewRef m => MonadMemo (Register m) where
    memoRead = memoRead_ writeRef --fmap (Register . lift) . Register . lift . memoRead . unRegister

instance NewRef m => MonadRefWriter (Register m) where
    liftRefWriter = Register . lift . liftRefWriter

instance NewRef m => MonadRegister (Register m) where
    askPostpone = Register ask

--------------------------

runRegister :: NewRef m => (forall a . m (m a, a -> m ())) -> Register m a -> m (a, m ())
runRegister newChan m = do
    (read, write) <- newChan
    runRegister_ read write m

runRegister_ :: NewRef m => (m (RefWriterT m ())) -> (RefWriterT m () -> m ()) -> Register m a -> m (a, m ())
runRegister_ read write m = do
    a <- fmap fst $ runWriterT $ flip runReaderT (write . liftRefWriter) $ unRegister m
    pure $ (,) a $ forever $ join $ fmap runRefWriterT read


runTests :: IO ()
#ifdef __TESTS__
runTests = tests runTest

runTest :: (Eq a, Show a) => String -> Register (Prog TP) a -> Prog' (a, Prog' ()) -> IO ()
runTest name = runTest_ name (TP . RefWriterT) $ \r w -> runRegister_ (fmap unTP r) (w . TP)

newtype TP = TP { unTP :: RefWriterT (Prog TP) () }
#else
runTests = fail "enable the tests flag like \'cabal configure --enable-tests -ftests; cabal build; cabal test\'"
#endif

