{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE CPP #-}
{- |
Reference implementation for the "Data.LensRef.Class" interface.

The implementation uses @unsafeCoerce@ internally, but its effect cannot escape.
-}
module Data.LensRef.Pure
    ( Register
    , runRegister
    , runTests
    ) where

import Data.Maybe
import qualified Data.IntSet as IntSet
import qualified Data.IntMap as IntMap
--import qualified Data.Map as Map
import Control.Applicative
import Control.Monad
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer
import Control.Monad.Identity
import Control.Lens.Simple

import Unsafe.Coerce

import Data.LensRef.Class
import Data.LensRef.Common
#ifdef __TESTS__
import Data.LensRef.TestEnv hiding (Id)
import Data.LensRef.Test
#endif

---------------------------------

-- Each atomic reference has a unique identifier
type Id = Int

-- set of identifiers
type Ids = IntSet.IntSet

-- collecting identifiers of references on whose values the return value depends on
type TrackedT = WriterT Ids

-- Handlers are added on trigger registration.
-- The registered triggers may be killed, blocked and unblocked via the handler.
-- invariant property: in the St state the ... is changed only
type Handler m = RegionStatusChangeHandler (MonadMonoid (StateT (St m) m))

-- collecting handlers
type HandlerT n m = WriterT (Handler n) m

newtype ReadT (m :: * -> *) a = ReadT { runReadT :: ReaderT ValSt (TrackedT Identity) a }
        deriving (Monad, Applicative, Functor, MonadReader ValSt)

-- invariant property: the values in St state are not changed, the state may be extended
type HandT m = StateT (St m) (TrackedT m)

newtype instance RefWriterOf (ReadT m) a
    = RefWriterOfReadT { runRefWriterOfReadT :: StateT (St m) m a }
        deriving (Monad, Applicative, Functor, MonadState (St m))

type ModifyT m = RefWriterOf (ReadT m)

-- invariant property: the St state is only exteded, not changed
type CreateT m = HandlerT m (StateT (St m) m)

type St m = (ValSt, TriggerSt m)

-- values of references
type ValSt = IntMap.IntMap Dyn

-- dynamic value
data Dyn where Dyn :: a -> Dyn

-- triggers
type TriggerSt m = IntMap.IntMap (UpdateFunState m)

data UpdateFunState m = UpdateFunState
    { _alive :: Bool
    , _dependencies :: (Id, Ids)
    , _updateFun :: ModifyT m ()    -- what to run if at least one of the dependency changes
    }

data Reference m a = Reference
    { readRef_  :: ReadT m a        
    , writeRef_ :: a -> ModifyT m ()
    , register
        :: Bool                 -- True: run the following function initially
        -> (a -> HandT m a)     -- trigger to be registered
        -> CreateT m ()         -- emits a handler
    }

-- postpone function
type Inner m n = ReaderT (ModifyT m () -> m ()) n

newtype Register m a = Register { unRegister :: Inner m (CreateT m) a }
    deriving (Functor, Applicative, Monad, MonadFix)

-------------------------------------

newReference :: (Monad m, Applicative m) => a -> CreateT m (Reference m a)
newReference a = do
    i <- gets $ nextKey . fst

    let getVal = asks $ unsafeGet . fromMaybe (error "fatal: cant find ref value") . IntMap.lookup i

        setVal :: MonadState (St n) m => a -> m ()
        setVal a = modify $ over _1 $ IntMap.insert i $ Dyn a

    setVal a

    pure Reference
        { readRef_ = ReadT $ do
            lift . tell $ IntSet.singleton i
            getVal

        , writeRef_ = \a -> do
            st_ <- gets snd
            let st = IntMap.insert (-1) (UpdateFunState True (i, mempty) $ setVal a) st_
                dom = [n | (n, UpdateFunState True _ _) <- IntMap.toList st]
                get n = _dependencies $ st IntMap.! n
                rel na nb = b `IntSet.member` da && a `IntSet.notMember` db where
                    (a, da) = get na
                    (b, db) = get nb

            l <- maybe (fail "cycle") pure $ topSort' rel dom (-1)
            when (not $ allUnique $ map (fst . get) l) $ fail "cycle"
            sequence_ $ map (_updateFun . (st IntMap.!)) l

        , register = \init upd -> do
            let gv = getTrackingIds $ liftRefReader' (ReadT getVal) >>= upd
            (ih, a) <- liftRefWriter gv
            when init $ setVal a

            ri <- gets $ nextKey . snd

            let modReg = do
                    (ih, a) <- gv
                    setVal a
                    modify $ over _2 $ IntMap.adjust (set dependencies (i,ih)) ri

            modify $ over _2 $ IntMap.insert ri (UpdateFunState True (i,ih) modReg)

            let f Kill = Nothing
                f Block = Just $ set alive False
                f Unblock = Just $ set alive True

            tell $ \msg -> MonadMonoid $ modify $ over _2 $ IntMap.update ((f msg <*>) . pure) ri

        }

joinReg :: (Monad m, Applicative m) => ReadT m (Reference m a) -> Bool -> (a -> HandT m a) -> CreateT m ()
joinReg m init a = do
    r <- newReference mempty
    register r True $ \kill -> do
        runHandler $ kill Kill
        ref <- liftRefReader' m
        fmap fst $ getHandler $ register ref init a
    tell $ \msg -> MonadMonoid $ do
        h <- runRefWriterOfReadT $ liftRefReader $ readRef_ r
        runMonadMonoid $ h msg

instance (Monad m, Applicative m) => RefClass (Reference m) where
    type RefReaderSimple (Reference m) = ReadT m

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

{-
    traversalMap k mr = pure $ Reference
        { readRef_  = fmap (^. k) $ readRefSimple mr
        , writeRef_ = \b -> do
            r <- mr
            a <- readRef_ r
            writeRef_ r $ set k b a
        , register = \init f -> joinReg mr init $ \a -> fmap (\b -> set k b a) $ f (a ^. k)
        }
-}

instance (Monad m, Applicative m) => MonadRefCreator (CreateT m) where

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
        = tell $ MonadMonoid . runRefWriterOfReadT . liftEffectM . h


----------------------------------- aux

getTrackingIds :: (Monad m, Applicative m) => HandT m a -> ModifyT m (Ids, a)
getTrackingIds = RefWriterOfReadT . mapStateT (fmap (\((a,st),ids) -> ((ids,a),st)) . runWriterT)

liftRefReader' :: (Monad m, Applicative m) => ReadT m a -> HandT m a
liftRefReader' = readerToState fst . mapReaderT (mapWriterT $ return . runIdentity) . runReadT

dropHandler :: (Monad m, Applicative m) => CreateT m a -> CreateT m a
dropHandler = lift . fmap fst . runWriterT

getHandler :: (Monad m, Applicative m) => CreateT m a -> HandT m (Handler m, a)
getHandler = mapStateT (lift . fmap (\((a,h),st)->((h,a),st))) . runWriterT

unsafeGet :: Dyn -> a
unsafeGet (Dyn a) = unsafeCoerce a

runHandler :: (Monad m, Applicative m) => MonadMonoid (StateT (St m) m) () -> HandT m ()
runHandler = mapStateT lift . runMonadMonoid

----------------------------------------- lenses

dependencies :: Lens' (UpdateFunState m) (Id, Ids)
dependencies k (UpdateFunState a b c) = k b <&> \b' -> UpdateFunState a b' c

alive :: Lens' (UpdateFunState m) Bool
alive k (UpdateFunState a b c) = k a <&> \a' -> UpdateFunState a' b c

-------------------------------------------------------

instance (Monad m, Applicative m) => MonadRefReader (CreateT m) where
    type BaseRef (CreateT m) = Reference m
    liftRefReader = lift . readerToState fst . mapReaderT (return . fst . runWriter) . runReadT

instance (Monad m, Applicative m) => MonadRefReader (ReadT m) where
    type BaseRef (ReadT m) = Reference m
    liftRefReader = id

instance (Monad m, Applicative m) => MonadRefReader (RefWriterOf (ReadT m)) where
    type BaseRef (RefWriterOf (ReadT m)) = Reference m
    liftRefReader = RefWriterOfReadT . readerToState fst . mapReaderT (return . fst . runWriter) . runReadT

instance (Monad m, Applicative m) => MonadRefWriter (RefWriterOf (ReadT m)) where
    liftRefWriter = id

instance (Monad m, Applicative m) => MonadMemo (CreateT m) where
    memoRead = memoRead_ $ \r -> lift . runRefWriterOfReadT . writeRefSimple r

instance (Monad m, Applicative m) => MonadRefWriter (CreateT m) where
    liftRefWriter = lift . runRefWriterOfReadT

instance MonadTrans Register where
    lift = Register . lift . lift . lift

instance (Monad m, Applicative m) => MonadEffect (RefWriterOf (ReadT m)) where
    type EffectM (RefWriterOf (ReadT m)) = m
    liftEffectM = RefWriterOfReadT . lift

instance (Monad m, Applicative m) => MonadEffect (CreateT m) where
    type EffectM (CreateT m) = m
    liftEffectM = lift . lift

instance (Monad m, Applicative m) => MonadEffect (Register m) where
    type EffectM (Register m) = m
    liftEffectM = Register . lift . lift . lift

instance (Monad m, Applicative m) => MonadRefReader (Register m) where
    type BaseRef (Register m) = Reference m
    liftRefReader = Register . lift . liftRefReader

instance (Monad m, Applicative m) => MonadRefCreator (Register m) where
    extRef r l       = Register . lift . extRef r l
    newRef           = Register . lift . newRef
    onChange r f     = Register $ ReaderT $ \st -> onChange r $ fmap (flip runReaderT st . unRegister) f
    onChangeEq r f   = Register $ ReaderT $ \st -> onChangeEq r $ fmap (flip runReaderT st . unRegister) f
    onChangeMemo r f = Register $ ReaderT $ \st -> onChangeMemo r $ fmap (fmap (flip runReaderT st . unRegister) . flip runReaderT st . unRegister) f
    onRegionStatusChange = Register . lift . onRegionStatusChange

instance (Monad m, Applicative m) => MonadMemo (Register m) where
    memoRead = memoRead_ writeRef --fmap (Register . lift) . Register . lift . memoRead . unRegister

instance (Monad m, Applicative m) => MonadRefWriter (Register m) where
    liftRefWriter = Register . lift . liftRefWriter

instance (Monad m, Applicative m) => MonadRegister (Register m) where
    askPostpone = Register ask

--------------------------

runRegister :: (Monad m, Applicative m) => (forall a . m (m a, a -> m ())) -> Register m a -> m (a, m ())
runRegister newChan m = do
    (read, write) <- newChan
    runRegister_ read write m

runRegister_ :: (Monad m, Applicative m) => m (Register m ()) -> (Register m () -> m ()) -> Register m a -> m (a, m ())
runRegister_ read write m = do
    (a, s) <- run mempty m
    pure $ (,) a $ fmap (const ()) $ run s $ forever $ join $ lift read
  where
    run s = flip runStateT s . fmap fst . runWriterT . flip runReaderT (write . Register . lift . liftRefWriter) . unRegister


runTests :: IO ()
#ifdef __TESTS__
runTests = tests runTest

runTest :: (Eq a, Show a) => String -> Register (Prog TP) a -> Prog' (a, Prog' ()) -> IO ()
runTest name = runTest_ name (TP . lift) $ \r w -> runRegister_ (fmap unTP r) (w . TP)

newtype TP = TP { unTP :: Register (Prog TP) () }
#else
runTests = fail "enable the tests flag like \'cabal configure --enable-tests -ftests; cabal build; cabal test\'"
#endif

