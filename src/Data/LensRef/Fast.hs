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
    , runPerformanceTests
    ) where

import Data.Maybe
import Control.Applicative hiding (empty)
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer
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
type Ids m = OrdRefSet m (Dyn, TIds m)

-- trigger id
type TId m = OrdRef m (UpdateFunState m)
type TIds m = OrdRefSet m (UpdateFunState m)

-- collecting identifiers of references on whose values the return value depends on
type TrackedT m = WriterT (Ids m)

-- Handlers are added on trigger registration.
-- The registered triggers may be killed, blocked and unblocked via the handler.
-- invariant property: in the St state the ... is changed only
type Handler m = RegionStatusChangeHandler (MonadMonoid m)

data RefReaderT m a
    = RefReaderT (TrackedT m m a)
    | RefReaderTPure a


type HandT m = TrackedT m m

newtype instance RefWriterOf (RefReaderT m) a
    = RefWriterT { runRefWriterT :: m a }
        deriving (Monad, Applicative, Functor, MonadFix)

type RefWriterT m = RefWriterOf (RefReaderT m)

-- collecting handlers
type RefCreatorT m = WriterT (Handler m) m


data UpdateFunState m = UpdateFunState
    { _alive :: Bool
    , _dependencies :: (Id m, Ids m)       -- (i, dependencies of i)
    , _updateFun :: RefWriterT m ()    -- what to run if at least one of the dependency changes
    , _reverseDeps :: TIds m
    }

--type MLens m a b = a -> m (b, b -> m a)

data Reference m a = Reference
    { readWrite :: RefReaderT m (a, a -> RefWriterT m ())
    , register
        :: Bool                 -- True: run the following function initially
        -> (a -> HandT m a)     -- trigger to be registered
        -> RefCreatorT m ()         -- emits a handler
    }

readRef_ r = fmap fst $ readWrite r

type Register m = ReaderT (RefWriterT m () -> m ()) (RefCreatorT m)

-------------------------

instance NewRef m => Functor (RefReaderT m) where
    fmap f (RefReaderTPure x) = RefReaderTPure $ f x
    fmap f (RefReaderT mr) = RefReaderT $ fmap f mr

instance NewRef m => Applicative (RefReaderT m) where
    pure a = RefReaderTPure a
    RefReaderTPure f <*> RefReaderTPure a = RefReaderTPure $ f a
    mf <*> ma = RefReaderT $ runRefReaderT mf <*> runRefReaderT ma

instance NewRef m => Monad (RefReaderT m) where
    return a = pure a
    RefReaderTPure r >>= f = f r
    RefReaderT mr >>= f = RefReaderT $ mr >>= runRefReaderT . f

runRefReaderT (RefReaderTPure a) = pure a
runRefReaderT (RefReaderT x) = x

------------------------------

newReference :: forall m a . NewRef m => a -> RefCreatorT m (Reference m a)
newReference a = do
    ir <- lift $ newOrdRef (Dyn a, mempty)

    let getVal :: m a
        getVal = runOrdRef ir $ use $ _1 . to unsafeGet
        setVal :: a -> m ()
        setVal = runOrdRef ir . (_1 .=) . Dyn

    pure Reference
        { readWrite = RefReaderT $ do

            tell $ insertOrdRef ir mempty
            a <- lift getVal

            return $ (,) a $ \a -> RefWriterT $ do

                setVal a

                let gr :: TId m -> m [TId m]
                    gr n = children =<< runOrdRef n (use dependencies)

                    children :: (Id m, Ids m) -> m [TId m]
                    children (b, db) = do
                        nas <- runOrdRef b $ use _2
                        fmap concat $ forM (ordRefToList nas) $ \na -> do
                            UpdateFunState alive (a, _) _ _ <- runOrdRef na get
                            pure $ if alive && not (ordRefMember a db)
                                then [na]
                                else []

                    store :: TId m -> SRef m (TIds m)
                    store n = Morph $ \f -> runOrdRef n $ zoom reverseDeps f

                m1 <- children (ir, mempty)

                l <- maybe (fail "cycle") pure =<< topSortComponentM store gr m1

                forM_ l $ \n -> join $ fmap runRefWriterT $ runOrdRef n $ use updateFun

        , register = \init upd -> do

            let gv = runWriterT $ lift getVal >>= upd


            (a, ih) <- lift gv
            when init $ lift $ setVal a

            ri <- lift $ newOrdRef $ UpdateFunState True (ir, ih) undefined mempty

            let addRev, delRev :: Id m -> m ()
                addRev x = runOrdRef x $ _2 %= insertOrdRef ri
                delRev x = runOrdRef x $ _2 %= deleteOrdRef ri

            let modReg = do
                    (a, ih) <- gv
                    setVal a


                    ih' <- runOrdRef ri $ use $ dependencies . _2
                    mapM_ delRev $ ordRefToList $ ih' `ordRefDifference` ih
                    mapM_ addRev $ ordRefToList $ ih `ordRefDifference` ih'

                    runOrdRef ri $ dependencies .= (ir, ih)

            lift $ runOrdRef ri $ updateFun .= RefWriterT modReg


            lift $ mapM_ addRev $ ordRefToList ih

            tell $ \msg -> MonadMonoid $ do

                    when (msg == Kill) $ do
                        ih' <- runOrdRef ri $ use $ dependencies . _2
                        mapM_ delRev $ ordRefToList ih'

                    runOrdRef ri $ alive .= (msg == Unblock)
        }


joinReg :: NewRef m => RefReaderT m (Reference m a) -> Bool -> (a -> HandT m a) -> RefCreatorT m ()
joinReg (RefReaderTPure r) init a = register r init a
joinReg (RefReaderT m) init a = do
    r <- newReference mempty
    register r True $ \kill -> do
        runHandler $ kill Kill
        ref <- m
        fmap fst $ getHandler $ register ref init a
    tell $ \msg -> MonadMonoid $ do
        h <- runRefWriterT $ liftRefReader $ readRef_ r
        runMonadMonoid $ h msg

instance NewRef m => RefClass (Reference m) where
    type RefReaderSimple (Reference m) = RefReaderT m

    unitRef = pure $ Reference
        { readWrite = pure ((), const $ pure ())
        , register  = const $ const $ pure ()
        }

    readRefSimple = join . fmap readRef_

    writeRefSimple mr a
        = liftRefReader (join $ fmap readWrite mr) >>= ($ a) . snd

    lensMap k mr = pure $ Reference
        { readWrite = join (fmap readWrite mr) <&> \(a, s) -> (a ^. k, \b -> s $ set k b a)
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

    onChange (RefReaderTPure a) f = fmap RefReaderTPure $ f a
    onChange m f = do
        r <- newReference (mempty, error "impossible #4")
        register r True $ \(h, _) -> do
            runHandler $ h Kill
            getHandler $ liftRefReader m >>= f
        return $ fmap snd $ readRef $ pure r

    onChangeEq (RefReaderTPure a) f = fmap RefReaderTPure $ f a
    onChangeEq (RefReaderT m) f = do
        r <- newReference (const False, (mempty, error "impossible #3"))
        register r True $ \it@(p, (h', _)) -> do
            a <- m
            if p a
              then return it
              else do
                runHandler $ h' Kill
                (h, b) <- getHandler $ f a
                return ((== a), (h, b))

        return $ fmap (snd . snd) $ readRef_ r

    onChangeMemo (RefReaderTPure a) f = fmap RefReaderTPure $ join $ f a
    onChangeMemo (RefReaderT mr) f = do
        r <- newReference ((const False, ((error "impossible #2", mempty, mempty) , error "impossible #1")), [])
        register r True upd
        return $ fmap (snd . snd . fst) $ readRef_ r
      where
        upd st@((p, ((m'',h1'',h2''), _)), memo) = do
            let it = (p, (m'', h1''))
            a <- mr
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

liftRefWriter' :: NewRef m => RefWriter (Register m) a -> Register m a
liftRefWriter' = lift . lift . runRefWriterT

-------------- lenses

dependencies :: Lens' (UpdateFunState m) (Id m, Ids m)
dependencies k (UpdateFunState a b c d) = k b <&> \b' -> UpdateFunState a b' c d

alive :: Lens' (UpdateFunState m) Bool
alive k (UpdateFunState a b c d) = k a <&> \a' -> UpdateFunState a' b c d

updateFun :: Lens' (UpdateFunState m) (RefWriterT m ())
updateFun k (UpdateFunState a b c d) = k c <&> \c' -> UpdateFunState a b c' d

reverseDeps :: Lens' (UpdateFunState m) (TIds m)
reverseDeps k (UpdateFunState a b c d) = k d <&> \d' -> UpdateFunState a b c d'

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

instance NewRef m => MonadEffect (RefWriterOf (RefReaderT m)) where
    type EffectM (RefWriterOf (RefReaderT m)) = m
    liftEffectM = RefWriterT

instance NewRef m => MonadEffect (RefCreatorT m) where
    type EffectM (RefCreatorT m) = m
    liftEffectM = lift

--------------------------

runRegister :: NewRef m => (forall a . m (m a, a -> m ())) -> Register m a -> m (a, m ())
runRegister newChan m = do
    (read, write) <- newChan
    runRegister_ read write m

runRegister_ :: NewRef m => (m (RefWriterT m ())) -> (RefWriterT m () -> m ()) -> Register m a -> m (a, m ())
runRegister_ read write m = do
    a <- fmap fst $ runWriterT $ flip runReaderT (write . liftRefWriter) m
    pure $ (,) a $ forever $ join $ fmap runRefWriterT read


runTests :: IO ()
#ifdef __TESTS__
runTests = tests liftRefWriter' runTest

runTest :: (Eq a, Show a) => String -> Register (Prog TP) a -> Prog' (a, Prog' ()) -> IO ()
runTest name = runTest_ name (TP . RefWriterT) $ \r w -> runRegister_ (fmap unTP r) (w . TP)

newtype TP = TP { unTP :: RefWriterT (Prog TP) () }

runPerformanceTests :: Int -> IO ()
runPerformanceTests = performanceTests liftRefWriter' assertEq runPTest

assertEq a b | a == b = return ()
assertEq a b = fail $ show a ++ " /= " ++ show b

runPTest :: String -> Register IO () -> IO ()
runPTest name m = do
    putStrLn name
    _ <- runRegister_ undefined (const $ return ()) m
    return ()
#else
runTests = fail "enable the tests flag like \'cabal configure --enable-tests -ftests; cabal build; cabal test\'"
#endif

