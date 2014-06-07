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

--import Debug.Trace
import Data.Maybe
import Data.Monoid
import Data.IORef
import qualified Data.IntMap as Map
import Control.Applicative hiding (empty)
--import Control.Monad.Reader
import Control.Monad.State
import Control.Lens.Simple

import Unsafe.Coerce
import System.IO.Unsafe

import Data.LensRef.Class
import Data.LensRef.Common
#ifdef __TESTS__
import Data.LensRef.TestEnv hiding (listen, Id)
import Data.LensRef.Test
#endif

----------------------

newtype Register m a = Register { unRegister :: SRef m (Sta m) -> m a }

instance Monad m => Monoid (Register m ()) where
--    {-# SPECIALIZE instance Monoid (Register IO ()) #-}
    {-# INLINE mempty #-}
    mempty = return ()
    {-# INLINE mappend #-}
    m `mappend` n = m >> n

{-# INLINE ask #-}
ask :: Monad m => Register m (SRef m (Sta m))
ask = Register return

instance Monad m => Monad (Register m) where
--    {-# SPECIALIZE instance Monad (Register IO) #-}
    {-# INLINE return #-}
    return = Register . const . return
    {-# INLINE (>>=) #-}
    Register m >>= f = Register $ \r -> m r >>= \a -> unRegister (f a) r

instance Applicative m => Applicative (Register m) where
--    {-# SPECIALIZE instance Applicative (Register IO) #-}
    {-# INLINE pure #-}
    pure = Register . const . pure
    {-# INLINE (<*>) #-}
    Register f <*> Register g = Register $ \r -> f r <*> g r

instance Functor m => Functor (Register m) where
--    {-# SPECIALIZE instance Functor (Register IO) #-}
    {-# INLINE fmap #-}
    fmap f (Register m) = Register $ fmap f . m

instance MonadFix m => MonadFix (Register m) where
--    {-# SPECIALIZE instance MonadFix (Register IO) #-}
    mfix f = Register $ \r -> mfix $ \a -> unRegister (f a) r

-- dynamic value + reverse deps
data Dyn m where Dyn :: a -> TIds m -> Dyn m

-- Each atomic reference has a unique identifier
type Id m = OrdRef m (Dyn m)   -- (value, reverse deps)
type Ids m = OrdRefSet m (Dyn m)

-- trigger id
type TId m = OrdRef m (UpdateFunState m)
type TIds m = OrdRefSet m (UpdateFunState m)

-- collecting identifiers of references on whose values the return value depends on
--type TrackedT m = WriterT (Ids m)

-- Handlers are added on trigger registration.
-- The registered triggers may be killed, blocked and unblocked via the handler.
-- invariant property: in the St state the ... is changed only
type Handler m = RegionStatusChangeHandler (MonadMonoid m)

data RefReaderT m a
    = RefReaderT (Bool -> Register m a)
    | RefReaderTPure a


newtype instance RefWriterOf (RefReaderT m) a
    = RefWriterT { runRefWriterT :: Register m a }
        deriving (Monad, Applicative, Functor, MonadFix)

data Sta m = Sta
    { _handler  :: Handler m
    , _deps     :: Ids m
    , _postpone :: (m () -> m ())
    }

data UpdateFunState m = UpdateFunState
    { _alive        :: Bool
    , _wid          :: (Id m)       -- i
    , _dependencies :: (Ids m)       --  dependencies of i
    , _updateFun    :: (m ())         -- what to run if at least one of the dependency changes
    , _reverseDeps  :: (TIds m)
    }

data Reference m a = Reference
    { readWrite :: !(RefReaderT m (a, a -> m ()))
    , register
        :: Bool                 -- True: run the following function initially
        -> (a -> m a)     -- trigger to be registered
        -> Register m ()         -- emits a handler
    }

{-# INLINE readRef_ #-}
readRef_ :: NewRef m => Reference m a -> RefReaderT m a
readRef_ r = readWrite r <&> fst

-------------------------

instance Functor m => Functor (RefReaderT m) where
--    {-# SPECIALIZE instance Functor (RefReaderT IO) #-}
    {-# INLINE fmap #-}
    fmap f (RefReaderTPure x) = RefReaderTPure $ f x
    fmap f (RefReaderT mr) = RefReaderT $ \b -> fmap f $ mr b

instance Applicative m => Applicative (RefReaderT m) where
--    {-# SPECIALIZE instance Applicative (RefReaderT IO) #-}
    {-# INLINE pure #-}
    pure = RefReaderTPure
    {-# INLINE (<*>) #-}
    RefReaderTPure f <*> RefReaderTPure a = RefReaderTPure $ f a
    mf <*> ma = RefReaderT $ \b -> runRefReaderT b mf <*> runRefReaderT b ma
      where
        runRefReaderT _ (RefReaderTPure a) = pure a
        runRefReaderT b (RefReaderT x) = x b

instance Monad m => Monad (RefReaderT m) where
--    {-# SPECIALIZE instance Monad (RefReaderT IO) #-}
    {-# INLINE return #-}
    return = return
    {-# INLINE (>>=) #-}
    RefReaderTPure r >>= f = f r
    RefReaderT mr >>= f = RefReaderT $ \b -> mr b >>= runRefReaderT_ b . f

{-# INLINE runRefReaderT_ #-}
runRefReaderT_ _ (RefReaderTPure a) = return a
runRefReaderT_ b (RefReaderT x) = x b


------------------------------

{-# INLINE newReference #-}
newReference = Register . const . newReference_

{-# SPECIALIZE newReference_ :: a -> IO (Reference IO a) #-}
newReference_ :: forall m a . NewRef m => a -> m (Reference m a)
newReference_ a = do
    ir@(OrdRef i oir) <- newOrdRef $ Dyn a mempty

    return Reference
        { readWrite = RefReaderT $ \b -> Register $ \st -> do

            Dyn a nas <- readRef' oir
            when b $ modRef' st $ deps %= Map.insert i oir

            return $ (,) (unsafeCoerce a) $ \a -> do

                writeRef' oir $ Dyn a nas

                when (not $ Map.null nas) $ do

                    let ch :: TId m -> m [TId m]
                        ch (OrdRef _ n) = do
                            UpdateFunState _ (OrdRef _ w) dep _ _ <- readRef' n
                            Dyn _ revDep <- readRef' w
                            fmap (map $ uncurry OrdRef) $ flip filterM (Map.toList revDep) $ \(_, na) -> do
                                UpdateFunState alive (OrdRef i _) _ _ _ <- readRef' na
                                pure $ alive && not (Map.member i dep)

                        topSort [] = pure ()
                        topSort (p@(OrdRef i op):ps) = do
                            readRef' op >>= _updateFun

                            let del (OrdRef _ n) = modRef' n $ do
                                    reverseDeps %= Map.delete i
                                    use $ reverseDeps . to Map.null
                            ys <- filterM del =<< ch p
                            topSort $ merge ps ys

                        collects v = mapM_ (collect v) =<< ch v
                        collect (OrdRef i op) v@(OrdRef _ ov) = do
                            notvisited <- modRef' ov $ do
                                reverseDeps %= Map.insert i op
                                use $ reverseDeps . to Map.null
                            when notvisited $ collects v

                    as <- fmap (map $ uncurry OrdRef) $ (`filterM` Map.toList nas) $ \(_, na) -> readRef' na <&> (^. alive)
                    mapM_ collects as
                    topSort as

        , register = \init upd -> Register $ \st -> do

            let gv = do
                    modRef' st $ deps %= mempty
                    a <- readRef' oir >>= upd . unsafeGet
                    h <- readRef' st
                    return (a, h ^. deps)

            (a, ih) <- gv

            when init $ modRef' oir $ modify $ \(Dyn _ s) -> Dyn a s

            OrdRef i ori <- newOrdRef $ error "impossible"

            let addRev, delRev :: SRef m (Dyn m) -> m ()
                addRev x = modRef' x $ revDep %= Map.insert i ori
                delRev x = modRef' x $ revDep %= Map.delete i

                modReg = do
                    (a, ih) <- gv

                    ih' <- readRef' ori <&> (^. dependencies)
                    mapM_ delRev $ Map.elems $ ih' `Map.difference` ih
                    mapM_ addRev $ Map.elems $ ih `Map.difference` ih'

                    modRef' oir $ modify $ \(Dyn _ s) -> Dyn a s
                    modRef' ori $ dependencies .= ih

            writeRef' ori $ UpdateFunState True ir ih modReg mempty

            mapM_ addRev $ Map.elems ih

            flip unRegister st $ tellHand $ \msg -> MonadMonoid $ do

                modRef' ori $ alive .= (msg == Unblock)

                when (msg == Kill) $ do
                    ih' <- readRef' ori
                    mapM_ delRev $ Map.elems $ ih' ^. dependencies

                -- TODO
                when (msg == Unblock) $ do
                    p <- readRef' st
                    UpdateFunState _ _ _ x _ <- readRef' ori
                    _postpone p x
        }

{-# SPECIALIZE joinReg :: RefReaderT IO (Reference IO a) -> Bool -> (a -> IO a) -> Register IO () #-}
joinReg :: NewRef m => RefReaderT m (Reference m a) -> Bool -> (a -> m a) -> Register m ()
joinReg (RefReaderTPure r) init a = register r init a
joinReg (RefReaderT m) init a = do
    st <- ask
    r <- newReference mempty
    register r True $ \kill -> flip unRegister st $ do
        runM kill Kill
        ref <- m True
        fmap fst $ getHandler $ register ref init a
    tellHand $ \msg -> MonadMonoid $ flip unRegister st $ do
        h <- runRefReaderT_ True $ readRef_ r
        runM h msg

instance NewRef m => RefClass (Reference m) where
    {-# SPECIALIZE instance RefClass (Reference IO) #-}
    type RefReaderSimple (Reference m) = RefReaderT m

    unitRef = pure $ Reference
        { readWrite = pure ((), const $ pure ())
        , register  = const $ const $ pure ()
        }

    {-# INLINE readRefSimple #-}
    readRefSimple (RefReaderTPure r) = readRef_ r
    readRefSimple (RefReaderT m) = RefReaderT $ \b -> m b >>= runRefReaderT_ b . readRef_

--    {-# INLINE writeRefSimple #-}
    writeRefSimple (RefReaderTPure r) a
        = RefWriterT $ runRefReaderT_ False (readWrite r) >>= Register . const . ($ a) . (^. _2)
    writeRefSimple (RefReaderT mr) a
        = RefWriterT $ mr False >>= runRefReaderT_ False . readWrite >>= Register . const . ($ a) . (^. _2)

    lensMap k mr = pure $ Reference
        { readWrite = (mr >>= readWrite) <&> \(a, s) -> (a ^. k, \b -> s $ set k b a)
        , register = \init f -> joinReg mr init $ \a -> fmap (\b -> set k b a) $ f (a ^. k)
        }

instance NewRef m => MonadRefCreator (Register m) where
    {-# SPECIALIZE instance MonadRefCreator (Register IO) #-}

    newRef = Register . const . fmap pure . newReference_

    extRef m k a0 = do
        st <- ask
        r <- newReference a0
        -- TODO: remove dropHandler?
        dropHandler $ do
            joinReg m False $ \_ -> flip unRegister st $ runRefReaderT_ True $ fmap (^. k) $ readRef_ r
            register r True $ \a -> flip unRegister st $ runRefReaderT_ True $ fmap (\b -> set k b a) $ readRefSimple m
        return $ pure r

    onChange (RefReaderTPure a) f = fmap RefReaderTPure $ f a
    onChange m f = do
        st <- ask
        r <- newReference (mempty, error "impossible #4")
        register r True $ \(h, _) -> flip unRegister st $ do
            runM h Kill
            getHandler $ liftRefReader m >>= f
        return $ fmap snd $ readRef $ pure r

    onChangeEq (RefReaderTPure a) f = fmap RefReaderTPure $ f a
    onChangeEq (RefReaderT m) f = do
        st <- ask
        r <- newReference (const False, (mempty, error "impossible #3"))
        register r True $ \it@(p, (h', _)) -> flip unRegister st $ do
            a <- m True
            if p a
              then return it
              else do
                runM h' Kill
                (h, b) <- getHandler $ f a
                return ((== a), (h, b))

        return $ fmap (snd . snd) $ readRef_ r

    onChangeMemo (RefReaderTPure a) f = fmap RefReaderTPure $ join $ f a
    onChangeMemo (RefReaderT mr) f = do
        st' <- ask
        r <- newReference ((const False, ((error "impossible #2", mempty, mempty) , error "impossible #1")), [])
        register r True $ \st@((p, ((m'',h1'',h2''), _)), memo) -> flip unRegister st' $ do
            let it = (p, (m'', h1''))
            a <- mr True
            if p a
              then return st
              else case listToMaybe [ b | (p, b) <- memo, p a] of
                Just (m',h1') -> do
                    runM h2'' Kill
                    runM h1'' Block
                    runM h1' Unblock
                    (h2, b') <- getHandler m'
                    return (((== a), ((m',h1',h2), b')), it: filter (not . ($ a) . fst) memo)
                Nothing -> do
                    runM h2'' Kill
                    (h1, m') <- getHandler $ f a
                    (h2, b') <- getHandler m'
                    return (((== a), ((m',h1,h2), b')), it: memo)
        return $ fmap (snd . snd . fst) $ readRef_ r

    onRegionStatusChange h
        = tellHand $ MonadMonoid . h


-------------------- aux

runM m k = Register . const $ runMonadMonoid $ m k

{-# INLINE tellHand #-}
tellHand :: (NewRef m) => Handler m -> Register m ()
tellHand h = Register $ \st -> modRef' st $ handler %= (`mappend` h)

{-# INLINE dropHandler #-}
dropHandler :: NewRef m => Register m a -> Register m a
dropHandler m = Register $ \st -> do
    x <- readRef' st
    a <- unRegister m st
    writeRef' st x
    return a

{-# INLINE getHandler #-}
getHandler :: NewRef m => Register m a -> Register m (Handler m, a)
getHandler m = Register $ \st -> do
    h' <- modRef' st $ replace handler mempty
    a <- unRegister m st
    h <- modRef' st $ replace handler h'
    return (h, a)

{-# INLINE replace #-}
replace :: Monad m => Lens' s a -> a -> StateT s m a
replace k x = do
    x' <- use k
    k .= x
    return x'

{-# INLINE unsafeGet #-}
unsafeGet :: Dyn m -> a
unsafeGet (Dyn a _) = unsafeCoerce a

-------------- lenses

{-# INLINE handler #-}
handler :: Lens' (Sta m) (Handler m)
handler k (Sta a b c) = k a <&> \a' -> Sta a' b c

{-# INLINE deps #-}
deps :: Lens' (Sta m) (Ids m)
deps k (Sta a b c) = k b <&> \b' -> Sta a b' c

{-# INLINE dependencies #-}
dependencies :: Lens' (UpdateFunState m) (Ids m)
dependencies k (UpdateFunState a b c d e) = k c <&> \c' -> UpdateFunState a b c' d e

{-# INLINE alive #-}
alive :: Lens' (UpdateFunState m) Bool
alive k (UpdateFunState a b c d e) = k a <&> \a' -> UpdateFunState a' b c d e

{-# INLINE reverseDeps #-}
reverseDeps :: Lens' (UpdateFunState m) (TIds m)
reverseDeps k (UpdateFunState a b c d e) = k e <&> \e' -> UpdateFunState a b c d e'

{-# INLINE revDep #-}
revDep :: Lens' (Dyn m) (TIds m)
revDep k (Dyn a b) = k b <&> \b' -> Dyn a b'

-------------------------------------------------------

instance NewRef m => MonadRefReader (Register m) where
    {-# SPECIALIZE instance MonadRefReader (Register IO) #-}
    type BaseRef (Register m) = Reference m
--    {-# INLINE liftRefReader #-}
    liftRefReader = runRefReaderT_ False

instance NewRef m => MonadRefReader (RefReaderT m) where
    {-# SPECIALIZE instance MonadRefReader (RefReaderT IO) #-}
    type BaseRef (RefReaderT m) = Reference m
--    {-# INLINE liftRefReader #-}
    liftRefReader = id

instance NewRef m => MonadRefReader (RefWriterOf (RefReaderT m)) where
    {-# SPECIALIZE instance MonadRefReader (RefWriterOf (RefReaderT IO)) #-}
    type BaseRef (RefWriterOf (RefReaderT m)) = Reference m
--    {-# INLINE liftRefReader #-}
    liftRefReader = RefWriterT . runRefReaderT_ False

instance NewRef m => MonadRefWriter (RefWriterOf (RefReaderT m)) where
    {-# SPECIALIZE instance MonadRefWriter (RefWriterOf (RefReaderT IO)) #-}
--    {-# INLINE liftRefWriter #-}
    liftRefWriter = id

instance NewRef m => MonadMemo (Register m) where
--    {-# SPECIALIZE instance MonadMemo (Register IO) #-}
    memoRead = memoRead_ $ \r -> runRefWriterT . writeRefSimple r

instance NewRef m => MonadEffect (RefWriterOf (RefReaderT m)) where
--    {-# SPECIALIZE instance MonadEffect (RefWriterOf (RefReaderT IO)) #-}
    type EffectM (RefWriterOf (RefReaderT m)) = m
--    {-# INLINE liftEffectM #-}
    liftEffectM = RefWriterT . Register . const

instance NewRef m => MonadEffect (Register m) where
--    {-# SPECIALIZE instance MonadEffect (Register IO) #-}
    type EffectM (Register m) = m
--    {-# INLINE liftEffectM #-}
    liftEffectM = Register . const

instance NewRef m => MonadRegister (Register m) where
--    {-# SPECIALIZE instance MonadRegister (Register IO) #-}
    askPostpone = do
        r <- ask
        p <- Register . const $ readRef' r
        return $ \f -> _postpone p . flip unRegister r . runRefWriterT $ f

--------------------------

runRegister :: NewRef m => (forall a . m (m a, a -> m ())) -> Register m a -> m (a, m ())
runRegister newChan m = do
    (read, write) <- newChan
    runRegister_ read write m

runRegister_ :: NewRef m => (m (m ())) -> (m () -> m ()) -> Register m a -> m (a, m ())
runRegister_ read write m = do
    r <- newRef' $ Sta mempty mempty write
    a <- flip unRegister r m
    pure $ (,) a $ forever $ join read

runTests :: IO ()
#ifdef __TESTS__
runTests = tests runRefWriterT runTest

runTest :: (Eq a, Show a) => String -> Register (Prog TP) a -> Prog' (a, Prog' ()) -> IO ()
runTest name = runTest_ name (TP) $ \r w -> runRegister_ (fmap unTP r) (w . TP)

newtype TP = TP { unTP :: Prog TP () }

runPerformanceTests :: Int -> IO ()
runPerformanceTests = performanceTests runRefWriterT assertEq runPTest

assertEq a b | a == b = return ()
assertEq a b = fail $ show a ++ " /= " ++ show b

runPTest :: String -> Register IO () -> IO ()
runPTest name m = do
    putStrLn name
    _ <- runRegister_ undefined (const $ return ()) m
    return ()
#else
runTests = fail "enable the tests flag like \'cabal configure --enable-tests -ftests; cabal build; cabal test\'"
runPerformanceTests _ = fail "enable the tests flag"
#endif


----------------------------------------------

data OrdRef m a = OrdRef !Int !(SRef m a)

instance Eq (OrdRef m a) where
--    {-# SPECIALIZE instance Eq (OrdRef IO a) #-}
    OrdRef i _ == OrdRef j _ = i == j

instance Ord (OrdRef m a) where
--    {-# SPECIALIZE instance Ord (OrdRef IO a) #-}
    OrdRef i _ `compare` OrdRef j _ = i `compare` j

{-# INLINE newOrdRef #-}
newOrdRef :: NewRef m => a -> m (OrdRef m a)
newOrdRef a = liftM2 OrdRef newId (newRef' a)

type OrdRefSet m a = Map.IntMap (SRef m a)

counter = unsafePerformIO $ newIORef (0 :: Int)

instance NewRef IO where
    type SRef IO = IORef

--    {-# INLINE newRef' #-}
    newRef' x = newIORef x
--    {-# INLINE readRef' #-}
    readRef' r = readIORef r
--    {-# INLINE writeRef' #-}
    writeRef' r a = writeIORef r a
--    {-# INLINE newId #-}
    newId = do
        c <- readIORef counter
        writeIORef counter $! succ c
        return c



