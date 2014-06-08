{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
--{-# LANGUAGE UndecidableInstances #-}
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
import Control.Applicative
import Control.Monad.State
import Control.Lens.Simple

import Unsafe.Coerce

import Data.LensRef.Class
import Data.LensRef.Common
#ifdef __TESTS__
import Data.LensRef.TestEnv hiding (listen, Id)
import Data.LensRef.Test
#endif

----------------------------------- data types

-- | reference temporal state
data RefState m where
    RefState 
        :: a        -- ^ reference value
        -> TIds m   -- ^ reverse dependencycoll (temporarily needed during topological sorting)
        -> RefState m

-- | trigger temporal state
data TriggerState m = TriggerState
    { _alive        :: Bool
    , _targetid     :: (Id m)     -- ^ target reference id
    , _dependencies :: (Ids m)    -- ^ source reference ids
    , _updateFun    :: (m ())     -- ^ what to run if at least one of the source ids changes
    , _reverseDeps  :: (TIds m)   -- ^ reverse dependencies
    }

-- | reference handler
data RefHandler m a = RefHandler
    { readWrite           -- ^ reader and writer actions
        :: !(RefReaderT m (a, a -> m ()))
    , registerTrigger     -- ^ how to registerTrigger a trigger
        :: Bool           -- ^ True: run the trigger initially also
        -> (a -> m a)     -- ^ trigger to be registered
        -> Register m ()
    }

-- | global variables
data GlobalVars m = GlobalVars
    { _handlercollection  :: Handler m   -- ^ collected handlers
    , _dependencycoll     :: Ids m       -- ^ collected dependencies
    , _postpone :: (m () -> m ())        -- ^ postpone action (never changes)
    , _counter :: !Int                   -- ^ increasing counter
    }

-- | reference identifier
type Id  m = OrdRef m (RefState m)
-- | reference identifiers
type Ids m = OrdRefSet m (RefState m)

-- | trigger identifier
type TId  m = OrdRef m (TriggerState m)
-- | trigger identifiers
type TIds m = OrdRefSet m (TriggerState m)

-- | IORef with Ord instance
data OrdRef    m a = OrdRef !Int !(SRef m a)
-- | IORefs with Ord instance
type OrdRefSet m a = Map.IntMap (SRef m a)


------------- data types for computations

-- reference reader monad
data RefReaderT m a
    = RefReaderT (Bool -> Register m a)
    | RefReaderTPure a

-- reference creator monad
newtype Register m a
    = Register { unRegister :: SRef m (GlobalVars m) -> m a }

-- reference writer monad
newtype instance RefWriterOf (RefReaderT m) a
    = RefWriterT { runRefWriterT :: Register m a }
        deriving (Monad, Applicative, Functor, MonadFix)

-- trigger handlers
-- The registered triggers may be killed, blocked and unblocked via the handlercollection.
type Handler m = RegionStatusChangeHandler (MonadMonoid m)

------------------------------

{-# SPECIALIZE newReference :: a -> Register IO (RefHandler IO a) #-}
newReference :: forall m a . NewRef m => a -> Register m (RefHandler m a)
newReference a = Register $ \st -> do
    ir@(OrdRef i oir) <- newOrdRef st $ RefState a mempty

    return RefHandler
        { readWrite = RefReaderT $ \b -> Register $ \st -> do

            RefState a nas <- readRef' oir
            when b $ modRef' st $ dependencycoll %= Map.insert i oir

            return $ (,) (unsafeCoerce a) $ \a -> do

                writeRef' oir $ RefState a nas

                when (not $ Map.null nas) $ do

                    let ch :: TId m -> m [TId m]
                        ch (OrdRef _ n) = do
                            TriggerState _ (OrdRef _ w) dep _ _ <- readRef' n
                            RefState _ revDep <- readRef' w
                            fmap (map $ uncurry OrdRef) $ flip filterM (Map.toList revDep) $ \(_, na) -> do
                                TriggerState alive (OrdRef i _) _ _ _ <- readRef' na
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

        , registerTrigger = \init upd -> Register $ \st -> do

            let gv = do
                    modRef' st $ dependencycoll %= mempty
                    a <- readRef' oir >>= upd . unsafeGet
                    h <- readRef' st
                    return (a, h ^. dependencycoll)

            (a, ih) <- gv

            when init $ modRef' oir $ modify $ \(RefState _ s) -> RefState a s

            OrdRef i ori <- newOrdRef st $ error "impossible"

            let addRev, delRev :: SRef m (RefState m) -> m ()
                addRev x = modRef' x $ revDep %= Map.insert i ori
                delRev x = modRef' x $ revDep %= Map.delete i

                modReg = do
                    (a, ih) <- gv

                    ih' <- readRef' ori <&> (^. dependencies)
                    mapM_ delRev $ Map.elems $ ih' `Map.difference` ih
                    mapM_ addRev $ Map.elems $ ih `Map.difference` ih'

                    modRef' oir $ modify $ \(RefState _ s) -> RefState a s
                    modRef' ori $ dependencies .= ih

            writeRef' ori $ TriggerState True ir ih modReg mempty

            mapM_ addRev $ Map.elems ih

            flip unRegister st $ tellHand $ \msg -> MonadMonoid $ do

                modRef' ori $ alive .= (msg == Unblock)

                when (msg == Kill) $ do
                    ih' <- readRef' ori
                    mapM_ delRev $ Map.elems $ ih' ^. dependencies

                -- TODO
                when (msg == Unblock) $ do
                    p <- readRef' st
                    TriggerState _ _ _ x _ <- readRef' ori
                    _postpone p x
        }

{-# SPECIALIZE joinReg :: RefReaderT IO (RefHandler IO a) -> Bool -> (a -> IO a) -> Register IO () #-}
joinReg :: NewRef m => RefReaderT m (RefHandler m a) -> Bool -> (a -> m a) -> Register m ()
joinReg (RefReaderTPure r) init a = registerTrigger r init a
joinReg (RefReaderT m) init a = do
    st <- ask
    r <- newReference mempty
    registerTrigger r True $ \kill -> flip unRegister st $ do
        runM kill Kill
        ref <- m True
        fmap fst $ getHandler $ registerTrigger ref init a
    tellHand $ \msg -> MonadMonoid $ flip unRegister st $ do
        h <- runRefReaderT_ True $ readRef_ r
        runM h msg

instance NewRef m => RefClass (RefHandler m) where
    {-# SPECIALIZE instance RefClass (RefHandler IO) #-}
    type RefReaderSimple (RefHandler m) = RefReaderT m

    unitRef = pure $ RefHandler
        { readWrite = pure ((), const $ pure ())
        , registerTrigger  = const $ const $ pure ()
        }

    {-# INLINE readRefSimple #-}
    readRefSimple (RefReaderTPure r) = readRef_ r
    readRefSimple (RefReaderT m) = RefReaderT $ \b -> m b >>= runRefReaderT_ b . readRef_

--    {-# INLINE writeRefSimple #-}
    writeRefSimple (RefReaderTPure r) a
        = RefWriterT $ runRefReaderT_ False (readWrite r) >>= Register . const . ($ a) . (^. _2)
    writeRefSimple (RefReaderT mr) a
        = RefWriterT $ mr False >>= runRefReaderT_ False . readWrite >>= Register . const . ($ a) . (^. _2)

    lensMap k mr = pure $ RefHandler
        { readWrite = (mr >>= readWrite) <&> \(a, s) -> (a ^. k, \b -> s $ set k b a)
        , registerTrigger = \init f -> joinReg mr init $ \a -> fmap (\b -> set k b a) $ f (a ^. k)
        }

instance NewRef m => MonadRefCreator (Register m) where
    {-# SPECIALIZE instance MonadRefCreator (Register IO) #-}

    newRef = fmap pure . newReference

    extRef m k a0 = do
        st <- ask
        r <- newReference a0
        -- TODO: remove dropHandler?
        dropHandler $ do
            joinReg m False $ \_ -> flip unRegister st $ runRefReaderT_ True $ fmap (^. k) $ readRef_ r
            registerTrigger r True $ \a -> flip unRegister st $ runRefReaderT_ True $ fmap (\b -> set k b a) $ readRefSimple m
        return $ pure r

    onChange (RefReaderTPure a) f = fmap RefReaderTPure $ f a
    onChange m f = do
        st <- ask
        r <- newReference (mempty, error "impossible #4")
        registerTrigger r True $ \(h, _) -> flip unRegister st $ do
            runM h Kill
            getHandler $ liftRefReader m >>= f
        return $ fmap snd $ readRef $ pure r

    onChangeEq (RefReaderTPure a) f = fmap RefReaderTPure $ f a
    onChangeEq (RefReaderT m) f = do
        st <- ask
        r <- newReference (const False, (mempty, error "impossible #3"))
        registerTrigger r True $ \it@(p, (h', _)) -> flip unRegister st $ do
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
        registerTrigger r True $ \st@((p, ((m'',h1'',h2''), _)), memo) -> flip unRegister st' $ do
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

{-# INLINE readRef_ #-}
readRef_ :: NewRef m => RefHandler m a -> RefReaderT m a
readRef_ r = readWrite r <&> fst

{-# INLINE ask #-}
ask :: Monad m => Register m (SRef m (GlobalVars m))
ask = Register return

{-# INLINE runRefReaderT_ #-}
runRefReaderT_ _ (RefReaderTPure a) = return a
runRefReaderT_ b (RefReaderT x) = x b

runM m k = Register . const $ runMonadMonoid $ m k

{-# INLINE tellHand #-}
tellHand :: (NewRef m) => Handler m -> Register m ()
tellHand h = Register $ \st -> modRef' st $ handlercollection %= (`mappend` h)

{-# INLINE dropHandler #-}
dropHandler :: NewRef m => Register m a -> Register m a
dropHandler m = Register $ \st -> do
    x <- readRef' st
    a <- unRegister m st
    modRef' st $ handlercollection .= (x ^. handlercollection)
    return a

{-# INLINE getHandler #-}
getHandler :: NewRef m => Register m a -> Register m (Handler m, a)
getHandler m = Register $ \st -> do
    h' <- modRef' st $ replace handlercollection mempty
    a <- unRegister m st
    h <- modRef' st $ replace handlercollection h'
    return (h, a)

{-# INLINE replace #-}
replace :: Monad m => Lens' s a -> a -> StateT s m a
replace k x = do
    x' <- use k
    k .= x
    return x'

{-# INLINE unsafeGet #-}
unsafeGet :: RefState m -> a
unsafeGet (RefState a _) = unsafeCoerce a

{-# INLINE newOrdRef #-}
newOrdRef :: NewRef m => SRef m (GlobalVars m) -> a -> m (OrdRef m a)
newOrdRef st a = do
    GlobalVars x y z c <- readRef' st
    writeRef' st $ GlobalVars x y z $ succ c
    r <- newRef' a
    return $ OrdRef c r

-------------- lenses

{-# INLINE handlercollection #-}
handlercollection :: Lens' (GlobalVars m) (Handler m)
handlercollection k (GlobalVars a b c d) = k a <&> \a' -> GlobalVars a' b c d

{-# INLINE dependencycoll #-}
dependencycoll :: Lens' (GlobalVars m) (Ids m)
dependencycoll k (GlobalVars a b c d) = k b <&> \b' -> GlobalVars a b' c d

{-# INLINE dependencies #-}
dependencies :: Lens' (TriggerState m) (Ids m)
dependencies k (TriggerState a b c d e) = k c <&> \c' -> TriggerState a b c' d e

{-# INLINE alive #-}
alive :: Lens' (TriggerState m) Bool
alive k (TriggerState a b c d e) = k a <&> \a' -> TriggerState a' b c d e

{-# INLINE reverseDeps #-}
reverseDeps :: Lens' (TriggerState m) (TIds m)
reverseDeps k (TriggerState a b c d e) = k e <&> \e' -> TriggerState a b c d e'

{-# INLINE revDep #-}
revDep :: Lens' (RefState m) (TIds m)
revDep k (RefState a b) = k b <&> \b' -> RefState a b'

------------------------------------------------------- type class instances

instance Monad m => Monoid (Register m ()) where
--    {-# SPECIALIZE instance Monoid (Register IO ()) #-}
    {-# INLINE mempty #-}
    mempty = return ()
    {-# INLINE mappend #-}
    m `mappend` n = m >> n

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

instance NewRef m => MonadRefReader (Register m) where
    {-# SPECIALIZE instance MonadRefReader (Register IO) #-}
    type BaseRef (Register m) = RefHandler m
--    {-# INLINE liftRefReader #-}
    liftRefReader = runRefReaderT_ False

instance NewRef m => MonadRefReader (RefReaderT m) where
    {-# SPECIALIZE instance MonadRefReader (RefReaderT IO) #-}
    type BaseRef (RefReaderT m) = RefHandler m
--    {-# INLINE liftRefReader #-}
    liftRefReader = id

instance NewRef m => MonadRefReader (RefWriterOf (RefReaderT m)) where
    {-# SPECIALIZE instance MonadRefReader (RefWriterOf (RefReaderT IO)) #-}
    type BaseRef (RefWriterOf (RefReaderT m)) = RefHandler m
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
    askPostpone = Register $ \st -> do
        p <- readRef' st
        return $ _postpone p . flip unRegister st . runRefWriterT

    runRegister' write m = do
        s <- newRef' $ GlobalVars mempty mempty write 0
        unRegister m s

instance Eq (OrdRef m a) where
--    {-# SPECIALIZE instance Eq (OrdRef IO a) #-}
    OrdRef i _ == OrdRef j _ = i == j

instance Ord (OrdRef m a) where
--    {-# SPECIALIZE instance Ord (OrdRef IO a) #-}
    OrdRef i _ `compare` OrdRef j _ = i `compare` j

liftRefWriter' = runRefWriterT

-------------------------- running


runRegister :: NewRef m => (forall a . m (m a, a -> m ())) -> Register m a -> m (a, m ())
runRegister newChan m = do
    (read, write) <- newChan
    runRegister_ read write m

runRegister_ :: NewRef m => (m (m ())) -> (m () -> m ()) -> Register m a -> m (a, m ())
runRegister_ read write m = do
    a <- runRegister' write m
    pure $ (,) a $ forever $ join read


runTests :: IO ()
#ifdef __TESTS__
runTests = tests liftRefWriter' runTest

runTest :: (Eq a, Show a) => String -> Register (Prog) a -> Prog' (a, Prog' ()) -> IO ()
runTest name = runTest_ name id $ \r w -> runRegister_ (fmap id r) (w)

runPerformanceTests :: Int -> IO ()
runPerformanceTests = performanceTests liftRefWriter' assertEq runPTest

assertEq a b | a == b = return ()
assertEq a b = fail $ show a ++ " /= " ++ show b

runPTest :: String -> Register IO () -> IO ()
runPTest name m = do
--    putStrLn name
    _ <- runRegister_ undefined (const $ return ()) m
    return ()
#else
runTests = fail "enable the tests flag like \'cabal configure --enable-tests -ftests; cabal build; cabal test\'"
runPerformanceTests _ = fail "enable the tests flag"
#endif

