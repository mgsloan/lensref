{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{- |
Fast implementation for the @MonadRefCreator@ interface.

TODO
- optimiziation: do not remember values
- optimiziation: equality check
-}
module Data.LensRef.Fast
    ( RefCreator
    , runRefCreator
    , liftRefWriter'
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

----------------------------------- data types

-- | reference temporal state
data RefState m where
    RefState 
        :: a        -- ^ reference value
        -> TIds m   -- ^ reverse dependency (temporarily needed during topological sorting)
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
        :: !(Bool -> m (a, a -> m ()))
    , registerTrigger     -- ^ how to registerTrigger a trigger
        :: Bool           -- ^ True: run the trigger initially also
        -> (a -> m a)     -- ^ trigger to be registered
        -> m ()
    }

-- | global variables
--{-# SPECIALIZE GlobalVars IO #-}
data GlobalVars m = GlobalVars
    { _handlercollection  :: !(SRef m (Handler m))  -- ^ collected handlers
    , _dependencycoll     :: !(SRef m (Ids m))      -- ^ collected dependencies
    , _postpone           :: !(SRef m (m ()))       -- ^ postponed actions
    , _counter            :: !(SRef m Int)          -- ^ increasing counter
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
    = RefReaderT (Bool -> RefCreator m a)
    | RefReaderTPure a

-- reference creator monad
newtype RefCreator m a
    = RefCreator { unRegister :: GlobalVars m -> m a }

-- reference writer monad
newtype instance RefWriterOf (RefReaderT m) a
    = RefWriterT { runRefWriterT :: RefCreator m a }
        deriving (Monad, Applicative, Functor, MonadFix)

-- trigger handlers
-- The registered triggers may be killed, blocked and unblocked via the handler.
type Handler m = RegionStatusChangeHandler m

------------------------------

{-# SPECIALIZE newReference :: GlobalVars IO -> a -> IO (RefHandler IO a) #-}
newReference :: forall m a . NewRef m => GlobalVars m -> a -> m (RefHandler m a)
newReference st a = do
    ir@(OrdRef i oir) <- newOrdRef st $ RefState a mempty

    return RefHandler
        { readWrite = \b -> do

            RefState a nas <- readRef' oir
            when b $ modRef' (_dependencycoll st) $ modify $ Map.insert i oir

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

                    p <- readRef' (_postpone st)
                    writeRef' (_postpone st) $ return ()
                    p

        , registerTrigger = \init upd -> do

            let gv = do
                    writeRef' (_dependencycoll st) mempty
                    a <- readRef' oir >>= upd . unsafeGet
                    h <- readRef' $ _dependencycoll st
                    return (a, h)

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

            flip unRegister st $ tellHand $ \msg -> do

                modRef' ori $ alive .= (msg == Unblock)

                when (msg == Kill) $ do
                    ih' <- readRef' ori
                    mapM_ delRev $ Map.elems $ ih' ^. dependencies

                -- TODO
                when (msg == Unblock) $ do
                    TriggerState _ _ _ x _ <- readRef' ori
                    modRef' (_postpone st) $ modify (>> x)
        }

{-# SPECIALIZE joinReg :: GlobalVars IO -> RefReaderT IO (RefHandler IO a) -> Bool -> (a -> IO a) -> IO () #-}
joinReg :: NewRef m => GlobalVars m -> RefReaderT m (RefHandler m a) -> Bool -> (a -> m a) -> m ()
joinReg _ (RefReaderTPure r) init a = registerTrigger r init a
joinReg st (RefReaderT m) init a = do
    r <- newReference st $ const $ pure ()
    registerTrigger r True $ \kill -> flip unRegister st $ do
        runM kill Kill
        ref <- m True
        fmap fst $ getHandler $ RefCreator $ \_ -> registerTrigger ref init a
    flip unRegister st $ tellHand $ \msg -> do
        h <- flip unRegister st $ runRefReaderT_ True $ readRef_ r
        flip unRegister st $ runM h msg

instance NewRef m => RefClass (RefHandler m) where
    {-# SPECIALIZE instance RefClass (RefHandler IO) #-}
    type RefReaderSimple (RefHandler m) = RefReaderT m

    unitRef = pure $ RefHandler
        { readWrite = \_ -> pure ((), const $ pure ())
        , registerTrigger  = const $ const $ pure ()
        }

    {-# INLINE readRefSimple #-}
    readRefSimple (RefReaderTPure r) = RefReaderT $ \b -> RefCreator $ \st -> readWrite r b <&> fst
    readRefSimple (RefReaderT m) = RefReaderT $ \b -> m b >>= runRefReaderT_ b . readRef_

--    {-# INLINE writeRefSimple #-}
    writeRefSimple (RefReaderTPure r) a
        = RefWriterT $ RefCreator $ \st -> readWrite r False >>= ($ a) . (^. _2)
    writeRefSimple (RefReaderT mr) a
        = RefWriterT $ mr False >>= \r -> RefCreator $ \st -> readWrite r False >>= ($ a) . (^. _2)

--    lensMap k (RefReaderTPure r) = 
    lensMap k mr = RefReaderT $ \b -> RefCreator $ \st -> pure $ RefHandler
        { readWrite = \b -> ((flip unRegister st $ runRefReaderT_ b mr) >>= \r -> readWrite r b) <&> \(a, s) -> (a ^. k, \b -> s $ set k b a)
        , registerTrigger = \init f -> joinReg st mr init $ \a -> fmap (\b -> set k b a) $ f (a ^. k)
        }

instance NewRef m => MonadRefCreator (RefCreator m) where
    {-# SPECIALIZE instance MonadRefCreator (RefCreator IO) #-}

    newRef a = RefCreator $ \st -> fmap pure $ newReference st a

    extRef m k a0 = do
        st <- ask
        r <- RefCreator $ \st -> newReference st a0
        -- TODO: remove dropHandler?
        dropHandler $ RefCreator $ \st -> do
            joinReg st m False $ \_ -> flip unRegister st $ runRefReaderT_ True $ fmap (^. k) $ readRef_ r
            registerTrigger r True $ \a -> flip unRegister st $ runRefReaderT_ True $ fmap (\b -> set k b a) $ readRefSimple m
        return $ pure r

    onChange (RefReaderTPure a) f = fmap RefReaderTPure $ f a
    onChange m f = RefCreator $ \st -> do
        r <- newReference st (const $ pure (), error "impossible #4")
        registerTrigger r True $ \(h, _) -> flip unRegister st $ do
            runM h Kill
            getHandler $ liftRefReader m >>= f
        return $ fmap snd $ readRef $ pure r

    onChangeEq (RefReaderTPure a) f = fmap RefReaderTPure $ f a
    onChangeEq r f = fmap readRef $ onChangeEq_ r f

    onChangeEq_ m f = RefCreator $ \st -> do
        r <- newReference st (const False, (const $ pure (), error "impossible #3"))
        registerTrigger r True $ \it@(p, (h', _)) -> flip unRegister st $ do
            a <- runRefReaderT_ True m
            if p a
              then return it
              else do
                runM h' Kill
                (h, b) <- getHandler $ f a
                return ((== a), (h, b))

        return $ lensMap (_2 . _2) $ pure r

    onChangeMemo (RefReaderTPure a) f = fmap RefReaderTPure $ join $ f a
    onChangeMemo (RefReaderT mr) f = RefCreator $ \st' -> do
        r <- newReference st' ((const False, ((error "impossible #2", const $ pure (), const $ pure ()) , error "impossible #1")), [])
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
        = tellHand h

{-# SPECIALIZE runRefCreator :: ((RefWriterOf (RefReaderT IO) () -> IO ()) -> RefCreator IO a) -> IO a #-}
runRefCreator :: NewRef m => ((RefWriterOf (RefReaderT m) () -> m ()) -> RefCreator m a) -> m a
--runRefCreator :: (m ~ RefCreator n, NewRef n) => ((RefWriter m () -> EffectM m ()) -> m a) -> EffectM m a
runRefCreator f = do
    a <- newRef' $ const $ pure ()
    b <- newRef' mempty
    c <- newRef' $ return ()
    d <- newRef' 0
    let s = GlobalVars a b c d
    unRegister (f $ flip unRegister s . runRefWriterT) s

-------------------- aux

{-# INLINE readRef_ #-}
readRef_ :: NewRef m => RefHandler m a -> RefReaderT m a
readRef_ r = RefReaderT $ \b -> RefCreator $ \st -> readWrite r b <&> fst

{-# INLINE ask #-}
ask :: Monad m => RefCreator m (GlobalVars m)
ask = RefCreator return

{-# INLINE runRefReaderT_ #-}
runRefReaderT_ _ (RefReaderTPure a) = return a
runRefReaderT_ b (RefReaderT x) = x b

runM m k = RefCreator . const $ m k

{-# NOINLINE liftRefWriter' #-}
liftRefWriter' :: RefWriterOf (RefReaderT m) a -> RefCreator m a
liftRefWriter' = runRefWriterT

{-# INLINE tellHand #-}
tellHand :: (NewRef m) => Handler m -> RefCreator m ()
tellHand h = RefCreator $ \st -> modRef' (_handlercollection st) $ modify $ \f msg -> f msg >> h msg

{-# INLINE dropHandler #-}
dropHandler :: NewRef m => RefCreator m a -> RefCreator m a
dropHandler m = RefCreator $ \st -> do
    x <- readRef' $ _handlercollection st
    a <- unRegister m st
    writeRef' (_handlercollection st) x
    return a

{-# INLINE getHandler #-}
getHandler :: NewRef m => RefCreator m a -> RefCreator m (Handler m, a)
getHandler m = RefCreator $ \st -> do
    let r = _handlercollection st
    h' <- readRef' r
    writeRef' r $ const $ pure ()
    a <- unRegister m st
    h <- readRef' r
    writeRef' r h'
    return (h, a)

{-# INLINE unsafeGet #-}
unsafeGet :: RefState m -> a
unsafeGet (RefState a _) = unsafeCoerce a

{-# INLINE newOrdRef #-}
newOrdRef :: NewRef m => GlobalVars m -> a -> m (OrdRef m a)
newOrdRef (GlobalVars _ _ _ st) a = do
    c <- readRef' st
    writeRef' st $ succ c
    r <- newRef' a
    return $ OrdRef c r

-------------- lenses

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

instance Monad m => Monoid (RefCreator m ()) where
--    {-# SPECIALIZE instance Monoid (RefCreator IO ()) #-}
    {-# INLINE mempty #-}
    mempty = return ()
    {-# INLINE mappend #-}
    m `mappend` n = m >> n

instance Monad m => Monad (RefCreator m) where
--    {-# SPECIALIZE instance Monad (RefCreator IO) #-}
    {-# INLINE return #-}
    return = RefCreator . const . return
    {-# INLINE (>>=) #-}
    RefCreator m >>= f = RefCreator $ \r -> m r >>= \a -> unRegister (f a) r

instance Applicative m => Applicative (RefCreator m) where
--    {-# SPECIALIZE instance Applicative (RefCreator IO) #-}
    {-# INLINE pure #-}
    pure = RefCreator . const . pure
    {-# INLINE (<*>) #-}
    RefCreator f <*> RefCreator g = RefCreator $ \r -> f r <*> g r

instance Functor m => Functor (RefCreator m) where
--    {-# SPECIALIZE instance Functor (RefCreator IO) #-}
    {-# INLINE fmap #-}
    fmap f (RefCreator m) = RefCreator $ fmap f . m

instance MonadFix m => MonadFix (RefCreator m) where
--    {-# SPECIALIZE instance MonadFix (RefCreator IO) #-}
    mfix f = RefCreator $ \r -> mfix $ \a -> unRegister (f a) r

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

instance NewRef m => MonadRefReader (RefCreator m) where
    {-# SPECIALIZE instance MonadRefReader (RefCreator IO) #-}
    type BaseRef (RefCreator m) = RefHandler m
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

instance NewRef m => MonadMemo (RefCreator m) where
--    {-# SPECIALIZE instance MonadMemo (RefCreator IO) #-}
    memoRead = memoRead_ $ \r -> runRefWriterT . writeRefSimple r

instance NewRef m => MonadEffect (RefWriterOf (RefReaderT m)) where
--    {-# SPECIALIZE instance MonadEffect (RefWriterOf (RefReaderT IO)) #-}
    type EffectM (RefWriterOf (RefReaderT m)) = m
--    {-# INLINE liftEffectM #-}
    liftEffectM = RefWriterT . RefCreator . const

instance NewRef m => MonadEffect (RefCreator m) where
--    {-# SPECIALIZE instance MonadEffect (RefCreator IO) #-}
    type EffectM (RefCreator m) = m
--    {-# INLINE liftEffectM #-}
    liftEffectM = RefCreator . const

instance Eq (OrdRef m a) where
--    {-# SPECIALIZE instance Eq (OrdRef IO a) #-}
    OrdRef i _ == OrdRef j _ = i == j

instance Ord (OrdRef m a) where
--    {-# SPECIALIZE instance Ord (OrdRef IO a) #-}
    OrdRef i _ `compare` OrdRef j _ = i `compare` j

