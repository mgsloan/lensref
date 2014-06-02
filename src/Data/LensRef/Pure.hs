{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
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
import Data.List
import Debug.Trace
import qualified Data.IntSet as IntSet
import qualified Data.IntMap as IntMap
import qualified Data.Set as Set
import qualified Data.Map as Map
import Control.Applicative
import Control.Monad
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer
import Control.Lens.Simple

import Unsafe.Coerce

import Data.LensRef.Class
import Data.LensRef.Common
#ifdef __TESTS__
import Data.LensRef.TestEnv hiding (Id)
import Data.LensRef.Test
#endif

---------------------------------

type Id = Int
type Ids = IntSet.IntSet

-- collecting identifiers of references on whose values the return value depends on
type TrackedT = WriterT Ids

-- collecting handlers (may be factored out)
type HandlerT m = WriterT (RegionStatusChangeHandler (MonadMonoid (CreateT m))) m

---------------------------------

-- invariant property: the St state is only exteded, never changed
newtype CreateT m a
    = CreateT { runCreateT :: StateT (St m) (TrackedT (HandlerT m)) a }
        deriving (Functor, Applicative, Monad, MonadFix, MonadState (St m))

mapCreateT f = CreateT . f . runCreateT

addTrackingIds :: (Monad m, Applicative m) => Ids -> CreateT m ()
addTrackingIds = CreateT . lift . tell

getTrackingIds :: (Monad m, Applicative m) => CreateT m a -> CreateT m (Ids, a)
getTrackingIds = mapCreateT $ mapStateT $ mapWriterT $ fmap g
  where
    g ((a,s),w) = (((w,a),s),mempty)

addHandler :: (Monad m, Applicative m) => RegionStatusChangeHandler (MonadMonoid (CreateT m)) -> CreateT m ()
addHandler = CreateT . lift . lift . tell

getHandler :: (Monad m, Applicative m) => CreateT m a -> CreateT m (RegionStatusChangeHandler (MonadMonoid (CreateT m)), a)
getHandler = mapCreateT $ mapStateT $ mapWriterT $ mapWriterT $ fmap g
  where
    g (((a,s),v),w) = ((((w,a),s),v),mempty)

instance MonadTrans CreateT where
    lift = CreateT . lift . lift . lift

type ModifyT = CreateT  -- changes also may happen
type ReadT = CreateT    -- just read

-----------------------------------------

-- state of all references
type St m = IntMap.IntMap (ReferenceState m)

initAllReferenceState :: St m
initAllReferenceState = mempty

data Dyn where
    Dyn :: a -> Dyn

unsafeGet :: Dyn -> a
unsafeGet (Dyn a) = unsafeCoerce a

-- state of one reference
data ReferenceState m = ReferenceState
    { refValue :: Dyn
    , updateFunctions :: IntMap.IntMap (Bool, Ids, ModifyT m ())
            -- registered update functions
            -- (alive, dependencies, what to run if at least one of the dependency changes)
    }

------------------------------------------

data Reference m a = Reference
    { readRef_  :: ReadT m a
    , writeRef_ :: a -> ModifyT m ()
    , register  :: Bool{-run initially-} -> (a -> ModifyT m a) -> ModifyT m ()
    }

nextKey = maybe 0 ((+1) . fst . fst) . IntMap.maxViewWithKey

newReference :: (Monad m, Applicative m) => a -> CreateT m (Reference m a)
newReference a = do
    i <- gets nextKey
    modify $ IntMap.insert i (ReferenceState (Dyn a) mempty)

    let
        getVal = gets $ unsafeGet . refValue . fromMaybe (error "fatal: cant find ref value") . IntMap.lookup i
        setVal a = modify $ IntMap.adjust (\(ReferenceState _ upd) -> ReferenceState (Dyn a) upd) i  -- dependency preserved

        -- TODO: check uniqueness of ids?
        addReg ids upd = state f where
          f st =
            ( delReg
            , IntMap.adjust (\(ReferenceState a upds) -> ReferenceState a $ IntMap.insert ri (True, ids, upd modReg) upds) i st
            )
           where
            ri = maybe (error "impossible") (\(ReferenceState _ upds) -> nextKey upds) $ IntMap.lookup i st
            delReg msg = modify $ IntMap.adjust (\(ReferenceState a upds) -> ReferenceState a $ IntMap.update (f msg) ri upds) i
              where
                f Kill _ = Nothing
                f Block (_,ids,upd) = Just (False,ids,upd)
                f Unblock (_,ids,upd) = Just (True,ids,upd)

            modReg ids = modify $ IntMap.adjust (\(ReferenceState a upds) -> ReferenceState a $ IntMap.adjust f ri upds) i
              where
                f (alive, _, upd) = (alive, ids, upd)

    pure Reference
        { readRef_ = do
            addTrackingIds $ IntSet.singleton i
            getVal

        , writeRef_ = \a -> do
            let gr (_, ids, act) = (ids, act)
            graph <- gets $ IntMap.map (map gr . filter (^. _1) . IntMap.elems . updateFunctions)
            sequence_ $ either (const $ error "cycle") id $ comp graph i $ setVal a

        , register = \init upd -> do
            let gv = getTrackingIds $ getVal >>= upd
            (ids, a) <- gv
            when init $ setVal a
            kill <- addReg ids $ \mod -> do
                (ids, a) <- gv
                setVal a
                mod ids
            addHandler $ MonadMonoid . kill
        }

joinReg :: (Monad m, Applicative m) => ReadT m (Reference m a) -> Bool -> (a -> ModifyT m a) -> ModifyT m ()
joinReg m init a = do
    r <- newReference mempty
    register r True $ \kill -> do
        runMonadMonoid $ kill Kill
        r <- m
        fmap fst $ getHandler $ register r init a
    addHandler $ \msg -> MonadMonoid $ do
        h <- readRef_ r
        runMonadMonoid $ h msg

instance (Monad m, Applicative m) => RefClass (Reference m) where
    type RefReaderSimple (Reference m) = CreateT m

    unitRef = pure $ Reference
        { readRef_ = pure ()
        , writeRef_ = const $ pure ()
        , register = const $ const $ pure ()
        }

    readRefSimple = join . fmap readRef_

    writeRefSimple mr a = RefWriterOfCreateT $ do
        r <- mr
        writeRef_ r a

    lensMap k mr = pure $ Reference
        { readRef_  = fmap (^. k) $ readRefSimple mr
        , writeRef_ = \b -> do
            r <- mr
            a <- readRef_ r
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
instance (Monad m, Applicative m) => MonadRefReader (CreateT m) where
    type BaseRef (CreateT m) = Reference m
    liftRefReader = id

newtype instance RefWriterOf (CreateT m) a
    = RefWriterOfCreateT { runRefWriterOfCreateT :: ModifyT m a }
        deriving (Monad, Applicative, Functor)

instance (Monad m, Applicative m) => MonadRefReader (RefWriterOf (CreateT m)) where
    type BaseRef (RefWriterOf (CreateT m)) = Reference m
    liftRefReader = RefWriterOfCreateT

instance (Monad m, Applicative m) => MonadRefWriter (RefWriterOf (CreateT m)) where
    liftRefWriter = id

instance (Monad m, Applicative m) => MonadMemo (CreateT m) where
    memoRead = memoRead_

instance (Monad m, Applicative m) => MonadRefWriter (ModifyT m) where
    liftRefWriter = runRefWriterOfCreateT

instance (Monad m, Applicative m) => MonadRefCreator (CreateT m) where

    extRef m k a0 = do
        r <- newReference a0
        (kill, ()) <- getHandler $ joinReg m False $ \_ -> fmap (^. k) $ readRef_ r      -- TODO: kill
        (kill', ()) <- getHandler $ register r True $ \a -> fmap (\b -> set k b a) $ readRefSimple m      -- TODO: kill
        return $ pure r

    newRef = fmap pure . newReference

-----------------------------------

-- postpone function
type Inner m = ReaderT (Register m () -> m ()) m

newtype Register m a = Register { unRegister :: CreateT (Inner m) a }
    deriving (Functor, Applicative, Monad, MonadFix)

instance MonadTrans Register where
    lift = Register . lift . lift

instance (Monad m, Applicative m) => MonadEffect (RefWriterOf (CreateT (Inner m))) where
    type EffectM (RefWriterOf (CreateT (Inner m))) = m
    liftEffectM = RefWriterOfCreateT . lift . lift

instance (Monad m, Applicative m) => MonadEffect (Register m) where
    type EffectM (Register m) = m
    liftEffectM = Register . lift . lift

instance (Monad m, Applicative m) => MonadRefReader (Register m) where
    type BaseRef (Register m) = Reference (Inner m)
    liftRefReader = Register . liftRefReader

instance (Monad m, Applicative m) => MonadRefCreator (Register m) where
    extRef r l = Register . extRef r l
    newRef = Register . newRef

instance (Monad m, Applicative m) => MonadMemo (Register m) where
    memoRead = memoRead_

instance (Monad m, Applicative m) => MonadRefWriter (Register m) where
    liftRefWriter = Register . liftRefWriter

instance (Monad m, Applicative m) => MonadRegister (Register m) where

    askPostpone = do
        f <- Register $ CreateT ask
        return $ f . Register . runRefWriterOfCreateT

    onRegionStatusChange h
        = Register $ addHandler $ MonadMonoid . lift . lift . h

    -- TODO: postpone events?
    onChange m f = Register $ do
        r <- newReference (const False, (mempty, error "impossible #3"))
        register r True upd
        return $ fmap (snd . snd) $ readRef_ r
      where
        upd it@(p, (h', _)) = do
            a <- m
            if p a
              then return it
              else do
                runMonadMonoid $ h' Kill
                (h, b) <- getHandler $ unRegister $ f a
                return ((== a), (h, b))

    -- TODO: postpone events?
    onChangeMemo mr f = Register $ do
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
                    runMonadMonoid $ h2'' Kill
                    runMonadMonoid $ h1'' Block
                    runMonadMonoid $ h1' Unblock
                    (h2, b') <- getHandler $ unRegister m'
                    return (((== a), ((m',h1',h2), b')), it: filter (not . ($ a) . fst) memo)
                Nothing -> do
                    runMonadMonoid $ h2'' Kill
                    (h1, m') <- getHandler $ unRegister $ f a
                    (h2, b') <- getHandler $ unRegister m'
                    return (((== a), ((m',h1,h2), b')), it: memo)


runRegister :: (Monad m, Applicative m) => (forall a . m (m a, a -> m ())) -> Register m a -> m (a, m ())
runRegister newChan m = do
    (read, write) <- newChan
    runRegister_ read write m

runRegister_ :: (Monad m, Applicative m) => m (Register m ()) -> (Register m () -> m ()) -> Register m a -> m (a, m ())
runRegister_ read write m = do
    (a, s) <- run initAllReferenceState m
    pure $ (,) a $ fmap (const ()) $ run s $ forever $ join $ lift read
  where
    run s = flip runReaderT write . fmap fst . runWriterT . fmap fst . runWriterT . flip runStateT s . runCreateT . unRegister


runTests :: IO ()
#ifdef __TESTS__
runTests = tests runTest

runTest :: (Eq a, Show a) => String -> Register (Prog TP) a -> Prog' (a, Prog' ()) -> IO ()
runTest name = runTest_ name (TP . lift) $ \r w -> runRegister_ (fmap unTP r) (w . TP)

newtype TP = TP { unTP :: Register (Prog TP) () }
#else
runTests = fail "enable the tests flag like \'cabal configure --enable-tests -ftests; cabal build; cabal test\'"
#endif

-------------------------------------

comp :: IntMap.IntMap [(Ids, x)] -> Id -> x -> Either [Edge (Id, Ids)] [x]
comp gr a x = fmap (map (m Map.!)) $ topSort fst m2 (a, mempty)
  where
    m = Map.insert (a, mempty) x $ Map.fromList [((d, dep), x) | (d, deps) <- IntMap.toList gr, (dep, x) <- deps]
    grr (c, forb) = [(d, dep) | (d, deps) <- IntMap.toList gr, d /= c, d `IntSet.notMember` forb, (dep, x) <- deps, c `IntSet.member` dep]

    m2 = Map.fromList [(n, grr n) | n <- Map.keys m ]

------------------------------------ topological sort
 
type Edge a = (a, a)

-- topoligical sorting
-- TODO: check cycles with proj
topSort :: (Ord n, Ord k) => (n -> k) -> Map.Map n [n] -> n -> Either [Edge n] [n]
topSort proj g v
    | not $ null $ backEdges g' v = Left []
    | otherwise = fmap (v:) $ sortit $ Map.delete v g'
  where
    backEdges g p = [n | (n, ps) <- Map.toList g, p `elem` ps]

    sortit m | Map.null m    = Right []
    sortit m = case listToMaybe $ sort [n | n <- Map.keys m, null $ backEdges m n] of
        Nothing -> Left []
        Just p -> fmap (p:) $ sortit $ Map.map (filter (/= p)) $ Map.delete p m

    g' = Map.filterWithKey (\k _ -> Set.member k s) g
      where
        s = execState (chop v) mempty

        chop v = do
          visited <- gets $ Set.member v
          if visited
            then return ()
            else do
              modify $ Set.insert v
              mapM_ chop $ g Map.! v

