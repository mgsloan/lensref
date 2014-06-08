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
{-# LANGUAGE TemplateHaskell #-}
module Data.LensRef.TestEnv where

import Control.Applicative
import Control.Monad.State
import Control.Monad.Writer hiding (listen, Any)
import Control.Monad.Operational
import Control.Monad.Identity
import qualified Data.Sequence as Seq
import Control.Lens.Simple hiding (view)

import Unsafe.Coerce

import Data.LensRef
import Data.LensRef.Class
import Data.LensRef.Common

--------------------------

newtype Id = Id Int deriving Eq

instance Show Id where show (Id i) = "#" ++ show i

newtype Port a = Port { unPort :: Int } deriving (Eq, Num)

instance Show (Port a) where show (Port i) = show i

data Inst a where
    Message  :: String -> Inst ()
    Listen   :: Show b => Port b -> (b -> Prog ()) -> Inst Id
    SetStatus  :: Id -> RegionStatusChange -> Inst ()

    ReadI :: Inst (Prog ())
    WriteI :: Prog () -> Inst ()
    NewRef :: a -> Inst (SRef (Prog) a)
    NewId :: Inst Int

type Prog = ProgramT (Inst) (State (Int, Seq.Seq Any))

---------------------------------------------------

newtype SRefProg a = SRefProg { runSRefProg :: forall x . StateT a (Prog) x -> Prog x }

instance NewRef (Prog) where
    type SRef (Prog) = SRefProg 
    newRef' = singleton . NewRef
    modRef' = runSRefProg
--    newId = singleton NewId

instance MonadEffect (Prog) where
    type EffectM (Prog) = Prog
    liftEffectM = id

message :: (MonadEffect m, EffectM m ~ Prog) => String -> m ()
message = liftEffectM . singleton . Message

infix 0 ==?

-- | Check an equality.
--(==?) :: (Eq a, Show a, MonadRegister m, EffectM m ~ Prog, MonadRegister (RefWriter m)) => a -> a -> m ()
rv ==? v = when (rv /= v) $ message $ "runTest failed: " ++ show rv ++ " /= " ++ show v


listen :: (MonadRegister m, EffectM m ~ Prog, Show a) => Port a -> (a -> RefWriter m ()) -> m ()
listen i m = do
    post <- askPostpone
    id <- liftEffectM . singleton $ Listen i $ post . m
    message $ "listener " ++ show id
    onRegionStatusChange $ \s -> do
        liftEffectM $ singleton $ SetStatus id s
        when (s == Kill) $ message $ show s ++ " " ++ show id


data Inst' a where
    Message' :: String -> Inst' ()
    Error'   :: String -> Inst' ()
    Send     :: forall a . Show a => Port a -> a -> Inst' ()

type Prog' = Program Inst'

message' = singleton . Message'
error' = singleton . Error'
send i s = singleton $ Send i s

--getProg' :: MonadError String m => Prog' b -> m b
getProg' :: Prog' b
    -> StateT s Er b
getProg' p = case runIdentity . viewT $ p of
    Return x -> pure x
    Send i s :>>= p -> do
        fail' $ "end expected instead of send " ++ show i ++ " " ++ show s
        getProg' $ p ()
    Message' s :>>= p -> do
        fail' $ "end expected instead of message' " ++ s
        getProg' $ p ()
    Error' s :>>= p -> do
        fail' $ "end expected instead of unfail " ++ s
        getProg' $ p ()
  

type Er = Writer [Either (Either String String) String] --ErrorT String (Writer [String])

tell_ s = tell [Right s]
fail' s = tell [Left $ Right s]
unfail s = tell [Left $ Left s]
handEr name = showRes name . runWriter -- . runErrorT
showRes name ((),l) = case f [] l of
    [] -> []
    xs -> ("test " ++ name ++ " failed.") : xs ++ [""]
  where
    f acc (Right x: xs) = f (x:acc) xs
    f acc (Left (Right s): Left (Left s'): xs) | s == s' = f (("unfail " ++ s'): acc) xs
    f acc (Left e: _) = reverse $ either id id e: acc
    f _ [] = []

data Any = forall x . Any x

data Listener = forall a . Show a => Listener
    { _listenerId :: Id
    , _listenerPort :: Port a
    , _listenerStatus :: RegionStatusChange
    , _listenerCallback :: a -> Prog ()
    }
--makeLenses ''Listener

listenerId :: Lens' (Listener) Id
listenerId k (Listener a b c d) = k a <&> \a' -> Listener a' b c d

data ST = ST
    { _postponed :: [Prog ()]
    , _listeners :: [Listener]
    , _idcounter :: Int
    , _vars :: (Int, Seq.Seq Any)
    }
--makeLenses ''ST

postponed :: Lens' (ST) [Prog ()]
postponed k (ST a b c d) = k a <&> \a' -> ST a' b c d

listeners :: Lens' (ST) [Listener]
listeners k (ST a b c d) = k b <&> \b' -> ST a b' c d

idcounter :: Lens' (ST) Int
idcounter k (ST a b c d) = k c <&> \c' -> ST a b c' d

vars :: Lens' (ST) (Int, Seq.Seq Any)
vars k (ST a b c d) = k d <&> \d' -> ST a b c d'


coeval_ :: forall a b
     . (Prog () -> Prog ())
    -> Prog a
    -> Prog' b
    -> StateT (ST) Er (Maybe a, Prog' b)
coeval_ lift_ q p = do
    op <- zoom vars $ mapStateT lift $ viewT q
    coeval__ lift_ op p

coeval__ :: forall a b
     . (Prog () -> Prog ())
    -> ProgramViewT (Inst) (State (Int, Seq.Seq Any)) a
    -> Prog' b
    -> StateT (ST) Er (Maybe a, Prog' b)
coeval__ lift_ op p = do
  nopostponed <- use $ postponed . to null
  case (op, view p) of

    (_, Error' s :>>= k) -> do
        unfail s
        coeval__ lift_ op $ k ()

    (Message s :>>= k, Return x) -> do
        fail' $ "the following message expected: " ++ s ++ " instead of pure"
        coeval_ lift_ (k ()) (pure x)

    (Message s :>>= k, Message' s' :>>= k')
        | s == s' -> do
            tell_ ("message: " ++ s)
            coeval_ lift_ (k ()) (k' ())
        | otherwise -> do
            fail' $ "the following message expected: " ++ s ++ " instead of " ++ s'
            coeval__ lift_ op $ k' ()

    (Message s :>>= _, Send _i s' :>>= k') -> do
        fail' $ "the following message expected: " ++ s ++ " instead of send " ++ show s'
        coeval__ lift_ op (k' ())

    (SetStatus i status :>>= k, _) -> do
        listeners %= case status of
            Kill -> filter ((/=i) . (^. listenerId))
            Block -> map f where
                f (Listener i' c Unblock x) | i' == i = Listener i c Block x
                f x = x
            Unblock -> map f where
                f (Listener i' c Block x) | i' == i = Listener i c Unblock x
                f x = x
        coeval_ lift_ (k ()) p

    (Listen i lr :>>= k, _) -> do
        co <- use idcounter
        listeners %= (Listener (Id co) i Unblock lr :)
        idcounter %= (+1)
        coeval_ lift_ (k $ Id co) p

    (ReadI :>>= k, _) | not nopostponed -> do
        x <- use $ postponed . to head
        postponed %= tail
        coeval_ lift_ (k x) p

    (WriteI x :>>= k, _) -> do
        postponed %= (++[x])
        coeval_ lift_ (k ()) p

    (NewId :>>= k, _) -> do
        i <- zoom (vars . _1) $ state $ \c -> (c, succ c)
        coeval_ lift_ (k i) p

    (NewRef a :>>= k, _) -> do
        n <- use $ vars . _2 . to Seq.length

        let ff :: forall aa bb . aa -> StateT aa (Prog) bb -> Prog bb
            ff _ (StateT f) = do
                v <- gets $ (`Seq.index` n) . snd
                modify $ over _2 $ Seq.update n $ error "recursive reference modification"
                case v of
                  Any w -> do
                    (x, w') <- f $ unsafeCoerce w
                    modify $ over _2 $ Seq.update n $ Any w'
                    pure x
        (vars . _2) %= (Seq.|> Any a)
        coeval_ lift_ (k $ SRefProg $ ff a) p

    (_, Send i@(Port pi) s :>>= k) -> do
        tell_ $ "send " ++ show i ++ " " ++ show s
        if not nopostponed
          then do
            fail' $ "early send of " ++ show s
          else do
            li' <- use $ listeners . to (\li -> [lift_ $ lr $ unsafeCoerce s | Listener _ (Port pi') Unblock lr <- li, pi == pi'])
            if (null li')
              then do
                fail' $ "message is not received: " ++ show i ++ " " ++ show s
              else do
                postponed %= (++ li')
        coeval__ lift_ op (k ())

    (ReadI :>>= _, _) | nopostponed -> pure (Nothing, p)

    (Return x, _) -> pure (Just x, p)

type Er' = Writer [Either (Either String String) String] --ErrorT String (Writer [String])


eval_ :: forall a
     . (Prog () -> Prog ())
    -> Prog a
    -> StateT (ST) Er' (Either a (Prog () -> Prog a))
eval_ lift_ q = do
    op <- zoom vars $ mapStateT lift $ viewT q
    eval__ lift_ op

eval__ :: forall a
     . (Prog () -> Prog ())
    -> ProgramViewT (Inst) (State (Int, Seq.Seq Any)) a
    -> StateT (ST) Er' (Either a (Prog () -> Prog a))
eval__ lift_ op = do
  nopostponed <- use $ postponed . to null
  case op of

    Message s :>>= k -> do
        tell_ ("message: " ++ s)
        eval_ lift_ (k ())

    SetStatus i status :>>= k -> do
        listeners %= case status of
            Kill -> filter ((/=i) . (^. listenerId))
            Block -> map f where
                f (Listener i' c Unblock x) | i' == i = Listener i c Block x
                f x = x
            Unblock -> map f where
                f (Listener i' c Block x) | i' == i = Listener i c Unblock x
                f x = x
        eval_ lift_ (k ())

    Listen i lr :>>= k -> do
        co <- use idcounter
        listeners %= (Listener (Id co) i Unblock lr :)
        idcounter %= (+1)
        eval_ lift_ (k $ Id co)

    ReadI :>>= k | not nopostponed -> do
        x <- use $ postponed . to head
        postponed %= tail
        eval_ lift_ (k x)

    WriteI x :>>= k -> do
        postponed %= (++[x])
        eval_ lift_ (k ())

    NewId :>>= k -> do
        i <- zoom (vars . _1) $ state $ \c -> (c, succ c)
        eval_ lift_ (k i)

    NewRef a :>>= k -> do
        n <- use $ vars . _2 . to Seq.length

        let ff :: forall aa bb . aa -> StateT aa (Prog) bb -> Prog bb
            ff _ (StateT f) = do
                v <- gets $ (`Seq.index` n) . snd
                modify $ over _2 $ Seq.update n $ error "recursive reference modification"
                case v of
                  Any w -> do
                    (x, w') <- f $ unsafeCoerce w
                    modify $ over _2 $ Seq.update n $ Any w'
                    pure x
        (vars . _2) %= (Seq.|> Any a)
        eval_ lift_ (k $ SRefProg $ ff a)
{-
    (_, Send i@(Port pi) s :>>= k) -> do
        tell_ $ "send " ++ show i ++ " " ++ show s
        if not nopostponed
          then do
            fail' $ "early send of " ++ show s
          else do
            li' <- use $ listeners . to (\li -> [lift_ $ lr $ unsafeCoerce s | Listener _ (Port pi') Unblock lr <- li, pi == pi'])
            if (null li')
              then do
                fail' $ "message is not received: " ++ show i ++ " " ++ show s
              else do
                postponed %= (++ li')
        coeval__ lift_ op (k ())
-}
    ReadI :>>= q | nopostponed -> pure $ Right q

    Return x -> pure $ Left x


runTest_ :: (Eq a, Show a, m ~ Prog)
    => String
    -> (Prog () -> Prog ())
    -> (m (Prog ()) -> (Prog () -> m ()) -> tm a -> m (a, m ()))
    -> tm a
    -> Prog' (a, Prog' ())
    -> IO ()
runTest_ name lift runRegister_ r p0 = showError $ handEr name $ flip evalStateT (ST [] [] 0 (0, Seq.empty)) $ do
    (Just (a1,c),pe) <- coeval_ lift (runRegister_ (singleton ReadI) (singleton . WriteI) r) p0
    (a2,p) <- getProg' pe
    when (a1 /= a2) $ fail' $ "results differ: " ++ show a1 ++ " vs " ++ show a2
    (_, pr) <- coeval_ lift c p
    getProg' pr

showError [] = pure ()
showError xs = fail $ "\n" ++ unlines xs



