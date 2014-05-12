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
{-# OPTIONS_HADDOCK hide #-}
module Data.LensRef.TestEnv where

import Control.Monad.State
import Control.Monad.Writer hiding (listen)
import Control.Monad.Operational hiding (view)
import qualified Data.Sequence as Seq
import Control.Lens hiding ((|>))

import Unsafe.Coerce

import Data.LensRef
import Data.LensRef.Common

----------------------


class MonadRegister tm => MonadRegisterRun tm where

    type AsocT tm :: *

    runReg :: (m ~ EffectM tm)
        => m (AsocT tm)
        -> (AsocT tm -> m ())
        -> tm a
        -> m (a, m ())



--------------------------

newtype Id = Id Int deriving Eq

instance Show Id where show (Id i) = "#" ++ show i

newtype Port a = Port { unPort :: Int } deriving (Eq, Num)

instance Show (Port a) where show (Port i) = show i

data Inst t a where
    Message  :: String -> Inst t ()
    Listen   :: Show b => Port b -> (b -> Prog t ()) -> Inst t Id
    SetStatus  :: Id -> RegisteredCallbackCommand -> Inst t ()

    ReadI :: Inst t t
    WriteI :: t -> Inst t ()
    NewRef :: a -> Inst t (Morph (StateT a (Prog t)) (Prog t))

type Prog t = ProgramT (Inst t) (State (Seq.Seq Anny))


---------------------------------------------------

instance NewRef (Prog t) where
    newRef' = singleton . NewRef

message = liftEffectM . singleton . Message

listen :: (MonadRegister m, EffectM m ~ Prog t, Show a) => Port a -> (a -> Modifier m ()) -> m ()
listen i m = do
    f <- registerCallback m
    id <- liftEffectM . singleton $ Listen i f
    message $ "listener " ++ show id
    getRegionStatus $ \s -> do
        singleton $ SetStatus id s
        when (s == Kill) $ singleton $ Message $ show s ++ " " ++ show id


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
    Return x -> return x
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
handEr = showRes . runWriter -- . runErrorT
showRes ((),l) = f [] l where
    f acc (Right x: xs) = f (x:acc) xs
    f acc (Left (Right s): Left (Left s'): xs) | s == s' = f (("unfail " ++ s'): acc) xs
    f acc (Left e: _) = reverse $ either id id e: acc
    f _ [] = []

type ST m = ([m], Listeners m, Int, Seq.Seq Anny)

data Anny = forall x . Anny x

data Listener m = forall a . Show a => Listener
    { listenerId :: Id
    , listenerPort :: Port a
    , listenerStatus :: RegisteredCallbackCommand
    , listenerCallback :: a -> Prog m ()
    }
type Listeners m = [Listener m]


coeval_ :: forall a b m
     . (Prog m () -> m)
    -> Prog m a -> Prog' b
    -> StateT (ST m) Er (a, Prog' b)
coeval_ lift = coeval where
 coeval q p = do
  (xx,li,co,vars_) <- get
  let (op, vars) = flip runState vars_ $ viewT $ q
  case ( op
      , runIdentity . viewT $ p) of
    (_, Error' s :>>= k) -> do
        unfail s
        coeval q (k ())
    (Message s :>>= k, Return x) -> do
        fail' $ "the following message expected: " ++ s ++ " instead of return"
        coeval (k ()) (return x)
    (Message s :>>= k, Message' s' :>>= k')
        | s == s' -> tell_ ("message: " ++ s) >> coeval (k ()) (k' ())
        | otherwise -> do
            fail' $ "the following message expected: " ++ s ++ " instead of " ++ s'
            coeval q (k' ())
    (Message s :>>= _, Send _i s' :>>= k') -> do
        fail' $ "the following message expected: " ++ s ++ " instead of send " ++ show s'
        coeval q (k' ())
    (SetStatus i Kill :>>= k, _) -> do
        let li' = filter ((/=i) . listenerId) li
        if length li' == length li
          then fail' "cant kill"
          else put (xx,li',co,vars)
        coeval (k ()) p
    (SetStatus i Block :>>= k, _) -> do
        let f (Listener i' c Unblock x) | i' == i = Listener i c Block x
            f x = x
        put (xx, map f li,co,vars)
        coeval (k ()) p
    (SetStatus i Unblock :>>= k, _) -> do
        let f (Listener i' c Block x) | i' == i = Listener i c Unblock x
            f x = x
        put (xx, map f li,co,vars)
        coeval (k ()) p
    (Listen i lr :>>= k, _) -> do
        put (xx, Listener (Id co) i Unblock lr: li, co + 1,vars)
        coeval (k $ Id co) p
    (ReadI :>>= k, _) | not $ null xx -> do
        let (q:qu) = xx
        put (qu, li, co,vars)
        coeval (k q) p
    (WriteI x :>>= k, _) -> do
        put (xx ++[x], li, co,vars)
        coeval (k ()) p

    (NewRef a :>>= k, _) -> do
        let n = Seq.length vars
            gg = Morph $ ff a
            ff :: forall aa bb . aa -> StateT aa (Prog m) bb -> Prog m bb
            ff _ (StateT f) = do
                vars <- get
                let (v1, v2_) = Seq.splitAt n vars
                    (v Seq.:< v2) = Seq.viewl v2_
                case v of
                    Anny w -> do
                      rr <- f $ unsafeCoerce w
                      case rr of
                        (x, w') -> do
                            put $ v1 Seq.>< (Anny w' Seq.<| v2)
                            return x
        put (xx, li, co,vars Seq.|> Anny a)
        coeval (k gg) p

    (_, Send i@(Port pi) s :>>= k) -> do
        tell_ $ "send " ++ show i ++ " " ++ show s
        if (not $ null xx)
          then do
            fail' $ "early send of " ++ show s
          else do
            let li' = [lift $ lr $ unsafeCoerce s | Listener _ (Port pi') Unblock lr <- li, pi == pi']
            if (null li')
              then do
                fail' $ "message is not received: " ++ show i ++ " " ++ show s
              else do
                put (xx ++ li', li, co,vars) --modify (`mappend` (li,[]))
        coeval q (k ())
    (ReadI :>>= _, _) | null xx -> return (undefined, p)
    (Return x, _) -> return (x, p)



runTest_ :: (Eq a, Show a, m ~ Prog n)
    => (Prog n () -> n)
    -> (m n -> (n -> m ()) -> tm a -> m (a, m ()))
    -> tm a
    -> Prog' (a, Prog' ())
    -> IO ()
runTest_ lift runRegister_ r p0 = putStrLn $ unlines $ handEr $ flip evalStateT ([], [], 0, Seq.empty) $ do
    let    m = runRegister_ (singleton ReadI) (singleton . WriteI) r
    ((a1,c),pe) <- coeval_ lift m p0
    (a2,p) <- getProg' pe
    when (a1 /= a2) $ fail' $ "results differ: " ++ show a1 ++ " vs " ++ show a2
    (_, pr) <- coeval_ lift c p
    getProg' pr

------------------------------------------------

-- | Check an equality.
(==?) :: (Eq a, Show a, MonadRegisterRun m, EffectM m ~ Prog (AsocT m)) => a -> a -> m ()
rv ==? v = when (rv /= v) $ message $ "runTest failed: " ++ show rv ++ " /= " ++ show v

-- | Check the current value of a given reference.
(==>) :: (Eq a, Show a, MonadRegisterRun m, EffectM m ~ Prog (AsocT m)) => Ref m a -> a -> m ()
r ==> v = readRef r >>= (==? v)

infix 0 ==>, ==?




