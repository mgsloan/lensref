{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
-- | Minimalized lens dependency. Compatible with the lens package.
module Control.Lens.Simple where

import Control.Applicative
import Control.Monad.Identity
import Control.Monad.Reader
import Control.Monad.State

-----------

type Lens s t a b = forall f. Functor f => (a -> f b) -> s -> f t
type Lens' s a = Lens s s a a

type Traversal s t a b = forall f. Applicative f => (a -> f b) -> s -> f t 
type Traversal' s a = Traversal s s a a

type Getting r s a = (a -> Const r a) -> s -> Const r s 

type ASetter s t a b = (a -> Identity b) -> s -> Identity t 

------------

lens :: (s -> a) -> (s -> b -> t) -> Lens s t a b
lens sa sbt afb s = sbt s <$> afb (sa s)

set :: ASetter s t a b -> b -> s -> t
set l b = runIdentity . l (\_ -> Identity b)
--set :: Lens s t a b -> b -> s -> t
--set l s = runIdentity . l (const $ Identity s)

over :: Lens s t a b -> (a -> b) -> s -> t
over l f = runIdentity . l (Identity . f)

united :: Lens' a ()
united f v = fmap (\() -> v) $ f ()

infixl 8 ^.

(^.) :: s -> Getting a s a -> a 
a ^. l = getConst $ l Const a

view :: MonadReader s m => Lens' s a -> m a
view l = asks (^. l)

(.=) :: MonadState s m => Lens' s a -> a -> m ()
l .= a = modify $ set l a

magnify :: Monad m => Lens' a b -> ReaderT b m c -> ReaderT a m c
magnify l (ReaderT f) = ReaderT $ \a -> f $ a ^. l

infixl 1 <&>

(<&>) :: Functor f => f a -> (a -> b) -> f b
as <&> f = f <$> as

---------------------------------

class Field1 s t a b | s -> a, t -> b, s b -> t, t a -> s where
    _1 :: Lens s t a b

instance Field1 (a,b) (a',b) a a' where
  _1 k ~(a,b) = k a <&> \a' -> (a',b)

instance Field1 (a,b,c) (a',b,c) a a' where
  _1 k ~(a,b,c) = k a <&> \a' -> (a',b,c)

instance Field1 (a,b,c,d) (a',b,c,d) a a' where
  _1 k ~(a,b,c,d) = k a <&> \a' -> (a',b,c,d)

class Field2 s t a b | s -> a, t -> b, s b -> t, t a -> s where
    _2 :: Lens s t a b

instance Field2 (a,b) (a,b') b b' where
  _2 k ~(a,b) = k b <&> \b' -> (a,b')

instance Field2 (a,b,c) (a,b',c) b b' where
  _2 k ~(a,b,c) = k b <&> \b' -> (a,b',c)

instance Field2 (a,b,c,d) (a,b',c,d) b b' where
  _2 k ~(a,b,c,d) = k b <&> \b' -> (a,b',c,d)

class Field3 s t a b | s -> a, t -> b, s b -> t, t a -> s where
    _3 :: Lens s t a b

instance Field3 (a,b,c) (a,b,c') c c' where
  _3 k ~(a,b,c) = k c <&> \c' -> (a,b,c')

