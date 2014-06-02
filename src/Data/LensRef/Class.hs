{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_HADDOCK prune #-}
{-# OPTIONS_HADDOCK not-home #-}
-- | Core lensref interface
module Data.LensRef.Class
    (
    -- * References
      RefClass (..)
    , RefSimple
    , RefWriterOf
    , RefWriterSimple

    , MonadRefReader (..)
    , MonadRefWriter (..)
    , Ref
    , RefReader
    , RefWriter

    -- * Reference creation
    , MonadRefCreator (..)

    -- * Effects
    , MonadEffect (..)

    -- * Dynamic networks
    , MonadRegister (..)
    , RegionStatusChange (..)
    , RegionStatusChangeHandler

    -- * Other
    , MonadMemo (..)
    ) where


import Control.Applicative
import Control.Monad.Writer
import Control.Monad.Trans.Control
import Control.Lens.Simple --(Lens', united)

--------------------------------


{- |
Type class for references which can be joined and on which lenses can be applied.

The join operation is 'join' from "Control.Monad":
If @(r :: RefReaderSimple r (RefSimple r a))@ then @(join r :: RefSimple r a)@.
This is possible because reference operations work with @(RefReaderSimple r (r a))@ instead
of just @(r a)@. For more compact type signatures, @(RefReaderSimple r (r a))@ is called @(RefSimple r a)@.
-}
class ( MonadRefReader (RefReaderSimple r)
      , MonadRefWriter (RefWriterSimple r)
      , RefReader (RefReaderSimple r) ~ RefReaderSimple r
      )
    => RefClass r where

    {- | unit reference
    -}
    unitRef :: RefSimple r ()

    {- | Apply a lens on a reference.
    -}
    lensMap :: Lens' a b -> RefSimple r a -> RefSimple r b
{-
    -- proposed by Michael Sloan (experimental)
    traversalMap :: (Monoid b) => Traversal' a b -> RefSimple r a -> RefSimple r b
-}
    {- | Associated reference reader monad.

    @(RefReaderSimple m)@ is ismoroprhic to @('Reader' x)@ for some @x@.
    Laws which ensures this isomorphism (@(r :: RefReaderSimple m a)@ is arbitrary):

    prop> r >> pure ()  =  pure ()
    prop> liftA2 (,) r r  =  fmap (\a -> (a, a)) r

    See also <http://stackoverflow.com/questions/16123588/what-is-this-special-functor-structure-called>
    -}
    type RefReaderSimple r :: * -> *

    {- | Reference read.
    -}
    readRefSimple  :: RefSimple r a -> RefReaderSimple r a

    {- | Reference write.
    -}
    writeRefSimple :: RefSimple r a -> a -> RefWriterSimple r ()

data family RefWriterOf (m :: * -> *) :: * -> *

{- |
There are two associated types of a reference, 'RefReaderSimple' and 'RefWriterSimple' which determines each-other.
This is implemented by putting only 'RefReaderSimple' into the 'RefClass' class and
adding a @RefWriterOf@ data family outside of 'RefClass'.

@RefWriterOf@ is hidden from the documentation because you never need it explicitly.
-}
type RefWriterSimple m = RefWriterOf (RefReaderSimple m)

-- | Reference wrapped into a RefReaderSimple monad. See the documentation of 'RefClass'.
type RefSimple r a = RefReaderSimple r (r a)

infixr 8 `lensMap`

-- | TODO
class ( Applicative m, Monad m
      , BaseRef (RefWriter m) ~ BaseRef m
      )
    => MonadRefReader m where

    -- | Base reference associated to the reference reader monad
    type BaseRef m :: * -> *

    liftRefReader :: RefReader m a -> m a

    {- | @readRef@ === @liftRefReader . readRefSimple@
    -}
    readRef :: (RefClass r, RefReader m ~ RefReaderSimple r) => RefSimple r a -> m a
    readRef = liftRefReader . readRefSimple


-- | TODO
type RefReader m = RefReaderSimple (BaseRef m)

-- | TODO
type RefWriter m = RefWriterSimple (BaseRef m)

-- | TODO
type Ref m a = RefSimple (BaseRef m) a



-- | TODO
class ( MonadRefReader m
      )
    => MonadRefWriter m where

    liftRefWriter :: RefWriter m a -> m a

    {- | @writeRef r@ === @liftRefWriter . writeRefSimple r@
    -}
    writeRef :: (RefClass r, RefReaderSimple r ~ RefReader m) => RefSimple r a -> a -> m ()
    writeRef r = liftRefWriter . writeRefSimple r

    -- | @modRef r f@ === @readRef r >>= writeRef r . f@
    modRef :: (RefClass r, RefReaderSimple r ~ RefReader m) => RefSimple r a -> (a -> a) -> m ()
    r `modRef` f = readRef r >>= writeRef r . f




{- | Monad for reference creation. Reference creation is not a method
of the 'RefClass' type class to make possible to
create the same type of references in multiple monads.

For basic usage examples, look into the source of @Data.LensRef.Test@.
-}
class ( RefClass (BaseRef m)
      , MonadRefReader m
      , MonadMemo m
      )
    => MonadRefCreator m where

    {- | Reference creation by extending the state of an existing reference.

    Suppose that @r@ is a reference and @k@ is a lens.

    Law 1: @extRef@ applies @k@ on @r@ backwards, i.e. 
    the result of @(extRef r k a0)@ should behaves exactly as @(lensMap k r)@.

    prop> (fmap (k .) $ extRef r k a0)  =  pure r

    Law 2: @extRef@ does not change the value of @r@:

    prop> (extRef r k a0 >> readRef r)  =  readRef r

    Law 3: Proper initialization of newly defined reference with @a0@:

    prop> (extRef r k a0 >>= readRef)  =  (readRef r >>= set k a0)
    -}
    extRef :: Ref m b -> Lens' a b -> a -> m (Ref m a)

    {- | @newRef@ extends the state @s@ in an independent way.

    @newRef@ === @extRef unitRef united@
    -}
    newRef :: a -> m (Ref m a)
    newRef = extRef unitRef united


-- | TODO
class (Monad m, Applicative m) => MonadMemo m where
    {- | Lazy monadic evaluation.
    In case of @y <- memoRead x@, invoking @y@ will invoke @x@ at most once.

    Laws:

     *  @(memoRead x >> pure ())@ === @pure ()@

     *  @(memoRead x >>= id)@ === @x@

     *  @(memoRead x >>= \y -> liftA2 (,) y y)@ === @fmap (\a -> (a, a)) y@

     *  @(memoRead x >>= \y -> liftA3 (,) y y y)@ === @fmap (\a -> (a, a, a)) y@

     *  ...
    -}
    memoRead :: m a -> m (m a)
{-
    memoWrite :: Eq b => (b -> m a) -> m (b -> m a)

    future :: (RefReader m a -> m a) -> m a
-}

-- | TODO
class ( Monad m, Applicative m
      , Monad (EffectM m), Applicative (EffectM m)
      )
    => MonadEffect m where

    type EffectM m :: * -> *

    liftEffectM :: EffectM m a -> m a

{-
class ( MonadRefCreator m
      )
    => MonadUpdate m where

    -- onUpdate
    accRef :: RefReader m a -> b -> (a -> b -> m b) -> m (Ref m b, Handle m)

    extRef :: Ref m b -> Lens' a b -> a -> m (Ref m a)

        -- handle:  block, unblock, kill, perform
-}


-- | Monad for dynamic actions
class ( MonadRefCreator m
      , MonadEffect m
      , MonadEffect (RefWriter m)
      , EffectM (RefWriter m) ~ EffectM m
      )
    => MonadRegister m where
{-
    onChangeAcc
        :: Eq b
        => RefReader m b
        -> b -> (b -> c)
        -> (b -> b -> c -> m (c -> m c))
        -> m (RefReader m c)
-}
--    onChange :: Eq a => RefReader m a -> m a

    onChange :: Eq a => RefReader m a -> (a -> m b) -> m (RefReader m b)
    onChange r f = onChangeMemo r $ pure . f

    onChangeMemo :: Eq a => RefReader m a -> (a -> m (m b)) -> m (RefReader m b)
--    onChangeMemo r f = onChangeAcc r undefined undefined $ \b _ _ -> fmap const $ f b

    onRegionStatusChange :: RegionStatusChangeHandler (EffectM m) -> m ()

    askPostpone :: m (RefWriter m () -> EffectM m ())


-- | TODO
data RegionStatusChange = Kill | Block | Unblock deriving (Eq, Ord, Show)

-- | TODO
type RegionStatusChangeHandler m = RegionStatusChange -> m ()

--------------------------------------------------- instances

instance (MonadRefReader m, Monoid w) => MonadRefReader (WriterT w m) where
    type BaseRef (WriterT w m) = BaseRef m
    liftRefReader = lift . liftRefReader

instance (MonadRefCreator m, Monoid w) => MonadRefCreator (WriterT w m) where
    extRef r l = lift . extRef r l
    newRef = lift . newRef

instance (MonadMemo m, Monoid w) => MonadMemo (WriterT w m) where
    memoRead m = liftWith $ \unlift -> fmap restoreT $ memoRead $ unlift m

instance (MonadEffect m, Monoid w) => MonadEffect (WriterT w m) where
    type EffectM (WriterT w m) = EffectM m
    liftEffectM = lift . liftEffectM
{-
instance (MonadRegister m, Monoid w) => MonadRegister (WriterT w m) where
    type UpdateM (WriterT w m) = UpdateM m
    onUpdate r b f = lift $ onUpdate r b f
    askPostpone = lift askPostpone
    onRegionStatusChange g = lift $ onRegionStatusChange g
-}







