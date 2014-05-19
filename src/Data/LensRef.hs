{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_HADDOCK prune #-}
module Data.LensRef
    (
    -- * Core
      module Data.LensRef.Class

    -- * Derived constructs
    , modRef
    , postponeModification
--    , undoTr

    , EqRefClass (..)
    , EqRefSimple, EqRef
    , hasEffect
    , toEqRef
    , fromEqRef
    , newEqRef
{-
    , CorrRef
    , corrRef
    , fromCorrRef
    , correction
-}
    ) where

--import Control.Monad
import Control.Monad.Identity
import Control.Lens.Simple (set)

import Data.LensRef.Class

--------------------------------


-- | TODO
postponeModification :: MonadRegister m => Modifier m () -> m ()
postponeModification = liftEffectM . runIdentity <=< registerCallback . Identity


-- | @modRef r f@ === @readRef r >>= writeRef r . f@
modRef :: (MonadRefWriter m, RefClass r, RefReaderSimple r ~ RefReader m) => RefSimple r a -> (a -> a) -> m ()
r `modRef` f = readRef r >>= writeRef r . f





{- | Reference with inherent equivalence.

-}
class RefClass r => EqRefClass r where
    valueIsChanging :: RefSimple r a -> RefReaderSimple r (a -> Bool)

{- | @hasEffect r f@ returns @False@ iff @(modRef m f)@ === @(return ())@.

@hasEffect@ is correct only if @toEqRef@ is applied on a pure reference (a reference which is a pure lens on the hidden state).

@hasEffect@ makes defining auto-sensitive buttons easier, for example.
-}
hasEffect
    :: EqRefClass r
    => RefSimple r a
    -> (a -> a)
    -> RefReaderSimple r Bool
hasEffect r f = do
    a <- readRef r
    ch <- valueIsChanging r
    return $ ch $ f a


-- | TODO
data EqRefCore r a = EqRefCore (r a) (a -> Bool{-changed-})

{- | RefClasss with inherent equivalence.

@EqRefSimple r a@ === @RefReaderSimple r (exist b . Eq b => (Lens' b a, r b))@

As a reference, @(m :: EqRefSimple r a)@ behaves as

@join $ liftM (uncurry lensMap) m@
-}
type EqRefSimple r a = RefReaderSimple r (EqRefCore r a)

-- | TODO
type EqRef m a = EqRefSimple (BaseRef m) a

{- | @EqRefSimple@ construction.
-}
toEqRef :: (RefClass r, Eq a) => RefSimple r a -> EqRefSimple r a
toEqRef r = do
    a <- readRef r
    r_ <- r
    return $ EqRefCore r_ (/= a)

-- | TODO
newEqRef :: (MonadRefCreator m, Eq a) => a -> m (EqRef m a) 
newEqRef = liftM toEqRef . newRef

{- | An @EqRefSimple@ is a normal reference if we forget about the equality.

@fromEqRef m@ === @join $ liftM (uncurry lensMap) m@
-}
fromEqRef :: RefClass r => EqRefSimple r a -> RefSimple r a
fromEqRef m = m >>= \(EqRefCore r _) -> return r

instance RefClass r => EqRefClass (EqRefCore r) where
    valueIsChanging m = do
        EqRefCore _r k <- m
        return k

instance RefClass r => RefClass (EqRefCore r) where

    type (RefReaderSimple (EqRefCore r)) = RefReaderSimple r

    readRefSimple = readRef . fromEqRef

    writeRefSimple = writeRefSimple . fromEqRef

    lensMap l m = do
        a <- readRef m
        EqRefCore r k <- m
        lr <- lensMap l $ return r
        return $ EqRefCore lr $ \b -> k $ set l b a

    unitRef = toEqRef unitRef

{-
data CorrBaseRef r a = CorrBaseRef (r a) (a -> Maybe a{-corrected-})

type CorrRef r a = RefReaderSimple r (CorrBaseRef r a)

instance RefClass r => RefClass (CorrBaseRef r) where

    type (RefReaderSimple (CorrBaseRef r)) = RefReaderSimple r

    readRef = readRef . fromCorrRef

    writeRefSimple = writeRefSimple . fromCorrRef

    lensMap l m = do
        a <- readRef m
        CorrBaseRef r k <- m
        lr <- lensMap l $ return r
        return $ CorrBaseRef lr $ \b -> fmap (^. l) $ k $ set l b a

    unitRef = corrRef (const Nothing) unitRef

fromCorrRef :: RefClass r => CorrRef r a -> RefSimple r a
fromCorrRef m = m >>= \(CorrBaseRef r _) -> return r

corrRef :: RefClass r => (a -> Maybe a) -> RefSimple r a -> CorrRef r a
corrRef f r = do
    r_ <- r
    return $ CorrBaseRef r_ f

correction :: RefClass r => CorrRef r a -> RefReaderSimple r (a -> Maybe a)
correction r = do
    CorrBaseRef _ f <- r
    return f
-}


