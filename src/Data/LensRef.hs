{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
-- {-# OPTIONS_HADDOCK prune #-}
module Data.LensRef
    (
    -- * Core

    -- ** References
      unitRef, lensMap      , RefReaderSimple, RefClass --RefClass (..)
            , RefSimple
--    , RefWriterOf
--    , RefWriterSimple

    , liftRefReader, readRef --MonadRefReader (..)
    , writeRef --MonadRefWriter (..)

    -- ** Reference creation
    , newRef, extRef, MonadRefCreator --MonadRefCreator (..)
    , Ref
    , RefReader
    , RefWriter

    -- ** Dynamic networks
    , onChange, onChangeMemo, RefWriter, MonadRegister --MonadRegister (..)
--    , RegionStatusChange (..)

    -- ** Other
    , memoRead --MonadMemo (..)

    -- * Derived constructs
    , modRef
    , postponeModification
--    , undoTr

    , EqRefClass        --EqRefClass (..)
            , hasEffect
--    , EqRefSimple
    , EqRef
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

import Control.Applicative
import Control.Lens.Simple (set)

import Data.LensRef.Class

--------------------------------


-- | TODO
postponeModification :: MonadRegister m => RefWriter m () -> m ()
postponeModification m = askPostpone >>= liftEffectM . ($ m)


-- | @modRef r f@ === @readRef r >>= writeRef r . f@
modRef :: (MonadRefWriter m, RefClass r, RefReaderSimple r ~ RefReader m) => RefSimple r a -> (a -> a) -> m ()
r `modRef` f = readRef r >>= writeRef r . f





{- | Reference with inherent equivalence.

-}
class RefClass r => EqRefClass r where
    valueIsChanging :: RefSimple r a -> RefReaderSimple r (a -> Bool)

{- | @hasEffect r f@ returns @False@ iff @(modRef m f)@ === @(pure ())@.

@hasEffect@ is correct only if @toEqRef@ is applied on a pure reference (a reference which is a pure lens on the hidden state).

@hasEffect@ makes defining auto-sensitive buttons easier, for example.
-}
hasEffect
    :: EqRefClass r
    => RefSimple r a
    -> (a -> a)
    -> RefReaderSimple r Bool
hasEffect r f = valueIsChanging r <*> (f <$> readRef r)


-- | TODO
data EqRefCore r a = EqRefCore (r a) (a -> Bool{-changed-})

{- | RefClasss with inherent equivalence.

@EqRefSimple r a@ === @RefReaderSimple r (exist b . Eq b => (Lens' b a, r b))@

As a reference, @(m :: EqRefSimple r a)@ behaves as

@join $ fmap (uncurry lensMap) m@
-}
type EqRefSimple r a = RefReaderSimple r (EqRefCore r a)

-- | TODO
type EqRef m a = EqRefSimple (BaseRef m) a

{- | @EqRefSimple@ construction.
-}
toEqRef :: (RefClass r, Eq a) => RefSimple r a -> EqRefSimple r a
toEqRef r = EqRefCore <$> r <*> ((/=) <$> readRef r)

-- | TODO
newEqRef :: (MonadRefCreator m, Eq a) => a -> m (EqRef m a) 
newEqRef = fmap toEqRef . newRef

{- | An @EqRefSimple@ is a normal reference if we forget about the equality.

@fromEqRef m@ === @join $ fmap (uncurry lensMap) m@
-}
fromEqRef :: RefClass r => EqRefSimple r a -> RefSimple r a
fromEqRef m = (\(EqRefCore r _) -> r) <$> m

instance RefClass r => EqRefClass (EqRefCore r) where
    valueIsChanging m = (\(EqRefCore _r k) -> k) <$> m

instance RefClass r => RefClass (EqRefCore r) where

    type (RefReaderSimple (EqRefCore r)) = RefReaderSimple r

    readRefSimple = readRef . fromEqRef

    writeRefSimple = writeRefSimple . fromEqRef

    lensMap l m = (>>=) m $ \(EqRefCore r k) ->
        EqRefCore <$> (lensMap l $ pure r) <*> ((\a b -> k $ set l b a)  <$> readRef m)

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
        lr <- lensMap l $ pure r
        pure $ CorrBaseRef lr $ \b -> fmap (^. l) $ k $ set l b a

    unitRef = corrRef (const Nothing) unitRef

fromCorrRef :: RefClass r => CorrRef r a -> RefSimple r a
fromCorrRef m = m >>= \(CorrBaseRef r _) -> pure r

corrRef :: RefClass r => (a -> Maybe a) -> RefSimple r a -> CorrRef r a
corrRef f r = do
    r_ <- r
    pure $ CorrBaseRef r_ f

correction :: RefClass r => CorrRef r a -> RefReaderSimple r (a -> Maybe a)
correction r = do
    CorrBaseRef _ f <- r
    pure f
-}


