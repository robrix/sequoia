{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FunctionalDependencies #-}
module Focalized.Calculus.Core
( -- * Core
  Core(..)
  -- * Structural
, Structural
, Weaken(..)
, wkL'
, wkR'
, Contract(..)
, Exchange(..)
  -- * Contextual
, Contextual(..)
, poppedL
, poppedR
, popL2
, popR2
, pushL2
, pushR2
, mapL
, mapR
-- , mapL2
, mapR2
, liftL
, liftR
, lowerL
, lowerR
, Contextually(..)
) where

import Control.Monad (join)
import Data.Functor.Contravariant
import Focalized.CPS
import Focalized.Calculus.Context
import Prelude hiding (init)

class Core s where
  {-# MINIMAL ((>>>) | (<<<)), init #-}

  (>>>)
    :: _Γ -|s|- _Δ > a   ->   a < _Γ -|s|- _Δ
    -- --------------------------------------
    ->              _Γ -|s|- _Δ
  (>>>) = flip (<<<)

  (<<<)
    :: a < _Γ -|s|- _Δ   ->   _Γ -|s|- _Δ > a
    -- --------------------------------------
    ->              _Γ -|s|- _Δ
  (<<<) = flip (>>>)

  infixr 1 >>>, <<<

  init
    -- -------------------
    :: a < _Γ -|s|- _Δ > a


-- Structural

type Structural s = (Weaken s, Contract s, Exchange s)


class Core s => Weaken s where
  wkL
    ::     _Γ -|s|- _Δ
    -- ---------------
    -> a < _Γ -|s|- _Δ

  wkR
    :: _Γ -|s|- _Δ
    -- ---------------
    -> _Γ -|s|- _Δ > a


wkL'
  :: (Weaken s, Exchange s)
  => a     < _Γ -|s|- _Δ
  -- -------------------
  -> a < b < _Γ -|s|- _Δ
wkL' = exL . wkL

wkR'
  :: (Weaken s, Exchange s)
  => _Γ -|s|- _Δ > a
  -- -------------------
  -> _Γ -|s|- _Δ > b > a
wkR' = exR . wkR


class Core s => Contract s where
  cnL
    :: a < a < _Γ -|s|- _Δ
    -- -------------------
    ->     a < _Γ -|s|- _Δ

  cnR
    :: _Γ -|s|- _Δ > a > a
    -- -------------------
    -> _Γ -|s|- _Δ > a


class Core s => Exchange s where
  exL
    :: a < b < _Γ -|s|- _Δ
    -- -------------------
    -> b < a < _Γ -|s|- _Δ

  exR
    :: _Γ -|s|- _Δ > a > b
    -- -------------------
    -> _Γ -|s|- _Δ > b > a


class Core s => Contextual r s | s -> r where
  -- | Pop something off the input context which can later be pushed. Used with 'pushL', this provides a generalized context restructuring facility.
  --
  -- @
  -- popL . pushL = id
  -- @
  -- @
  -- pushL . popL = id
  -- @
  popL
    :: (a -> _Γ -|s|- _Δ)
    -- ------------------
    ->  a  < _Γ -|s|- _Δ

  -- | Pop something off the output context which can later be pushed. Used with 'pushR', this provides a generalized context restructuring facility.
  --
  -- @
  -- popR . pushR = id
  -- @
  -- @
  -- pushR . popR = id
  -- @
  popR
    :: (r •a -> _Γ -|s|- _Δ)
    -- ------------------------
    ->          _Γ -|s|- _Δ > a


  -- | Push something onto the input context which was previously popped off it. Used with 'popL', this provides a generalized context restructuring facility. It is undefined what will happen if you push something which was not previously popped.
  --
  -- @
  -- popL . pushL = id
  -- @
  -- @
  -- pushL . popL = id
  -- @
  pushL
    ::  a  < _Γ -|s|- _Δ
    -- ------------------
    -> (a -> _Γ -|s|- _Δ)

  -- | Push something onto the output context which was previously popped off it. Used with 'popR', this provides a generalized context restructuring facility. It is undefined what will happen if you push something which was not previously popped.
  --
  -- @
  -- popR . pushR = id
  -- @
  -- @
  -- pushR . popR = id
  -- @
  pushR
    ::          _Γ -|s|- _Δ > a
    -- ------------------------
    -> (r •a -> _Γ -|s|- _Δ)


poppedL
  :: Contextual r s
  => (_Γ -|s|- _Δ     ->     _Γ' -|s|- _Δ')
  -- --------------------------------------
  -> (a < _Γ -|s|- _Δ -> a < _Γ' -|s|- _Δ')
poppedL f p = popL (f . pushL p)

poppedR
  :: Contextual r s
  => (_Γ -|s|- _Δ     -> _Γ' -|s|- _Δ')
  -- --------------------------------------
  -> (_Γ -|s|- _Δ > a -> _Γ' -|s|- _Δ' > a)
poppedR f p = popR (f . pushR p)


popL2
  :: Contextual r s
  => (a -> b -> _Γ -|s|- _Δ)
  -- -----------------------
  ->  a  < b  < _Γ -|s|- _Δ
popL2 f = popL (popL . f)

popR2
  :: Contextual r s
  => (r •a -> r •b -> _Γ -|s|- _Δ)
  -- ------------------------------------
  ->                  _Γ -|s|- _Δ > b > a
popR2 f = popR (popR . f)


pushL2
  :: Contextual r s
  => a < b < _Γ -|s|- _Δ   ->   a   ->   b
  -- -------------------------------------
  ->         _Γ -|s|- _Δ
pushL2 p = pushL . pushL p

pushR2
  :: Contextual r s
  => _Γ -|s|- _Δ > b > a   ->   r •a   ->   r •b
  -- -------------------------------------------
  -> _Γ -|s|- _Δ
pushR2 p = pushR . pushR p


mapL
  :: Contextual r s
  => (a' -> a)
  -> a  < _Γ -|s|- _Δ
  -- ----------------
  -> a' < _Γ -|s|- _Δ
mapL f p = popL (pushL p . f)

mapR
  :: Contextual r s
  => (a -> a')
  -> _Γ -|s|- _Δ > a
  -- ----------------
  -> _Γ -|s|- _Δ > a'
mapR f p = popR (pushR p . contramap f)


-- FIXME: this is clearly possible, tho it’s less clear that it’s a good idea.
-- mapL2
--  :: (c -> (b, a)) -> a < _Γ -|s|- _Δ -> b < _Γ -|s|- _Δ
--  -- ---------------------------------------------------
--  ->                  c < _Γ -|s|- _Δ
-- mapL2 f a b = popL (pushL b . exl . f) <> popL (pushL a . exr . f)

mapR2
  :: Contextual r s
  => (a -> b -> c) -> _Γ -|s|- _Δ > a   ->   _Γ -|s|- _Δ > b
  -- -------------------------------------------------------
  ->                     _Γ -|s|- _Δ > c
mapR2 f a b = mapR f (wkR' a) >>> popL (`mapR` b)
  where wkR' = popR2 . flip . const . pushR


liftL
  :: Contextual r s
  => r •a
  -- ---------------
  -> a < _Γ -|s|- _Δ
liftL = pushR init

liftR
  :: Contextual r s
  => a
  -- ---------------
  -> _Γ -|s|- _Δ > a
liftR = pushL init


lowerL
  :: Contextual r s
  => (r •a            -> _Γ -|s|- _Δ)
  -- --------------------------------
  -> (a < _Γ -|s|- _Δ -> _Γ -|s|- _Δ)
lowerL k p = popR k >>> p

lowerR
  :: Contextual r s
  => (a               -> _Γ -|s|- _Δ)
  -- --------------------------------
  -> (_Γ -|s|- _Δ > a -> _Γ -|s|- _Δ)
lowerR k p = p >>> popL k


newtype Contextually s r _Γ _Δ = Contextually { getContextually :: _Γ -|s|- _Δ }
  deriving (Core)

instance Contextual r s => Weaken (Contextually s r) where
  wkL = Contextually . popL . const . getContextually
  wkR = Contextually . popR . const . getContextually

instance Contextual r s => Contract (Contextually s r) where
  cnL = Contextually . popL . join . pushL2 . getContextually
  cnR = Contextually . popR . join . pushR2 . getContextually

instance Contextual r s => Exchange (Contextually s r) where
  exL = Contextually . popL2 . flip . pushL2 . getContextually
  exR = Contextually . popR2 . flip . pushR2 . getContextually
