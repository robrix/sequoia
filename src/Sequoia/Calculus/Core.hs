{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
module Sequoia.Calculus.Core
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
, swapΓ
, swapΔ
, popΓΔ
, popΓ
, popΔ
, popL
, popR
, pushL
, pushR
, pushΓΔ
, pushΓ
, pushΔ
, poppedL
, poppedR
, poppedL2
, poppedR2
, popL2
, popR2
, pushL2
, pushR2
, mapΓΔ
, mapΓ
, mapΔ
, mapL
, mapR
, mapL2
, mapR2
, liftL
, liftR
, lowerL
, lowerR
, Contextually(..)
) where

import Control.Monad (join)
import Data.Bifunctor
import Data.Profunctor
import Prelude hiding (init)
import Sequoia.Calculus.Context
import Sequoia.Conjunction
import Sequoia.Continuation as K
import Sequoia.Disjunction
import Sequoia.Functor.K

class Core r e s | s -> r e where
  {-# MINIMAL ((>>>) | (<<<)), init #-}

  (>>>)
    :: _Γ -|s|- _Δ > a   ->   a < _Γ -|s|- _Δ
    -- --------------------------------------
    ->             _Γ -|s|- _Δ
  (>>>) = flip (<<<)

  (<<<)
    :: a < _Γ -|s|- _Δ   ->   _Γ -|s|- _Δ > a
    -- --------------------------------------
    ->             _Γ -|s|- _Δ
  (<<<) = flip (>>>)

  infixr 1 >>>, <<<

  init
    -- -------------------
    :: a < _Γ -|s|- _Δ > a


-- Structural

type Structural r e s = (Weaken r e s, Contract r e s, Exchange r e s)


class Core r e s => Weaken r e s where
  wkL
    ::     _Γ -|s|- _Δ
    -- ---------------
    -> a < _Γ -|s|- _Δ

  wkR
    :: _Γ -|s|- _Δ
    -- ---------------
    -> _Γ -|s|- _Δ > a


wkL'
  :: (Weaken r e s, Exchange r e s)
  => a     < _Γ -|s|- _Δ
  -- -------------------
  -> a < b < _Γ -|s|- _Δ
wkL' = exL . wkL

wkR'
  :: (Weaken r e s, Exchange r e s)
  => _Γ -|s|- _Δ > a
  -- -------------------
  -> _Γ -|s|- _Δ > b > a
wkR' = exR . wkR


class Core r e s => Contract r e s where
  cnL
    :: a < a < _Γ -|s|- _Δ
    -- -------------------
    ->     a < _Γ -|s|- _Δ

  cnR
    :: _Γ -|s|- _Δ > a > a
    -- -------------------
    -> _Γ -|s|- _Δ > a


class Core r e s => Exchange r e s where
  exL
    :: a < b < _Γ -|s|- _Δ
    -- -------------------
    -> b < a < _Γ -|s|- _Δ

  exR
    :: _Γ -|s|- _Δ > a > b
    -- -------------------
    -> _Γ -|s|- _Δ > b > a


class Core r e s => Contextual r e s where
  swapΓΔ
    :: (K r _Δ  -> _Γ  -> _Γ' -|s|- _Δ')
    -> (K r _Δ' -> _Γ' -> _Γ  -|s|- _Δ)


swapΓ
  :: Contextual r e s
  => (_Γ  -> _Γ' -|s|- _Δ)
  -> (_Γ' -> _Γ  -|s|- _Δ)
swapΓ f _Γ' = popΓΔ (\ _Δ _Γ -> pushΓΔ (f _Γ) _Δ _Γ')

swapΔ
  :: Contextual r e s
  => (K r _Δ  -> _Γ -|s|- _Δ')
  -> (K r _Δ' -> _Γ -|s|- _Δ)
swapΔ f _Δ' = popΓΔ (\ _Δ -> pushΓΔ (f _Δ) _Δ')


popΓΔ
  :: Contextual r e s
  => (K r _Δ -> _Γ -> Γ -|s|- r)
  -- ---------------------------
  ->                 _Γ -|s|- _Δ
popΓΔ f = swapΓΔ f idK Γ

-- | Pop something off the input context which can later be pushed. Used with 'pushΓ', this provides a generalized context restructuring facility.
--
-- @
-- popΓ . pushΓ = id
-- @
-- @
-- pushΓ . popΓ = id
-- @
popΓ
  :: Contextual r e s
  => (_Γ -> Γ -|s|- _Δ)
  -- ------------------
  ->  _Γ      -|s|- _Δ
popΓ f = swapΓ f Γ

-- | Pop something off the output context which can later be pushed. Used with 'pushΔ', this provides a generalized context restructuring facility.
--
-- @
-- popΔ . pushΔ = id
-- @
-- @
-- pushΔ . popΔ = id
-- @
popΔ
  :: Contextual r e s
  => (K r _Δ -> _Γ -|s|- r)
  -- ----------------------
  ->            _Γ -|s|- _Δ
popΔ f = swapΔ f idK


-- | Pop something off the input context which can later be pushed. Used with 'pushL', this provides a generalized context restructuring facility.
--
-- @
-- popL . pushL = id
-- @
-- @
-- pushL . popL = id
-- @
popL
  :: Contextual r e s
  => (a -> _Γ -|s|- _Δ)
  -- ------------------
  ->  a  < _Γ -|s|- _Δ
popL f = popΓ (\ c -> pushΓ (f (exl c)) (exr c))

-- | Pop something off the output context which can later be pushed. Used with 'pushR', this provides a generalized context restructuring facility.
--
-- @
-- popR . pushR = id
-- @
-- @
-- pushR . popR = id
-- @
popR
  :: Contextual r e s
  => (K r a -> _Γ -|s|- _Δ)
  -- -------------------------
  ->           _Γ -|s|- _Δ > a
popR f = popΔ (\ c -> pushΔ (f (inrK c)) (inlK c))


pushΓΔ
  :: Contextual r e s
  =>                 _Γ -|s|- _Δ
  -- ---------------------------
  -> (K r _Δ -> _Γ -> Γ -|s|- r)
pushΓΔ = swapΓΔ . const . const

-- | Push something onto the input context which was previously popped off it. Used with 'popΓ', this provides a generalized context restructuring facility. It is undefined what will happen if you push something which was not previously popped.
--
-- @
-- popΓ . pushΓ = id
-- @
-- @
-- pushΓ . popΓ = id
-- @
pushΓ
  :: Contextual r e s
  =>  _Γ      -|s|- _Δ
  -- ------------------
  -> (_Γ -> Γ -|s|- _Δ)
pushΓ = swapΓ . const

-- | Push something onto the output context which was previously popped off it. Used with 'popΔ', this provides a generalized context restructuring facility. It is undefined what will happen if you push something which was not previously popped.
--
-- @
-- popΔ . pushΔ = id
-- @
-- @
-- pushΔ . popΔ = id
-- @
pushΔ
  :: Contextual r e s
  =>            _Γ -|s|- _Δ
  -- -----------------------
  -> (K r _Δ -> _Γ -|s|-  r)
pushΔ = swapΔ . const


-- | Push something onto the input context which was previously popped off it. Used with 'popL', this provides a generalized context restructuring facility. It is undefined what will happen if you push something which was not previously popped.
--
-- @
-- popL . pushL = id
-- @
-- @
-- pushL . popL = id
-- @
pushL
  :: Contextual r e s
  =>  a  < _Γ -|s|- _Δ
  -- ------------------
  -> (a -> _Γ -|s|- _Δ)
pushL s a = popΓ (\ c -> pushΓ s (a `inlr` c))

-- | Push something onto the output context which was previously popped off it. Used with 'popR', this provides a generalized context restructuring facility. It is undefined what will happen if you push something which was not previously popped.
--
-- @
-- popR . pushR = id
-- @
-- @
-- pushR . popR = id
-- @
pushR
  :: Contextual r e s
  =>           _Γ -|s|- _Δ > a
  -- -------------------------
  -> (K r a -> _Γ -|s|- _Δ)
pushR s a = popΔ (\ c -> pushΔ s (c |> a))


poppedL
  :: Contextual r e s
  => (    _Γ -|s|- _Δ ->     _Γ' -|s|- _Δ')
  -- --------------------------------------
  -> (a < _Γ -|s|- _Δ -> a < _Γ' -|s|- _Δ')
poppedL f p = popL (f . pushL p)

poppedR
  :: Contextual r e s
  => (_Γ -|s|- _Δ     -> _Γ' -|s|- _Δ')
  -- --------------------------------------
  -> (_Γ -|s|- _Δ > a -> _Γ' -|s|- _Δ' > a)
poppedR f p = popR (f . pushR p)

poppedL2
  :: Contextual r e s
  =>         (_Γ -|s|- _Δ ->         _Γ' -|s|- _Δ')
  -- ----------------------------------------------
  -> (a < b < _Γ -|s|- _Δ -> a < b < _Γ' -|s|- _Δ')
poppedL2 = poppedL . poppedL

poppedR2
  :: Contextual r e s
  => (_Γ -|s|- _Δ         -> _Γ' -|s|- _Δ')
  -- ----------------------------------------------
  -> (_Γ -|s|- _Δ > a > b -> _Γ' -|s|- _Δ' > a > b)
poppedR2 = poppedR . poppedR


popL2
  :: Contextual r e s
  => (a -> b -> _Γ -|s|- _Δ)
  -- -----------------------
  ->  a  < b  < _Γ -|s|- _Δ
popL2 f = popL (popL . f)

popR2
  :: Contextual r e s
  => (K r a -> K r b -> _Γ -|s|- _Δ)
  -- --------------------------------------
  ->                    _Γ -|s|- _Δ > b > a
popR2 f = popR (popR . f)


pushL2
  :: Contextual r e s
  => a < b < _Γ -|s|- _Δ -> a -> b
  -- -----------------------------
  ->         _Γ -|s|- _Δ
pushL2 p = pushL . pushL p

pushR2
  :: Contextual r e s
  => _Γ -|s|- _Δ > b > a -> K r a -> K r b
  -- -------------------------------------
  -> _Γ -|s|- _Δ
pushR2 p = pushR . pushR p


mapΓΔ
  :: Contextual r e s
  => (_Γ' -> _Γ)
  -> (_Δ -> _Δ')
  -> _Γ  -|s|- _Δ
  -- -------------
  -> _Γ' -|s|- _Δ'
mapΓΔ f g p = popΓΔ (\ _Δ _Γ -> pushΓΔ p (_Δ •<< g) (f _Γ))

mapΓ
  :: Contextual r e s
  => (_Γ' -> _Γ)
  -> _Γ  -|s|- _Δ
  -- ------------
  -> _Γ' -|s|- _Δ
mapΓ = (`mapΓΔ` id)

mapΔ
  :: Contextual r e s
  => (_Δ -> _Δ')
  -> _Γ -|s|- _Δ
  -- ------------
  -> _Γ -|s|- _Δ'
mapΔ = (id `mapΓΔ`)


mapL
  :: Contextual r e s
  => (a' -> a)
  -> a  < _Γ -|s|- _Δ
  -- ----------------
  -> a' < _Γ -|s|- _Δ
mapL f = mapΓ (first f)

mapR
  :: Contextual r e s
  => (a -> a')
  -> _Γ -|s|- _Δ > a
  -- ----------------
  -> _Γ -|s|- _Δ > a'
mapR f = mapΔ (fmap f)


mapL2
 :: Contextual r e s
 => (c -> Either b a)
 -> a < _Γ -|s|- _Δ   ->   b < _Γ -|s|- _Δ
 -- --------------------------------------
 ->            c < _Γ -|s|- _Δ
mapL2 f a b = popL ((pushL b <--> pushL a) . f)

mapR2
  :: Contextual r e s
  => (a -> b -> c)
  -> _Γ -|s|- _Δ > a   ->   _Γ -|s|- _Δ > b
  -- --------------------------------------
  ->            _Γ -|s|- _Δ > c
mapR2 f a b = mapR f (wkR' a) >>> popL (`mapR` b)
  where wkR' = popR2 . flip . const . pushR


liftL
  :: Contextual r e s
  => K r a
  -- ---------------
  -> a < _Γ -|s|- _Δ
liftL = pushR init

liftR
  :: Contextual r e s
  => a
  -- ---------------
  -> _Γ -|s|- _Δ > a
liftR = pushL init


lowerL
  :: Contextual r e s
  => (K r a           -> _Γ -|s|- _Δ)
  -- --------------------------------
  -> (a < _Γ -|s|- _Δ -> _Γ -|s|- _Δ)
lowerL k p = popR k >>> p

lowerR
  :: Contextual r e s
  => (a               -> _Γ -|s|- _Δ)
  -- --------------------------------
  -> (_Γ -|s|- _Δ > a -> _Γ -|s|- _Δ)
lowerR k p = p >>> popL k


newtype Contextually s _Γ _Δ = Contextually { getContextually :: _Γ -|s|- _Δ }
  deriving (Core r e)

instance Contextual r e s => Weaken r e (Contextually s) where
  wkL = Contextually . popL . const . getContextually
  wkR = Contextually . popR . const . getContextually

instance Contextual r e s => Contract r e (Contextually s) where
  cnL = Contextually . popL . join . pushL2 . getContextually
  cnR = Contextually . popR . join . pushR2 . getContextually

instance Contextual r e s => Exchange r e (Contextually s) where
  exL = Contextually . popL2 . flip . pushL2 . getContextually
  exR = Contextually . popR2 . flip . pushR2 . getContextually

instance Contextual r e s => Profunctor (Contextually s) where
  dimap f g (Contextually p) = Contextually (mapΓΔ f g p)
