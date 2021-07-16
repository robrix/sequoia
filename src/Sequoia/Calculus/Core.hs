{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE QuantifiedConstraints #-}
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
  -- ** Swapping
, swapΓ
, swapΔ
  -- ** Popping
, popΓΔ
, popΓ
, popΔ
, popL
, popR
  -- ** Pushing
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
  -- ** Mapping
, mapΓΔ
, mapΓ
, mapΔ
, mapL
, mapR
, mapL2
, mapR2
  -- ** Lifting
, liftL
, liftR
  -- ** Lowering
, lowerL
, lowerR
  -- ** Deriving
, Contextually(..)
) where

import Control.Monad (join)
import Data.Profunctor
import Prelude hiding (init)
import Sequoia.Calculus.Context
import Sequoia.Conjunction
import Sequoia.Continuation as K
import Sequoia.Disjunction
import Sequoia.Functor.K
import Sequoia.Functor.V
import Sequoia.Value

-- Core

class Core e r s | s -> e r where
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

type Structural e r s = (Weaken e r s, Contract e r s, Exchange e r s)


class Core e r s => Weaken e r s where
  wkL
    ::     _Γ -|s|- _Δ
    -- ---------------
    -> a < _Γ -|s|- _Δ

  wkR
    :: _Γ -|s|- _Δ
    -- ---------------
    -> _Γ -|s|- _Δ > a


wkL'
  :: (Weaken e r s, Exchange e r s)
  => a     < _Γ -|s|- _Δ
  -- -------------------
  -> a < b < _Γ -|s|- _Δ
wkL' = exL . wkL

wkR'
  :: (Weaken e r s, Exchange e r s)
  => _Γ -|s|- _Δ > a
  -- -------------------
  -> _Γ -|s|- _Δ > b > a
wkR' = exR . wkR


class Core e r s => Contract e r s where
  cnL
    :: a < a < _Γ -|s|- _Δ
    -- -------------------
    ->     a < _Γ -|s|- _Δ

  cnR
    :: _Γ -|s|- _Δ > a > a
    -- -------------------
    -> _Γ -|s|- _Δ > a


class Core e r s => Exchange e r s where
  exL
    :: a < b < _Γ -|s|- _Δ
    -- -------------------
    -> b < a < _Γ -|s|- _Δ

  exR
    :: _Γ -|s|- _Δ > a > b
    -- -------------------
    -> _Γ -|s|- _Δ > b > a


-- Contextual

class (Core e r s, forall a b . Env e (s a b)) => Contextual e r s where
  swapΓΔ
    :: (V e _Γ  -> K r _Δ  -> _Γ' -|s|- _Δ')
    -> (V e _Γ' -> K r _Δ' -> _Γ  -|s|- _Δ)


-- Swapping

swapΓ
  :: Contextual e r s
  => (V e _Γ  -> _Γ' -|s|- _Δ)
  -> (V e _Γ' -> _Γ  -|s|- _Δ)
swapΓ f _Γ' = popΓΔ (\ _Γ _Δ -> pushΓΔ (f _Γ) _Γ' _Δ)

swapΔ
  :: Contextual e r s
  => (K r _Δ  -> _Γ -|s|- _Δ')
  -> (K r _Δ' -> _Γ -|s|- _Δ)
swapΔ f _Δ' = popΓΔ (\ _Γ _Δ -> pushΓΔ (f _Δ) _Γ _Δ')


-- Popping

popΓΔ
  :: Contextual e r s
  => (V e _Γ -> K r _Δ -> e -|s|- r)
  -- -------------------------------
  ->                     _Γ -|s|- _Δ
popΓΔ f = swapΓΔ f idV idK

-- | Pop something off the input context which can later be pushed. Used with 'pushΓ', this provides a generalized context restructuring facility.
--
-- @
-- popΓ . pushΓ = id
-- @
-- @
-- pushΓ . popΓ = id
-- @
popΓ
  :: Contextual e r s
  => (V e _Γ -> e -|s|- _Δ)
  -- ----------------------
  ->      _Γ      -|s|- _Δ
popΓ f = swapΓ f idV

-- | Pop something off the output context which can later be pushed. Used with 'pushΔ', this provides a generalized context restructuring facility.
--
-- @
-- popΔ . pushΔ = id
-- @
-- @
-- pushΔ . popΔ = id
-- @
popΔ
  :: Contextual e r s
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
  :: Contextual e r s
  => (a -> _Γ -|s|- _Δ)
  -- ------------------
  ->  a  < _Γ -|s|- _Δ
popL f = popΓ (\ c -> val (\ a -> pushΓ (f a) (exrF c)) (exlF c))

-- | Pop something off the output context which can later be pushed. Used with 'pushR', this provides a generalized context restructuring facility.
--
-- @
-- popR . pushR = id
-- @
-- @
-- pushR . popR = id
-- @
popR
  :: Contextual e r s
  => (K r a -> _Γ -|s|- _Δ)
  -- -------------------------
  ->           _Γ -|s|- _Δ > a
popR f = popΔ (\ c -> pushΔ (f (inrK c)) (inlK c))


popL2
  :: Contextual e r s
  => (a -> b -> _Γ -|s|- _Δ)
  -- -----------------------
  ->  a  < b  < _Γ -|s|- _Δ
popL2 f = popL (popL . f)

popR2
  :: Contextual e r s
  => (K r a -> K r b -> _Γ -|s|- _Δ)
  -- --------------------------------------
  ->                    _Γ -|s|- _Δ > b > a
popR2 f = popR (popR . f)


poppedL
  :: Contextual e r s
  => (    _Γ -|s|- _Δ ->     _Γ' -|s|- _Δ')
  -- --------------------------------------
  -> (a < _Γ -|s|- _Δ -> a < _Γ' -|s|- _Δ')
poppedL f p = popL (f . pushL p)

poppedR
  :: Contextual e r s
  => (_Γ -|s|- _Δ     -> _Γ' -|s|- _Δ')
  -- --------------------------------------
  -> (_Γ -|s|- _Δ > a -> _Γ' -|s|- _Δ' > a)
poppedR f p = popR (f . pushR p)

poppedL2
  :: Contextual e r s
  =>         (_Γ -|s|- _Δ ->         _Γ' -|s|- _Δ')
  -- ----------------------------------------------
  -> (a < b < _Γ -|s|- _Δ -> a < b < _Γ' -|s|- _Δ')
poppedL2 = poppedL . poppedL

poppedR2
  :: Contextual e r s
  => (_Γ -|s|- _Δ         -> _Γ' -|s|- _Δ')
  -- ----------------------------------------------
  -> (_Γ -|s|- _Δ > a > b -> _Γ' -|s|- _Δ' > a > b)
poppedR2 = poppedR . poppedR


-- Pushing

pushΓΔ
  :: Contextual e r s
  =>                     _Γ -|s|- _Δ
  -- -------------------------------
  -> (V e _Γ -> K r _Δ -> e -|s|- r)
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
  :: Contextual e r s
  =>      _Γ      -|s|- _Δ
  -- ----------------------
  -> (V e _Γ -> e -|s|- _Δ)
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
  :: Contextual e r s
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
  :: Contextual e r s
  =>  a  < _Γ -|s|- _Δ
  -- ------------------
  -> (a -> _Γ -|s|- _Δ)
pushL s a = popΓ (\ c -> pushΓ s (inV0 a <| c))

-- | Push something onto the output context which was previously popped off it. Used with 'popR', this provides a generalized context restructuring facility. It is undefined what will happen if you push something which was not previously popped.
--
-- @
-- popR . pushR = id
-- @
-- @
-- pushR . popR = id
-- @
pushR
  :: Contextual e r s
  =>           _Γ -|s|- _Δ > a
  -- -------------------------
  -> (K r a -> _Γ -|s|- _Δ)
pushR s a = popΔ (\ c -> pushΔ s (c |> a))


pushL2
  :: Contextual e r s
  => a < b < _Γ -|s|- _Δ -> a -> b
  -- -----------------------------
  ->         _Γ -|s|- _Δ
pushL2 p = pushL . pushL p

pushR2
  :: Contextual e r s
  => _Γ -|s|- _Δ > b > a -> K r a -> K r b
  -- -------------------------------------
  -> _Γ -|s|- _Δ
pushR2 p = pushR . pushR p


-- Mapping

mapΓΔ
  :: Contextual e r s
  => (V e _Γ' -> V e _Γ)
  -> (K r _Δ' -> K r _Δ)
  -> _Γ  -|s|- _Δ
  -- -------------
  -> _Γ' -|s|- _Δ'
mapΓΔ f g p = popΓΔ (\ _Γ _Δ -> pushΓΔ p (f _Γ) (g _Δ))

mapΓ
  :: Contextual e r s
  => (V e _Γ' -> V e _Γ)
  -> _Γ  -|s|- _Δ
  -- ------------
  -> _Γ' -|s|- _Δ
mapΓ = (`mapΓΔ` id)

mapΔ
  :: Contextual e r s
  => (K r _Δ' -> K r _Δ)
  -> _Γ -|s|- _Δ
  -- ------------
  -> _Γ -|s|- _Δ'
mapΔ = (id `mapΓΔ`)


mapL
  :: Contextual e r s
  => (V e a' -> V e a)
  -> a  < _Γ -|s|- _Δ
  -- ----------------
  -> a' < _Γ -|s|- _Δ
mapL f = mapΓ (f . exlF >∘∘< exrF)

mapR
  :: Contextual e r s
  => (a -> a')
  -> _Γ -|s|- _Δ > a
  -- ----------------
  -> _Γ -|s|- _Δ > a'
mapR f = mapΔ (contramap (fmap f))


mapL2
 :: Contextual e r s
 => (c -> Either b a)
 -> a < _Γ -|s|- _Δ   ->   b < _Γ -|s|- _Δ
 -- --------------------------------------
 ->            c < _Γ -|s|- _Δ
mapL2 f a b = popL ((pushL b <--> pushL a) . f)

mapR2
  :: Contextual e r s
  => (a -> b -> c)
  -> _Γ -|s|- _Δ > a   ->   _Γ -|s|- _Δ > b
  -- --------------------------------------
  ->            _Γ -|s|- _Δ > c
mapR2 f a b = mapR f (wkR' a) >>> popL (`mapR` b)
  where wkR' = popR2 . flip . const . pushR


-- Lifting

liftL
  :: Contextual e r s
  => K r a
  -- ---------------
  -> a < _Γ -|s|- _Δ
liftL = pushR init

liftR
  :: Contextual e r s
  => a
  -- ---------------
  -> _Γ -|s|- _Δ > a
liftR = pushL init


-- Lowering

lowerL
  :: Contextual e r s
  => (K r a           -> _Γ -|s|- _Δ)
  -- --------------------------------
  -> (a < _Γ -|s|- _Δ -> _Γ -|s|- _Δ)
lowerL k p = popR k >>> p

lowerR
  :: Contextual e r s
  => (a               -> _Γ -|s|- _Δ)
  -- --------------------------------
  -> (_Γ -|s|- _Δ > a -> _Γ -|s|- _Δ)
lowerR k p = p >>> popL k


-- Deriving

newtype Contextually s _Γ _Δ = Contextually { getContextually :: _Γ -|s|- _Δ }
  deriving (Core e r)

instance Contextual e r s => Weaken e r (Contextually s) where
  wkL = Contextually . popL . const . getContextually
  wkR = Contextually . popR . const . getContextually

instance Contextual e r s => Contract e r (Contextually s) where
  cnL = Contextually . popL . join . pushL2 . getContextually
  cnR = Contextually . popR . join . pushR2 . getContextually

instance Contextual e r s => Exchange e r (Contextually s) where
  exL = Contextually . popL2 . flip . pushL2 . getContextually
  exR = Contextually . popR2 . flip . pushR2 . getContextually

instance Contextual e r s => Profunctor (Contextually s) where
  dimap f g (Contextually p) = Contextually (mapΓΔ (fmap f) (contramap g) p)
