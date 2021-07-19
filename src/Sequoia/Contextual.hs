{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}
module Sequoia.Contextual
( -- * Contextual
  Contextual(..)
  -- ** Swapping
, swapΓ
, swapΔ
  -- ** Popping
, popΓΔ
, popΓ
, popΔ
, popΓL
, popΔR
, popL
, popR
  -- ** Pushing
, pushL
, pushR
, pushΓΔ
, pushΓ
, pushΔ
, pushΓL
, pushΔR
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
, mapΓL
, mapΔR
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
import Sequoia.Calculus.Core
import Sequoia.Calculus.Structural
import Sequoia.Conjunction
import Sequoia.Continuation as K
import Sequoia.Disjunction
import Sequoia.Functor.K
import Sequoia.Functor.V
import Sequoia.Value

-- Contextual

class (Core s, Env2 s, forall e r . Profunctor (s e r)) => Contextual s where
  swapΓΔ
    :: (V e _Γ  -> K r _Δ  -> _Γ' -|s e r|- _Δ')
    -> (V e _Γ' -> K r _Δ' -> _Γ  -|s e r|- _Δ)


-- Swapping

swapΓ
  :: Contextual s
  => (V e _Γ  -> _Γ' -|s e r|- _Δ)
  -> (V e _Γ' -> _Γ  -|s e r|- _Δ)
swapΓ f _Γ' = popΓΔ (\ _Γ _Δ -> pushΓΔ (f _Γ) _Γ' _Δ)

swapΔ
  :: Contextual s
  => (K r _Δ  -> _Γ -|s e r|- _Δ')
  -> (K r _Δ' -> _Γ -|s e r|- _Δ)
swapΔ f _Δ' = popΓΔ (\ _Γ _Δ -> pushΓΔ (f _Δ) _Γ _Δ')


-- Popping

popΓΔ
  :: Contextual s
  => (V e _Γ -> K r _Δ -> e -|s e r|- r)
  -- -----------------------------------
  ->                     _Γ -|s e r|- _Δ
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
  :: Contextual s
  => (V e _Γ -> e -|s e r|- _Δ)
  -- --------------------------
  ->      _Γ      -|s e r|- _Δ
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
  :: Contextual s
  => (K r _Δ -> _Γ -|s e r|- r)
  -- --------------------------
  ->            _Γ -|s e r|- _Δ
popΔ f = swapΔ f idK


-- | Pop something off the input context which can later be pushed. Used with 'pushΓL', this provides a generalized context restructuring facility.
--
-- @
-- popΓL . pushΓL = id
-- @
-- @
-- pushΓL . popΓL = id
-- @
popΓL
  :: Contextual s
  => (V e a -> _Γ -|s e r|- _Δ)
  -- --------------------------
  ->      a  < _Γ -|s e r|- _Δ
popΓL f = popΓ (pushΓ . f . exlF <*> exrF)

-- | Pop something off the output context which can later be pushed. Used with 'pushΔR', this provides a generalized context restructuring facility.
--
-- @
-- popΔR . pushΔR = id
-- @
-- @
-- pushΔR . popΔR = id
-- @
popΔR
  :: Contextual s
  => (K r a -> _Γ -|s e r|- _Δ)
  -- -----------------------------
  ->           _Γ -|s e r|- _Δ > a
popΔR f = popΔ (pushΔ . f . inrK <*> inlK)


-- | Pop something off the input context which can later be pushed. Used with 'pushL', this provides a generalized context restructuring facility.
--
-- @
-- popL . pushL = id
-- @
-- @
-- pushL . popL = id
-- @
popL
  :: Contextual s
  => (a -> _Γ -|s e r|- _Δ)
  -- ----------------------
  ->  a  < _Γ -|s e r|- _Δ
popL = popΓL . val2

-- | Pop something off the output context which can later be pushed. Used with 'pushR', this provides a generalized context restructuring facility.
--
-- @
-- popR . pushR = id
-- @
-- @
-- pushR . popR = id
-- @
popR
  :: Contextual s
  => (K r a -> _Γ -|s e r|- _Δ)
  -- -----------------------------
  ->           _Γ -|s e r|- _Δ > a
popR = popΔR


popL2
  :: Contextual s
  => (a -> b -> _Γ -|s e r|- _Δ)
  -- ---------------------------
  ->  a  < b  < _Γ -|s e r|- _Δ
popL2 f = popL (popL . f)

popR2
  :: Contextual s
  => (K r a -> K r b -> _Γ -|s e r|- _Δ)
  -- ------------------------------------------
  ->                    _Γ -|s e r|- _Δ > b > a
popR2 f = popR (popR . f)


poppedL
  :: Contextual s
  => (    _Γ -|s e r|- _Δ ->     _Γ' -|s e r|- _Δ')
  -- ----------------------------------------------
  -> (a < _Γ -|s e r|- _Δ -> a < _Γ' -|s e r|- _Δ')
poppedL f p = popL (f . pushL p)

poppedR
  :: Contextual s
  => (_Γ -|s e r|- _Δ     -> _Γ' -|s e r|- _Δ')
  -- ----------------------------------------------
  -> (_Γ -|s e r|- _Δ > a -> _Γ' -|s e r|- _Δ' > a)
poppedR f p = popR (f . pushR p)

poppedL2
  :: Contextual s
  =>         (_Γ -|s e r|- _Δ ->         _Γ' -|s e r|- _Δ')
  -- ------------------------------------------------------
  -> (a < b < _Γ -|s e r|- _Δ -> a < b < _Γ' -|s e r|- _Δ')
poppedL2 = poppedL . poppedL

poppedR2
  :: Contextual s
  => (_Γ -|s e r|- _Δ         -> _Γ' -|s e r|- _Δ')
  -- ------------------------------------------------------
  -> (_Γ -|s e r|- _Δ > a > b -> _Γ' -|s e r|- _Δ' > a > b)
poppedR2 = poppedR . poppedR


-- Pushing

pushΓΔ
  :: Contextual s
  =>                     _Γ -|s e r|- _Δ
  -- -----------------------------------
  -> (V e _Γ -> K r _Δ -> e -|s e r|- r)
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
  :: Contextual s
  =>      _Γ      -|s e r|- _Δ
  -- --------------------------
  -> (V e _Γ -> e -|s e r|- _Δ)
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
  :: Contextual s
  =>            _Γ -|s e r|- _Δ
  -- ---------------------------
  -> (K r _Δ -> _Γ -|s e r|-  r)
pushΔ = swapΔ . const


-- | Push something onto the input context which was previously popped off it. Used with 'popΓL', this provides a generalized context restructuring facility. It is undefined what will happen if you push something which was not previously popped.
--
-- @
-- popΓL . pushΓL = id
-- @
-- @
-- pushΓL . popΓL = id
-- @
pushΓL
  :: Contextual s
  =>      a  < _Γ -|s e r|- _Δ
  -- --------------------------
  -> (V e a -> _Γ -|s e r|- _Δ)
pushΓL s a = popΓ (pushΓ s . (a <|))

-- | Push something onto the output context which was previously popped off it. Used with 'popΔR', this provides a generalized context restructuring facility. It is undefined what will happen if you push something which was not previously popped.
--
-- @
-- popΔR . pushΔR = id
-- @
-- @
-- pushΔR . popΔR = id
-- @
pushΔR
  :: Contextual s
  =>           _Γ -|s e r|- _Δ > a
  -- -----------------------------
  -> (K r a -> _Γ -|s e r|- _Δ)
pushΔR s a = popΔ (\ c -> pushΔ s (c |> a))


-- | Push something onto the input context which was previously popped off it. Used with 'popL', this provides a generalized context restructuring facility. It is undefined what will happen if you push something which was not previously popped.
--
-- @
-- popL . pushL = id
-- @
-- @
-- pushL . popL = id
-- @
pushL
  :: Contextual s
  =>  a  < _Γ -|s e r|- _Δ
  -- ----------------------
  -> (a -> _Γ -|s e r|- _Δ)
pushL s = pushΓL s . inV0

-- | Push something onto the output context which was previously popped off it. Used with 'popR', this provides a generalized context restructuring facility. It is undefined what will happen if you push something which was not previously popped.
--
-- @
-- popR . pushR = id
-- @
-- @
-- pushR . popR = id
-- @
pushR
  :: Contextual s
  =>           _Γ -|s e r|- _Δ > a
  -- -----------------------------
  -> (K r a -> _Γ -|s e r|- _Δ)
pushR = pushΔR


pushL2
  :: Contextual s
  => a < b < _Γ -|s e r|- _Δ -> a -> b
  -- ---------------------------------
  ->         _Γ -|s e r|- _Δ
pushL2 p = pushL . pushL p

pushR2
  :: Contextual s
  => _Γ -|s e r|- _Δ > b > a -> K r a -> K r b
  -- -----------------------------------------
  -> _Γ -|s e r|- _Δ
pushR2 p = pushR . pushR p


-- Mapping

mapΓΔ
  :: Contextual s
  => (V e _Γ' -> V e _Γ)
  -> (K r _Δ' -> K r _Δ)
  -> _Γ  -|s e r|- _Δ
  -- -----------------
  -> _Γ' -|s e r|- _Δ'
mapΓΔ f g p = popΓΔ (\ _Γ _Δ -> pushΓΔ p (f _Γ) (g _Δ))

mapΓ
  :: Contextual s
  => (V e _Γ' -> V e _Γ)
  -> _Γ  -|s e r|- _Δ
  -- ----------------
  -> _Γ' -|s e r|- _Δ
mapΓ = (`mapΓΔ` id)

mapΔ
  :: Contextual s
  => (K r _Δ' -> K r _Δ)
  -> _Γ -|s e r|- _Δ
  -- ----------------
  -> _Γ -|s e r|- _Δ'
mapΔ = (id `mapΓΔ`)


mapΓL
  :: Contextual s
  => (V e a' -> V e a)
  -> a  < _Γ -|s e r|- _Δ
  -- --------------------
  -> a' < _Γ -|s e r|- _Δ
mapΓL f = mapΓ (f . exlF >∘∘∘< exrF)

mapΔR
  :: Contextual s
  => (K r a' -> K r a)
  -> _Γ -|s e r|- _Δ > a
  -- --------------------
  -> _Γ -|s e r|- _Δ > a'
mapΔR f = mapΔ (inlK <•••> f . inrK)


mapL
  :: Profunctor p
  => (a' -> a)
  -> a  < _Γ -|p|- _Δ
  -- ----------------
  -> a' < _Γ -|p|- _Δ
mapL = lmap . firstConj

mapR
  :: Profunctor p
  => (a -> a')
  -> _Γ -|p|- _Δ > a
  -- ----------------
  -> _Γ -|p|- _Δ > a'
mapR = rmap . fmap


mapL2
 :: Contextual s
 => (c -> Either b a)
 -> a < _Γ -|s e r|- _Δ   ->   b < _Γ -|s e r|- _Δ
 -- ----------------------------------------------
 ->            c < _Γ -|s e r|- _Δ
mapL2 f a b = popL ((pushL b <--> pushL a) . f)

mapR2
  :: Contextual s
  => (a -> b -> c)
  -> _Γ -|s e r|- _Δ > a   ->   _Γ -|s e r|- _Δ > b
  -- ----------------------------------------------
  ->            _Γ -|s e r|- _Δ > c
mapR2 f a b = mapR f (wkR' a) >>> popL (`mapR` b)
  where wkR' = popR2 . flip . const . pushR


-- Lifting

liftL
  :: Contextual s
  => K r a
  -- -----------------------
  ->     a < _Γ -|s e r|- _Δ
liftL = pushR init

liftR
  :: Contextual s
  =>               V e a
  -- -------------------
  -> _Γ -|s e r|- _Δ > a
liftR v = popΓ (\ _Γ -> pushΓ init (v <| _Γ))


-- Lowering

lowerL
  :: Contextual s
  => (K r a                   -> _Γ -|s e r|- _Δ)
  -- --------------------------------------------
  -> (    a < _Γ -|s e r|- _Δ -> _Γ -|s e r|- _Δ)
lowerL k p = popR k >>> p

lowerR
  :: Contextual s
  => (              V e a -> _Γ -|s e r|- _Δ)
  -- ----------------------------------------
  -> (_Γ -|s e r|- _Δ > a -> _Γ -|s e r|- _Δ)
lowerR k p = p >>> popΓ (\ _Γ -> pushΓ (k (exlF _Γ)) (exrF _Γ))


-- Deriving

newtype Contextually s e r _Γ _Δ = Contextually { getContextually :: _Γ -|s e r|- _Δ }
  deriving Core

instance Contextual s => Weaken (Contextually s) where
  wkL = Contextually . popL . const . getContextually
  wkR = Contextually . popR . const . getContextually

instance Contextual s => Contract (Contextually s) where
  cnL = Contextually . popL . join . pushL2 . getContextually
  cnR = Contextually . popR . join . pushR2 . getContextually

instance Contextual s => Exchange (Contextually s) where
  exL = Contextually . popL2 . flip . pushL2 . getContextually
  exR = Contextually . popR2 . flip . pushR2 . getContextually

instance Contextual s => Profunctor (Contextually s e r) where
  dimap f g (Contextually p) = Contextually (mapΓΔ (fmap f) (contramap g) p)
