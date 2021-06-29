{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DefaultSignatures #-}
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
, popL
, popR
, pushL
, pushR
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
import Focalized.Conjunction
import Focalized.Disjunction
import Prelude hiding (init)

class Core s where
  {-# MINIMAL ((>>>) | (<<<)), init #-}

  (>>>)
    :: _Γ -|s r|- _Δ > a   ->   a < _Γ -|s r|- _Δ
    -- ------------------------------------------
    ->              _Γ -|s r|- _Δ
  (>>>) = flip (<<<)

  (<<<)
    :: a < _Γ -|s r|- _Δ   ->   _Γ -|s r|- _Δ > a
    -- ------------------------------------------
    ->              _Γ -|s r|- _Δ
  (<<<) = flip (>>>)

  infixr 1 >>>, <<<

  init
    -- ---------------------
    :: a < _Γ -|s r|- _Δ > a


-- Structural

type Structural s = (Weaken s, Contract s, Exchange s)


class Core s => Weaken s where
  wkL
    ::     _Γ -|s r|- _Δ
    -- -----------------
    -> a < _Γ -|s r|- _Δ

  wkR
    :: _Γ -|s r|- _Δ
    -- -----------------
    -> _Γ -|s r|- _Δ > a


wkL'
  :: (Weaken s, Exchange s)
  => a     < _Γ -|s r|- _Δ
  -- ---------------------
  -> a < b < _Γ -|s r|- _Δ
wkL' = exL . wkL

wkR'
  :: (Weaken s, Exchange s)
  => _Γ -|s r|- _Δ > a
  -- ---------------------
  -> _Γ -|s r|- _Δ > b > a
wkR' = exR . wkR


class Core s => Contract s where
  cnL
    :: a < a < _Γ -|s r|- _Δ
    -- ---------------------
    ->     a < _Γ -|s r|- _Δ

  cnR
    :: _Γ -|s r|- _Δ > a > a
    -- ---------------------
    -> _Γ -|s r|- _Δ > a


class Core s => Exchange s where
  exL
    :: a < b < _Γ -|s r|- _Δ
    -- ---------------------
    -> b < a < _Γ -|s r|- _Δ

  exR
    :: _Γ -|s r|- _Δ > a > b
    -- ---------------------
    -> _Γ -|s r|- _Δ > b > a


class Core s => Contextual s where
  -- | Pop something off the input context which can later be pushed. Used with 'pushLn', this provides a generalized context restructuring facility.
  --
  -- @
  -- popLn . pushLn = id
  -- @
  -- @
  -- pushLn . popLn = id
  -- @
  popLn
    :: (_Γ -> Γ -|s r|- _Δ)
    -- --------------------
    ->  _Γ      -|s r|- _Δ

  -- | Pop something off the output context which can later be pushed. Used with 'pushRn', this provides a generalized context restructuring facility.
  --
  -- @
  -- popRn . pushRn = id
  -- @
  -- @
  -- pushRn . popRn = id
  -- @
  popRn
    :: (r •_Δ -> _Γ -|s r|-  Δ)
    -- ------------------------
    ->           _Γ -|s r|- _Δ


  -- | Push something onto the input context which was previously popped off it. Used with 'popLn', this provides a generalized context restructuring facility. It is undefined what will happen if you push something which was not previously popped.
  --
  -- @
  -- popLn . pushLn = id
  -- @
  -- @
  -- pushLn . popLn = id
  -- @
  pushLn
    ::  _Γ      -|s r|- _Δ
    -- --------------------
    -> (_Γ -> Γ -|s r|- _Δ)

  -- | Push something onto the output context which was previously popped off it. Used with 'popRn', this provides a generalized context restructuring facility. It is undefined what will happen if you push something which was not previously popped.
  --
  -- @
  -- popRn . pushRn = id
  -- @
  -- @
  -- pushRn . popRn = id
  -- @
  pushRn
    ::           _Γ -|s r|- _Δ
    -- ------------------------
    -> (r •_Δ -> _Γ -|s r|-  Δ)


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
  => (a -> _Γ -|s r|- _Δ)
  -- --------------------
  ->  a  < _Γ -|s r|- _Δ
popL f = popLn (\ c -> pushLn (f (exl c)) (exr c))

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
  => (r •a -> _Γ -|s r|- _Δ)
  -- --------------------------
  ->          _Γ -|s r|- _Δ > a
popR f = popRn (\ c -> pushRn (f (contramap inr c)) (contramap inl c))


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
  =>  a  < _Γ -|s r|- _Δ
  -- --------------------
  -> (a -> _Γ -|s r|- _Δ)
pushL s a = popLn (\ c -> pushLn s (a <| c))

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
  =>          _Γ -|s r|- _Δ > a
  -- --------------------------
  -> (r •a -> _Γ -|s r|- _Δ)
pushR s a = popRn (\ c -> pushRn s (c ||> a))


poppedL
  :: Contextual s
  => (_Γ -|s r|- _Δ     ->     _Γ' -|s r|- _Δ')
  -- ------------------------------------------
  -> (a < _Γ -|s r|- _Δ -> a < _Γ' -|s r|- _Δ')
poppedL f p = popL (f . pushL p)

poppedR
  :: Contextual s
  => (_Γ -|s r|- _Δ     -> _Γ' -|s r|- _Δ')
  -- ------------------------------------------
  -> (_Γ -|s r|- _Δ > a -> _Γ' -|s r|- _Δ' > a)
poppedR f p = popR (f . pushR p)


popL2
  :: Contextual s
  => (a -> b -> _Γ -|s r|- _Δ)
  -- -------------------------
  ->  a  < b  < _Γ -|s r|- _Δ
popL2 f = popL (popL . f)

popR2
  :: Contextual s
  => (r •a -> r •b -> _Γ -|s r|- _Δ)
  -- --------------------------------------
  ->                  _Γ -|s r|- _Δ > b > a
popR2 f = popR (popR . f)


pushL2
  :: Contextual s
  => a < b < _Γ -|s r|- _Δ   ->   a   ->   b
  -- ---------------------------------------
  ->         _Γ -|s r|- _Δ
pushL2 p = pushL . pushL p

pushR2
  :: Contextual s
  => _Γ -|s r|- _Δ > b > a   ->   r •a   ->   r •b
  -- -----------------
  -> _Γ -|s r|- _Δ
pushR2 p = pushR . pushR p


mapL
  :: Contextual s
  => (a' -> a)
  -> a  < _Γ -|s r|- _Δ
  -- ------------------
  -> a' < _Γ -|s r|- _Δ
mapL f p = popL (pushL p . f)

mapR
  :: Contextual s
  => (a -> a')
  -> _Γ -|s r|- _Δ > a
  -- ------------------
  -> _Γ -|s r|- _Δ > a'
mapR f p = popR (pushR p . contramap f)


-- FIXME: this is clearly possible, tho it’s less clear that it’s a good idea.
-- mapL2
--  :: (c -> (b, a)) -> a < _Γ -|s r|- _Δ -> b < _Γ -|s r|- _Δ
--  -- -------------------------------------------------------
--  ->                  c < _Γ -|s r|- _Δ
-- mapL2 f a b = popL (pushL b . exl . f) <> popL (pushL a . exr . f)

mapR2
  :: Contextual s
  => (a -> b -> c) -> _Γ -|s r|- _Δ > a   ->   _Γ -|s r|- _Δ > b
  -- -----------------------------------------------------------
  ->                     _Γ -|s r|- _Δ > c
mapR2 f a b = mapR f (wkR' a) >>> popL (`mapR` b)
  where wkR' = popR2 . flip . const . pushR


liftL
  :: Contextual s
  => r •a
  -- -----------------
  -> a < _Γ -|s r|- _Δ
liftL = pushR init

liftR
  :: Contextual s
  => a
  -- -----------------
  -> _Γ -|s r|- _Δ > a
liftR = pushL init


lowerL
  :: Contextual s
  => (r •a              -> _Γ -|s r|- _Δ)
  -- ------------------------------------
  -> (a < _Γ -|s r|- _Δ -> _Γ -|s r|- _Δ)
lowerL k p = popR k >>> p

lowerR
  :: Contextual s
  => (a                 -> _Γ -|s r|- _Δ)
  -- ------------------------------------
  -> (_Γ -|s r|- _Δ > a -> _Γ -|s r|- _Δ)
lowerR k p = p >>> popL k


newtype Contextually s r _Γ _Δ = Contextually { getContextually :: _Γ -|s r|- _Δ }
  deriving (Core)

instance Contextual s => Weaken (Contextually s) where
  wkL = Contextually . popL . const . getContextually
  wkR = Contextually . popR . const . getContextually

instance Contextual s => Contract (Contextually s) where
  cnL = Contextually . popL . join . pushL2 . getContextually
  cnR = Contextually . popR . join . pushR2 . getContextually

instance Contextual s => Exchange (Contextually s) where
  exL = Contextually . popL2 . flip . pushL2 . getContextually
  exR = Contextually . popR2 . flip . pushR2 . getContextually
