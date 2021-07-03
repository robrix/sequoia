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
, swapΓ
, swapΔ
, popΓΔ
, popΓ
, popΔ
, popL
, popR
, popLn
, popRn
, pushL
, pushR
, pushLn
, pushRn
, selectL
, selectR
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
import Data.Functor.Contravariant
import Data.Profunctor
import Focalized.Calculus.Context
import Focalized.Conjunction
import Focalized.Continuation
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
  swapΓΔ
    :: (r •_Δ  -> _Γ  -> _Γ' -|s r|- _Δ')
    -> (r •_Δ' -> _Γ' -> _Γ  -|s r|- _Δ)


swapΓ
  :: Contextual s
  => (_Γ  -> _Γ' -|s r|- _Δ)
  -> (_Γ' -> _Γ  -|s r|- _Δ)
swapΓ f _Γ' = popΓΔ (\ _Δ _Γ -> pushΓΔ (f _Γ) _Δ _Γ')

swapΔ
  :: Contextual s
  => (r •_Δ  -> _Γ -|s r|- _Δ')
  -> (r •_Δ' -> _Γ -|s r|- _Δ)
swapΔ f _Δ' = popΓΔ (\ _Δ -> pushΓΔ (f _Δ) _Δ')


popΓΔ
  :: Contextual s
  => (r •_Δ -> _Γ -> Γ -|s r|-  r)
  -- -----------------------------
  ->                _Γ -|s r|- _Δ
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
  :: Contextual s
  => (_Γ -> Γ -|s r|- _Δ)
  -- --------------------
  ->  _Γ      -|s r|- _Δ
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
  :: Contextual s
  => (r •_Δ -> _Γ -|s r|-  r)
  -- ------------------------
  ->           _Γ -|s r|- _Δ
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
  :: Contextual s
  => (a -> _Γ -|s r|- _Δ)
  -- --------------------
  ->  a  < _Γ -|s r|- _Δ
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
  :: Contextual s
  => (r •a -> _Γ -|s r|- _Δ)
  -- --------------------------
  ->          _Γ -|s r|- _Δ > a
popR f = popΔ (\ c -> pushΔ (f (contramap inr c)) (contramap inl c))


popLn
  :: (Contextual s, MemberΓ n a _Γ _Γ')
  => (n :. a -> _Γ' -|s r|- _Δ)
  -- --------------------------
  ->            _Γ  -|s r|- _Δ
popLn f = popΓ (\ _Γ -> let v@(V (a, _Γ')) = rejectΓ (V _Γ) in pushΓ (f (a <$ v)) _Γ')

popRn
  :: (Contextual s, MemberΔ n a _Δ _Δ')
  => ( n :. r •a -> _Γ -|s r|- _Δ')
  -- ------------------------------
  ->                _Γ -|s r|- _Δ
popRn f = popΔ (\ _Δ -> let v@(V (_Δ', a)) = rejectΔ (V _Δ) in pushΔ (f (a <$ v)) _Δ')


pushΓΔ
  :: Contextual s
  =>                _Γ -|s r|- _Δ
  -- -----------------------------
  -> (r •_Δ -> _Γ -> Γ -|s r|-  r)
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
  =>  _Γ      -|s r|- _Δ
  -- --------------------
  -> (_Γ -> Γ -|s r|- _Δ)
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
  =>           _Γ -|s r|- _Δ
  -- ------------------------
  -> (r •_Δ -> _Γ -|s r|-  r)
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
  :: Contextual s
  =>  a  < _Γ -|s r|- _Δ
  -- --------------------
  -> (a -> _Γ -|s r|- _Δ)
pushL s a = popΓ (\ c -> pushΓ s (a <| c))

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
pushR s a = popΔ (\ c -> pushΔ s (c |> a))


pushLn
  :: (Contextual s, MemberΓ n a _Γ _Γ')
  =>             _Γ -|s r|- _Δ
  -- --------------------------
  -> (n :. a -> _Γ' -|s r|- _Δ)
pushLn s a = popΓ (pushΓ s . getV . injectΓ . (<$> a) . flip (,))

pushRn
  :: (Contextual s, MemberΔ n a _Δ _Δ')
  =>          _Γ -|s r|- _Δ
  -- --------------------------
  -> ( n :. r •a -> _Γ -|s r|- _Δ')
pushRn s a = popΔ (pushΔ s . getV . injectΔ . (<$> a) . (,))


selectL
  :: (Contextual s, ElemL a _Γ _Γ')
  => a < _Γ' -|s r|- _Δ
  -- ------------------
  ->     _Γ  -|s r|- _Δ
selectL s = popΓ (pushΓ s . uncurry (<|) . rejectL)

selectR
  :: (Contextual s, ElemR a _Δ _Δ')
  => _Γ -|s r|- _Δ' > a
  -- ------------------
  -> _Γ -|s r|- _Δ
selectR s = popΔ (pushΔ s . uncurry (|>) . rejectR)


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

poppedL2
  :: Contextual s
  =>         (_Γ -|s r|- _Δ ->         _Γ' -|s r|- _Δ')
  -- --------------------------------------------------
  -> (a < b < _Γ -|s r|- _Δ -> a < b < _Γ' -|s r|- _Δ')
poppedL2 = poppedL . poppedL

poppedR2
  :: Contextual s
  => (_Γ -|s r|- _Δ         -> _Γ' -|s r|- _Δ')
  -- --------------------------------------------------
  -> (_Γ -|s r|- _Δ > a > b -> _Γ' -|s r|- _Δ' > a > b)
poppedR2 = poppedR . poppedR


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
  -- ---------------------------------------------
  -> _Γ -|s r|- _Δ
pushR2 p = pushR . pushR p


mapΓΔ
  :: Contextual s
  => (_Γ' -> _Γ)
  -> (_Δ -> _Δ')
  -> _Γ  -|s r|- _Δ
  -- ---------------
  -> _Γ' -|s r|- _Δ'
mapΓΔ f g p = popΓΔ (\ _Δ _Γ -> pushΓΔ p (_Δ •<< g) (f _Γ))

mapΓ
  :: Contextual s
  => (_Γ' -> _Γ)
  -> _Γ  -|s r|- _Δ
  -- --------------
  -> _Γ' -|s r|- _Δ
mapΓ = (`mapΓΔ` id)

mapΔ
  :: Contextual s
  => (_Δ -> _Δ')
  -> _Γ -|s r|- _Δ
  -- --------------
  -> _Γ -|s r|- _Δ'
mapΔ = (id `mapΓΔ`)


mapL
  :: Contextual s
  => (a' -> a)
  -> a  < _Γ -|s r|- _Δ
  -- ------------------
  -> a' < _Γ -|s r|- _Δ
mapL f = mapΓ (first f)

mapR
  :: Contextual s
  => (a -> a')
  -> _Γ -|s r|- _Δ > a
  -- ------------------
  -> _Γ -|s r|- _Δ > a'
mapR f = mapΔ (fmap f)


mapL2
 :: Contextual s
 => (c -> Either b a)
 -> a < _Γ -|s r|- _Δ   ->   b < _Γ -|s r|- _Δ
 -- ------------------------------------------
 ->             c < _Γ -|s r|- _Δ
mapL2 f a b = popL ((pushL b <--> pushL a) . f)

mapR2
  :: Contextual s
  => (a -> b -> c)
  -> _Γ -|s r|- _Δ > a   ->   _Γ -|s r|- _Δ > b
  -- ------------------------------------------
  ->             _Γ -|s r|- _Δ > c
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

instance Contextual s => Profunctor (Contextually s r) where
  dimap f g (Contextually p) = Contextually (mapΓΔ f g p)
