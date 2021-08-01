{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}
module Sequoia.Contextual
( -- * Contextual
  Contextual(..)
  -- ** Popping
, popΓΔ
, popΓ
, popΔ
, popL
, popR
  -- ** Pushing
, pushΓΔ
, pushΓ
, pushΔ
, pushL
, pushR
, poppedL
, poppedR
, poppedΓ
, poppedΔ
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
, traverseΓΔ
, traverseΓ
, traverseΔ
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
import Data.Function
import Data.Profunctor
import Fresnel.Getter
import Fresnel.Iso
import Fresnel.Review
import Fresnel.Setter
import Prelude hiding (init)
import Sequoia.Calculus.Context
import Sequoia.Calculus.Core
import Sequoia.Calculus.Structural
import Sequoia.Conjunction
import Sequoia.Disjunction
import Sequoia.Profunctor.Context
import Sequoia.Profunctor.Continuation
import Sequoia.Profunctor.Value

-- Contextual

class (Core s, forall e r a . MonadEnv e (s e r a), forall e r . Profunctor (s e r)) => Contextual s where
  sequent :: (_Δ • r -> e ∘ _Γ -> e ==> r) -> _Γ -|s e r|- _Δ
  appSequent :: _Γ -|s e r|- _Δ -> (_Δ • r -> e ∘ _Γ -> e ==> r)



-- Popping

popΓΔ
  :: Contextual s
  => Iso' (_Δ • r) (_Δ' • r, y)
  -> Iso' (e ∘ _Γ) (x, e ∘ _Γ')
  -> (y -> x -> _Γ' -|s e r|- _Δ')
  -- -----------------------------
  ->            _Γ  -|s e r|- _Δ
popΓΔ oΔ oΓ f = sequent (\ _Δ _Γ ->
  let (_Δ', y) = view oΔ _Δ
      (x, _Γ') = view oΓ _Γ
  in appSequent (f y x) _Δ' _Γ')

-- | Pop something off the input context which can later be pushed. Used with 'pushΓ', this provides a generalized context restructuring facility.
--
-- @
-- popΓ o . pushΓ o = id
-- @
-- @
-- pushΓ o . popΓ o = id
-- @
popΓ
  :: Contextual s
  => Iso' (e ∘ _Γ) (x, e ∘ _Γ')
  -> (x -> _Γ' -|s e r|- _Δ)
  -- -----------------------
  ->       _Γ  -|s e r|- _Δ
popΓ o = popΓΔ idΔ o . const

-- | Pop something off the output context which can later be pushed. Used with 'pushΔ', this provides a generalized context restructuring facility.
--
-- @
-- popΔ o . pushΔ o = id
-- @
-- @
-- pushΔ o . popΔ o = id
-- @
popΔ
  :: Contextual s
  => Iso' (_Δ • r) (_Δ' • r, y)
  -> (y -> _Γ -|s e r|- _Δ')
  -- -----------------------
  ->       _Γ -|s e r|- _Δ
popΔ o f = sequent (\ _Δ -> let (_Δ', y) = view o _Δ in appSequent (f y) _Δ')


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
  => (e ∘ a -> _Γ -|s e r|- _Δ)
  -- --------------------------
  ->      a  < _Γ -|s e r|- _Δ
popL = popΓ consΓ

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
  => (a • r -> _Γ -|s e r|- _Δ)
  -- -----------------------------
  ->           _Γ -|s e r|- _Δ > a
popR = popΔ snocΔ


popL2
  :: Contextual s
  => (e ∘ a -> e ∘ b -> _Γ -|s e r|- _Δ)
  -- -----------------------------------
  ->      a      < b  < _Γ -|s e r|- _Δ
popL2 f = popL (popL . f)

popR2
  :: Contextual s
  => (a • r -> b • r -> _Γ -|s e r|- _Δ)
  -- ------------------------------------------
  ->                    _Γ -|s e r|- _Δ > b > a
popR2 f = popR (popR . f)


poppedΓ
  :: Contextual s
  => Iso
    (e ∘ _Γ''')   (e ∘ _Γ)
    (x, e ∘ _Γ'') (x, e ∘ _Γ')
  -> Setter
    (_Γ  -|s e r|- _Δ) (_Γ''' -|s e r|- _Δ')
    (_Γ' -|s e r|- _Δ) (_Γ''  -|s e r|- _Δ')
poppedΓ g = roam (\ f p -> traverseΓ g (\ h -> f (mapΓ h p)))

poppedΔ
  :: Contextual s
  => Iso
    (_Δ''' • r)   (_Δ • r)
    (_Δ'' • r, y) (_Δ' • r, y)
  -> Setter
    (_Γ -|s e r|- _Δ ) (_Γ' -|s e r|- _Δ''')
    (_Γ -|s e r|- _Δ') (_Γ' -|s e r|- _Δ'')
poppedΔ g = roam (\ f p -> traverseΔ g (\ h -> f (mapΔ h p)))


poppedL
  :: Contextual s
  => Setter
    (a < _Γ -|s e r|- _Δ) (a < _Γ' -|s e r|- _Δ')
    (    _Γ -|s e r|- _Δ) (    _Γ' -|s e r|- _Δ')
poppedL = poppedΓ consΓ

poppedR
  :: Contextual s
  => Setter
    (_Γ -|s e r|- _Δ > a) (_Γ' -|s e r|- _Δ' > a)
    (_Γ -|s e r|- _Δ    ) (_Γ' -|s e r|- _Δ'    )
poppedR = poppedΔ snocΔ

poppedL2
  :: Contextual s
  => Setter
    (a < b < _Γ -|s e r|- _Δ) (a < b < _Γ' -|s e r|- _Δ')
    (        _Γ -|s e r|- _Δ) (        _Γ' -|s e r|- _Δ')
poppedL2 = poppedΓ (consΓ . fmapping consΓ . assocConj)

poppedR2
  :: Contextual s
  => Setter
    (_Γ -|s e r|- _Δ > a > b) (_Γ' -|s e r|- _Δ' > a > b)
    (_Γ -|s e r|- _Δ        ) (_Γ' -|s e r|- _Δ'        )
poppedR2 = poppedΔ (snocΔ . firsting snocΔ . from assocConj)


-- Pushing

pushΓΔ
  :: Contextual s
  =>                     _Γ -|s e r|- _Δ
  -- -----------------------------------
  -> (_Δ • r -> e ∘ _Γ -> e -|s e r|- r)
pushΓΔ s _Δ _Γ = sequent (\ _Δ' _Γ' -> _Δ' •<< appSequent s _Δ _Γ <<∘ _Γ')

-- | Push something onto the input context which was previously popped off it. Used with 'popΓ', this provides a generalized context restructuring facility. It is undefined what will happen if you push something which was not previously popped.
--
-- @
-- popΓ o . pushΓ o = id
-- @
-- @
-- pushΓ o . popΓ o = id
-- @
pushΓ
  :: Contextual s
  => Iso' (e ∘ _Γ) (x, e ∘ _Γ')
  ->       _Γ  -|s e r|- _Δ
  -- -----------------------
  -> (x -> _Γ' -|s e r|- _Δ)
pushΓ o s x = sequent (\ _Δ' -> appSequent s _Δ' . review o . (x,))

-- | Push something onto the output context which was previously popped off it. Used with 'popΔ', this provides a generalized context restructuring facility. It is undefined what will happen if you push something which was not previously popped.
--
-- @
-- popΔ o . pushΔ o = id
-- @
-- @
-- pushΔ o . popΔ o = id
-- @
pushΔ
  :: Contextual s
  => Iso' (_Δ • r) (_Δ' • r, y)
  ->       _Γ -|s e r|- _Δ
  -- -----------------------
  -> (y -> _Γ -|s e r|- _Δ')
pushΔ o s y = sequent (appSequent s . review o . (,y))


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
  =>      a  < _Γ -|s e r|- _Δ
  -- --------------------------
  -> (e ∘ a -> _Γ -|s e r|- _Δ)
pushL = pushΓ consΓ

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
  -> (a • r -> _Γ -|s e r|- _Δ)
pushR = pushΔ snocΔ


pushL2
  :: Contextual s
  => a < b < _Γ -|s e r|- _Δ -> e ∘ a -> e ∘ b
  -- -----------------------------------------
  ->         _Γ -|s e r|- _Δ
pushL2 p = pushL . pushL p

pushR2
  :: Contextual s
  => _Γ -|s e r|- _Δ > b > a -> a • r -> b • r
  -- -----------------------------------------
  -> _Γ -|s e r|- _Δ
pushR2 p = pushR . pushR p


-- Mapping

mapΓΔ
  :: Contextual s
  => (e ∘ _Γ' -> e ∘ _Γ)
  -> (_Δ' • r -> _Δ • r)
  -> _Γ  -|s e r|- _Δ
  -- -----------------
  -> _Γ' -|s e r|- _Δ'
mapΓΔ f g p = sequent (\ _Δ _Γ -> appSequent p (g _Δ) (f _Γ))

mapΓ
  :: Contextual s
  => (e ∘ _Γ' -> e ∘ _Γ)
  -> _Γ  -|s e r|- _Δ
  -- ----------------
  -> _Γ' -|s e r|- _Δ
mapΓ = (`mapΓΔ` id)

mapΔ
  :: Contextual s
  => (_Δ' • r -> _Δ • r)
  -> _Γ -|s e r|- _Δ
  -- ----------------
  -> _Γ -|s e r|- _Δ'
mapΔ = (id `mapΓΔ`)


mapL
  :: Contextual s
  => (e ∘ a' -> e ∘ a)
  -> a  < _Γ -|s e r|- _Δ
  -- --------------------
  -> a' < _Γ -|s e r|- _Δ
mapL f = mapΓ (f . exlF >∘∘∘< exrF)

mapR
  :: Contextual s
  => (a' • r -> a • r)
  -> _Γ -|s e r|- _Δ > a
  -- --------------------
  -> _Γ -|s e r|- _Δ > a'
mapR f = mapΔ (inlK <•••> f . inrK)


mapL2
 :: Contextual s
 => (e ∘ c -> Either (e ∘ b) (e ∘ a))
 -> a < _Γ -|s e r|- _Δ   ->   b < _Γ -|s e r|- _Δ
 -- ----------------------------------------------
 ->            c < _Γ -|s e r|- _Δ
mapL2 f a b = popL ((pushL b <--> pushL a) . f)

mapR2
  :: Contextual s
  => ((c • r -> b • r) • r -> a • r)
  -> _Γ -|s e r|- _Δ > a   ->   _Γ -|s e r|- _Δ > b
  -- ----------------------------------------------
  ->            _Γ -|s e r|- _Δ > c
mapR2 f a b = mapR f (wkR' a) >>> popL (val (`mapR` b))
  where wkR' = popR2 . flip . const . pushR


traverseΓΔ
  :: Contextual s
  => Iso
    (e ∘ _Γ''')   (e ∘ _Γ)
    (x, e ∘ _Γ'') (x, e ∘ _Γ')
  -> Iso
    (_Δ''' • r)   (_Δ • r)
    (_Δ'' • r, y) (_Δ' • r, y)
  -> ((e ∘ _Γ' -> e ∘ _Γ) -> (_Δ' • r -> _Δ • r) -> _Γ''  -|s e r|- _Δ'')
  ->                                                _Γ''' -|s e r|- _Δ'''
traverseΓΔ f g s = sequent (\ _Δ' _Γ' -> withIso f (\ saΓ btΓ -> withIso g (\ saΔ btΔ ->
  let (x, _Γ) = saΓ _Γ'
      (_Δ, y) = saΔ _Δ'
  in appSequent (s (btΓ . (x,)) (btΔ . (,y))) _Δ _Γ)))

traverseΓ
  :: Contextual s
  => Iso
    (e ∘ _Γ''')   (e ∘ _Γ)
    (x, e ∘ _Γ'') (x, e ∘ _Γ')
  -> ((e ∘ _Γ' -> e ∘ _Γ) -> _Γ''  -|s e r|- _Δ)
  ->                         _Γ''' -|s e r|- _Δ
traverseΓ f b = traverseΓΔ f idΔ (const . b)

traverseΔ
  :: Contextual s
  => Iso
    (_Δ''' • r)   (_Δ • r)
    (_Δ'' • r, y) (_Δ' • r, y)
  -> ((_Δ' • r -> _Δ • r) -> _Γ -|s e r|- _Δ'')
  ->                         _Γ -|s e r|- _Δ'''
traverseΔ f b = traverseΓΔ idΓ f (const b)


-- Lifting

liftL
  :: Contextual s
  => a • r
  -- -----------------------
  ->     a < _Γ -|s e r|- _Δ
liftL = pushR init

liftR
  :: Contextual s
  =>               e ∘ a
  -- -------------------
  -> _Γ -|s e r|- _Δ > a
liftR = pushΓ consΓ init


-- Lowering

lowerL
  :: Contextual s
  => (a • r                   -> _Γ -|s e r|- _Δ)
  -- --------------------------------------------
  -> (    a < _Γ -|s e r|- _Δ -> _Γ -|s e r|- _Δ)
lowerL k p = popR k >>> p

lowerR
  :: Contextual s
  => (              e ∘ a -> _Γ -|s e r|- _Δ)
  -- ----------------------------------------
  -> (_Γ -|s e r|- _Δ > a -> _Γ -|s e r|- _Δ)
lowerR k p = p >>> popΓ consΓ k


-- Deriving

newtype Contextually s e r _Γ _Δ = Contextually { getContextually :: _Γ -|s e r|- _Δ }
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

instance Contextual s => Profunctor (Contextually s e r) where
  dimap f g (Contextually p) = Contextually (mapΓΔ (fmap f) (lmap g) p)


-- Utilities

idΔ :: Iso' a (a, ())
idΔ = iso (,()) fst

idΓ :: Iso' a ((), a)
idΓ = iso ((),) snd
