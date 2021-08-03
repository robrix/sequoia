{-# LANGUAGE TypeFamilies #-}
module Sequoia.Calculus.Negate
( -- * Negate
  NegateIntro(..)
, negateL'
, negateR'
, shiftN
, dnePK
, dniPK
, negateLK
, negateRK
, negateLK'
, negateRK'
  -- * Connectives
, module Sequoia.Connective.Negate
) where

import Data.Profunctor
import Prelude hiding (init, negate)
import Sequoia.Calculus.Context
import Sequoia.Calculus.Control
import Sequoia.Calculus.Core
import Sequoia.Calculus.Structural
import Sequoia.Conjunction
import Sequoia.Connective.Negate
import Sequoia.Connective.Negation
import Sequoia.Contextual
import Sequoia.Polarity
import Sequoia.Profunctor.Context
import Sequoia.Profunctor.Continuation as K
import Sequoia.Profunctor.Value

-- Negate

class Core s => NegateIntro s where
  negateL
    :: Neg a
    =>                _Γ -|s e r|- _Δ > a
    -- ----------------------------------
    -> Negate e a r < _Γ -|s e r|- _Δ

  negateR
    :: Neg a
    => a < _Γ -|s e r|- _Δ
    -- ----------------------------------
    ->     _Γ -|s e r|- _Δ > Negate e a r


negateL'
  :: (NegateIntro s, Weaken s, Neg a)
  => Negate e a r < _Γ -|s e r|- _Δ
  -- ----------------------------------
  ->                _Γ -|s e r|- _Δ > a
negateL' p = negateR init >>> wkR p

negateR'
  :: (NegateIntro s, Weaken s, Neg a)
  =>     _Γ -|s e r|- _Δ > Negate e a r
  -- ----------------------------------
  -> a < _Γ -|s e r|- _Δ
negateR' p = wkL p >>> negateL init


shiftN
  :: (Control s, Contextual s)
  => Negate e a r < _Γ -|s e r|- _Δ > r
  -- ----------------------------------
  ->                _Γ -|s e r|- _Δ > a
shiftN = shift . negateLK'


dnePK
  :: Contextual s
  =>             a •• r < _Γ -|s e r|- _Δ
  -- --------------------------------------
  -> Negate e (a ¬ r) r < _Γ -|s e r|- _Δ
dnePK = mapL (fmap getNegateNot)

dniPK
  :: Contextual s
  => _Γ -|s e r|- _Δ > a •• r
  -- ------------------------------------
  -> _Γ -|s e r|- _Δ > Negate e (a ¬ r) r
dniPK s = sequent (\ _Δ _Γ -> env (\ e -> appSequent s (lmap (fmap (negateNot e)) _Δ) _Γ))


negateLK
  :: Contextual s
  =>        a • r < _Γ -|s e r|- _Δ
  -- ------------------------------
  -> Negate e a r < _Γ -|s e r|- _Δ
negateLK = mapL (fmap negateK)

negateRK
  :: Contextual s
  => _Γ -|s e r|- _Δ > a • r
  -- ------------------------------
  -> _Γ -|s e r|- _Δ > Negate e a r
negateRK s = sequent (\ _Δ _Γ -> env (\ e -> appSequent s (lmap (fmap (negate e)) _Δ) _Γ))


negateLK'
  :: Contextual s
  => Negate e a r < _Γ -|s e r|- _Δ
  -- ------------------------------
  ->        a • r < _Γ -|s e r|- _Δ
negateLK' s = sequent (\ _Δ _Γ -> env (\ e -> appSequent s _Δ (pure (negate e (e ∘ exlF _Γ)) >∘∘< exrF _Γ)))

negateRK'
  :: Contextual s
  => _Γ -|s e r|- _Δ > Negate e a r
  -- ------------------------------
  -> _Γ -|s e r|- _Δ > a • r
negateRK' = mapR (lmap negateK)
