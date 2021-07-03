module Focalized.Calculus.Negate
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
, module Focalized.Connective.Negate
) where

import Focalized.CPS
import Focalized.Calculus.Context
import Focalized.Calculus.Control
import Focalized.Calculus.Core
import Focalized.Connective.Negate
import Focalized.Connective.Negation
import Focalized.Continuation
import Focalized.Polarity
import Prelude hiding (init)

-- Negate

class NegateIntro s where
  negateL
    :: Neg a
    =>        _Γ -|s r|- _Δ > a
    -- ------------------------
    -> r -a < _Γ -|s r|- _Δ
  negateR
    :: Neg a
    => a < _Γ -|s r|- _Δ
    -- ------------------------
    ->     _Γ -|s r|- _Δ > r -a


negateL'
  :: (NegateIntro s, Weaken s, Neg a)
  => r -a < _Γ -|s r|- _Δ
  -- ------------------------
  ->        _Γ -|s r|- _Δ > a
negateL' p = negateR init >>> wkR p

negateR'
  :: (NegateIntro s, Weaken s, Neg a)
  =>     _Γ -|s r|- _Δ > r -a
  -- ------------------------
  -> a < _Γ -|s r|- _Δ
negateR' p = wkL p >>> negateL init


shiftN
  :: (Control s, Contextual s)
  => r -a < _Γ -|s r|- _Δ > r
  -- ------------------------
  ->        _Γ -|s r|- _Δ > a
shiftN = shift . negateLK'


dnePK
  :: Contextual s
  => r ••a < _Γ -|s r|- _Δ
  -- ---------------------
  -> r -¬a < _Γ -|s r|- _Δ
dnePK = mapL getNegateNot

dniPK
  :: Contextual s
  => _Γ -|s r|- _Δ > r ••a
  -- ---------------------
  -> _Γ -|s r|- _Δ > r -¬a
dniPK = mapR negateNot


negateLK
  :: Contextual s
  => r •a < _Γ -|s r|- _Δ
  -- --------------------
  -> r -a < _Γ -|s r|- _Δ
negateLK = mapL getNegate

negateRK
  :: Contextual s
  => _Γ -|s r|- _Δ > r •a
  -- --------------------
  -> _Γ -|s r|- _Δ > r -a
negateRK = mapR Negate


negateLK'
  :: Contextual s
  => r -a < _Γ -|s r|- _Δ
  -- --------------------
  -> r •a < _Γ -|s r|- _Δ
negateLK' = mapL Negate

negateRK'
  :: Contextual s
  => _Γ -|s r|- _Δ > r -a
  -- --------------------
  -> _Γ -|s r|- _Δ > r •a
negateRK' = mapR getNegate
