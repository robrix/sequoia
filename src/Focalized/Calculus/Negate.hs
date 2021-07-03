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

import Focalized.Calculus.Context
import Focalized.Calculus.Control
import Focalized.Calculus.Core
import Focalized.Connective.Negate
import Focalized.Connective.Negation
import Focalized.Polarity
import Prelude hiding (init)

-- Negate

class Core s => NegateIntro s where
  negateL
    :: Neg a
    =>          _Γ -|s|- _Δ > a
    -- ------------------------
    -> K s -a < _Γ -|s|- _Δ
  negateR
    :: Neg a
    => a < _Γ -|s|- _Δ
    -- ------------------------
    ->     _Γ -|s|- _Δ > K s -a


negateL'
  :: (NegateIntro s, Weaken s, Neg a)
  => K s -a < _Γ -|s|- _Δ
  -- ------------------------
  ->          _Γ -|s|- _Δ > a
negateL' p = negateR init >>> wkR p

negateR'
  :: (NegateIntro s, Weaken s, Neg a)
  =>     _Γ -|s|- _Δ > K s -a
  -- ------------------------
  -> a < _Γ -|s|- _Δ
negateR' p = wkL p >>> negateL init


shiftN
  :: (Control s, Contextual (s r))
  => K (s r) -a < _Γ -|s r|- _Δ > r
  -- ------------------------------
  ->              _Γ -|s r|- _Δ > a
shiftN = shift . negateLK'


dnePK
  :: Contextual s
  => KK s   a < _Γ -|s|- _Δ
  -- ----------------------
  -> K  s -¬a < _Γ -|s|- _Δ
dnePK = mapL getNegateNot

dniPK
  :: Contextual s
  => _Γ -|s|- _Δ > KK s   a
  -- ----------------------
  -> _Γ -|s|- _Δ > K  s -¬a
dniPK = mapR negateNot


negateLK
  :: Contextual s
  => K s  a < _Γ -|s|- _Δ
  -- --------------------
  -> K s -a < _Γ -|s|- _Δ
negateLK = mapL getNegate

negateRK
  :: Contextual s
  => _Γ -|s|- _Δ > K s  a
  -- --------------------
  -> _Γ -|s|- _Δ > K s -a
negateRK = mapR Negate


negateLK'
  :: Contextual s
  => K s -a < _Γ -|s|- _Δ
  -- --------------------
  -> K s  a < _Γ -|s|- _Δ
negateLK' = mapL Negate

negateRK'
  :: Contextual s
  => _Γ -|s|- _Δ > K s -a
  -----------------------
  -> _Γ -|s|- _Δ > K s  a
negateRK' = mapR getNegate
