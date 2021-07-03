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
import Focalized.Continuation
import Focalized.Polarity
import Prelude hiding (init)

-- Negate

class Core k s => NegateIntro k s where
  negateL
    :: Neg a
    =>        _Γ -|s|- _Δ > a
    -- ------------------------
    -> k -a < _Γ -|s|- _Δ
  negateR
    :: Neg a
    => a < _Γ -|s|- _Δ
    -- ------------------------
    ->     _Γ -|s|- _Δ > k -a


negateL'
  :: (NegateIntro k s, Weaken k s, Neg a)
  => k -a < _Γ -|s|- _Δ
  -- ----------------------
  ->        _Γ -|s|- _Δ > a
negateL' p = negateR init >>> wkR p

negateR'
  :: (NegateIntro k s, Weaken k s, Neg a)
  =>     _Γ -|s|- _Δ > k -a
  -- ----------------------
  -> a < _Γ -|s|- _Δ
negateR' p = wkL p >>> negateL init


shiftN
  :: (Control s, Contextual k (s k))
  => k -a < _Γ -|s k|- _Δ > Rep k
  -- ----------------------------
  ->        _Γ -|s k|- _Δ > a
shiftN = shift . negateLK'


dnePK
  :: Contextual k s
  => k **a < _Γ -|s|- _Δ
  -- -------------------
  -> k -¬a < _Γ -|s|- _Δ
dnePK = mapL getNegateNot

dniPK
  :: Contextual k s
  => _Γ -|s|- _Δ > k **a
  -- -------------------
  -> _Γ -|s|- _Δ > k -¬a
dniPK = mapR negateNot


negateLK
  :: Contextual k s
  => k  a < _Γ -|s|- _Δ
  -- ------------------
  -> k -a < _Γ -|s|- _Δ
negateLK = mapL getNegate

negateRK
  :: Contextual k s
  => _Γ -|s|- _Δ > k  a
  -- ------------------
  -> _Γ -|s|- _Δ > k -a
negateRK = mapR Negate


negateLK'
  :: Contextual k s
  => k -a < _Γ -|s|- _Δ
  -- ------------------
  -> k  a < _Γ -|s|- _Δ
negateLK' = mapL Negate

negateRK'
  :: Contextual k s
  => _Γ -|s|- _Δ > k -a
  -- ------------------
  -> _Γ -|s|- _Δ > k  a
negateRK' = mapR getNegate
