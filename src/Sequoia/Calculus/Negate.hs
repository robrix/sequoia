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

import Prelude hiding (init)
import Sequoia.Calculus.Context
import Sequoia.Calculus.Control
import Sequoia.Calculus.Core
import Sequoia.Connective.Negate
import Sequoia.Connective.Negation
import Sequoia.Continuation as K
import Sequoia.Polarity

-- Negate

class Core k v s => NegateIntro k v s where
  negateL
    :: Neg a
    =>        _Γ -|s|- _Δ > a
    -- ----------------------
    -> k -a < _Γ -|s|- _Δ
  negateR
    :: Neg a
    => a < _Γ -|s|- _Δ
    -- ----------------------
    ->     _Γ -|s|- _Δ > k -a


negateL'
  :: (NegateIntro k v s, Weaken k v s, Neg a)
  => k -a < _Γ -|s|- _Δ
  -- ----------------------
  ->        _Γ -|s|- _Δ > a
negateL' p = negateR init >>> wkR p

negateR'
  :: (NegateIntro k v s, Weaken k v s, Neg a)
  =>     _Γ -|s|- _Δ > k -a
  -- ----------------------
  -> a < _Γ -|s|- _Δ
negateR' p = wkL p >>> negateL init


shiftN
  :: (Control k s, Contextual (k r) v (s r e), K.Rep (k r) ~ r)
  => k r -a < _Γ -|s r e|- _Δ > r
  -- ----------------------------
  ->          _Γ -|s r e|- _Δ > a
shiftN = shift . negateLK'


dnePK
  :: Contextual k v s
  => k **a < _Γ -|s|- _Δ
  -- -------------------
  -> k -¬a < _Γ -|s|- _Δ
dnePK = mapL getNegateNot

dniPK
  :: Contextual k v s
  => _Γ -|s|- _Δ > k **a
  -- -------------------
  -> _Γ -|s|- _Δ > k -¬a
dniPK = mapR negateNot


negateLK
  :: Contextual k v s
  => k  a < _Γ -|s|- _Δ
  -- ------------------
  -> k -a < _Γ -|s|- _Δ
negateLK = mapL getNegate

negateRK
  :: Contextual k v s
  => _Γ -|s|- _Δ > k  a
  -- ------------------
  -> _Γ -|s|- _Δ > k -a
negateRK = mapR Negate


negateLK'
  :: Contextual k v s
  => k -a < _Γ -|s|- _Δ
  -- ------------------
  -> k  a < _Γ -|s|- _Δ
negateLK' = mapL Negate

negateRK'
  :: Contextual k v s
  => _Γ -|s|- _Δ > k -a
  -- ------------------
  -> _Γ -|s|- _Δ > k  a
negateRK' = mapR getNegate
