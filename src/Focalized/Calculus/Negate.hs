{-# LANGUAGE FunctionalDependencies #-}
module Focalized.Calculus.Negate
( -- * Positive negation
  PosNegation(..)
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
, module Focalized.Negate
) where

import Focalized.CPS
import Focalized.Calculus.Context
import Focalized.Calculus.Control
import Focalized.Calculus.Core
import Focalized.Negate
import Focalized.Negation
import Focalized.Polarity
import Prelude hiding (init)

-- Positive negation

class PosNegation r s | s -> r where
  negateL
    :: Neg a
    =>        _Γ -|s|- _Δ > a
    -- ----------------------
    -> r -a < _Γ -|s|- _Δ
  negateR
    :: Neg a
    => a < _Γ -|s|- _Δ
    -- ----------------------
    ->     _Γ -|s|- _Δ > r -a


negateL'
  :: (PosNegation r s, Weaken s, Neg a)
  => r -a < _Γ -|s|- _Δ
  -- ----------------------
  ->        _Γ -|s|- _Δ > a
negateL' p = negateR init >>> wkR p

negateR'
  :: (PosNegation r s, Weaken s, Neg a)
  =>     _Γ -|s|- _Δ > r -a
  -- ----------------------
  -> a < _Γ -|s|- _Δ
negateR' p = wkL p >>> negateL init


shiftN
  :: (Control s, Contextual r (s r))
  => r -a < _Γ -|s r|- _Δ > r
  -- ------------------------
  ->        _Γ -|s r|- _Δ > a
shiftN = shift . negateLK'


dnePK
  :: Contextual r s
  => r ••a < _Γ -|s|- _Δ
  -- -------------------
  -> r -¬a < _Γ -|s|- _Δ
dnePK = mapL getNegateNot

dniPK
  :: Contextual r s
  => _Γ -|s|- _Δ > r ••a
  -- -------------------
  -> _Γ -|s|- _Δ > r -¬a
dniPK = mapR negateNot


negateLK
  :: Contextual r s
  => r •a < _Γ -|s|- _Δ
  -- ------------------
  -> r -a < _Γ -|s|- _Δ
negateLK = mapL getNegate

negateRK
  :: Contextual r s
  => _Γ -|s|- _Δ > r •a
  -- ------------------
  -> _Γ -|s|- _Δ > r -a
negateRK = mapR Negate


negateLK'
  :: Contextual r s
  => r -a < _Γ -|s|- _Δ
  -- ------------------
  -> r •a < _Γ -|s|- _Δ
negateLK' = mapL Negate

negateRK'
  :: Contextual r s
  => _Γ -|s|- _Δ > r -a
  -- ------------------
  -> _Γ -|s|- _Δ > r •a
negateRK' = mapR getNegate
