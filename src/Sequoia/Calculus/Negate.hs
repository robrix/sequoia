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
import Sequoia.Functor.K
import Sequoia.Polarity

-- Negate

class Core e r s => NegateIntro e r s where
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
  :: (NegateIntro e r s, Weaken e r s, Neg a)
  => r -a < _Γ -|s|- _Δ
  -- ----------------------
  ->        _Γ -|s|- _Δ > a
negateL' p = negateR init >>> wkR p

negateR'
  :: (NegateIntro e r s, Weaken e r s, Neg a)
  =>     _Γ -|s|- _Δ > r -a
  -- ----------------------
  -> a < _Γ -|s|- _Δ
negateR' p = wkL p >>> negateL init


shiftN
  :: (Control s, Contextual e r (s e r))
  => r -a < _Γ -|s e r|- _Δ > r
  -- --------------------------
  ->        _Γ -|s e r|- _Δ > a
shiftN = shift . negateLK'


dnePK
  :: Contextual e r s
  => K r **a < _Γ -|s|- _Δ
  -- ---------------------
  ->   r -¬a < _Γ -|s|- _Δ
dnePK = mapL getNegateNot

dniPK
  :: Contextual e r s
  => _Γ -|s|- _Δ > K r **a
  -- ---------------------
  -> _Γ -|s|- _Δ >   r -¬a
dniPK = mapR negateNot


negateLK
  :: Contextual e r s
  => K r  a < _Γ -|s|- _Δ
  -- --------------------
  ->   r -a < _Γ -|s|- _Δ
negateLK = mapL getNegate

negateRK
  :: Contextual e r s
  => _Γ -|s|- _Δ > K r  a
  -- --------------------
  -> _Γ -|s|- _Δ >   r -a
negateRK = mapR Negate


negateLK'
  :: Contextual e r s
  =>   r -a < _Γ -|s|- _Δ
  -- --------------------
  -> K r  a < _Γ -|s|- _Δ
negateLK' = mapL Negate

negateRK'
  :: Contextual e r s
  => _Γ -|s|- _Δ >   r -a
  -- --------------------
  -> _Γ -|s|- _Δ > K r  a
negateRK' = mapR getNegate
