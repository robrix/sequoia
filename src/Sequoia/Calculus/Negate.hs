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

class Core r e s => NegateIntro r e s where
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
  :: (NegateIntro r e s, Weaken r e s, Neg a)
  => r -a < _Γ -|s|- _Δ
  -- ----------------------
  ->        _Γ -|s|- _Δ > a
negateL' p = negateR init >>> wkR p

negateR'
  :: (NegateIntro r e s, Weaken r e s, Neg a)
  =>     _Γ -|s|- _Δ > r -a
  -- ----------------------
  -> a < _Γ -|s|- _Δ
negateR' p = wkL p >>> negateL init


shiftN
  :: (Control s, Contextual r e (s r e))
  => r -a < _Γ -|s r e|- _Δ > r
  -- --------------------------
  ->        _Γ -|s r e|- _Δ > a
shiftN = shift . negateLK'


dnePK
  :: Contextual r e s
  => K r **a < _Γ -|s|- _Δ
  -- ---------------------
  ->   r -¬a < _Γ -|s|- _Δ
dnePK = mapL getNegateNot

dniPK
  :: Contextual r e s
  => _Γ -|s|- _Δ > K r **a
  -- ---------------------
  -> _Γ -|s|- _Δ >   r -¬a
dniPK = mapR negateNot


negateLK
  :: Contextual r e s
  => K r  a < _Γ -|s|- _Δ
  -- --------------------
  ->   r -a < _Γ -|s|- _Δ
negateLK = mapL getNegate

negateRK
  :: Contextual r e s
  => _Γ -|s|- _Δ > K r  a
  -- --------------------
  -> _Γ -|s|- _Δ >   r -a
negateRK = mapR Negate


negateLK'
  :: Contextual r e s
  =>   r -a < _Γ -|s|- _Δ
  -- --------------------
  -> K r  a < _Γ -|s|- _Δ
negateLK' = mapL Negate

negateRK'
  :: Contextual r e s
  => _Γ -|s|- _Δ >   r -a
  -- --------------------
  -> _Γ -|s|- _Δ > K r  a
negateRK' = mapR getNegate
