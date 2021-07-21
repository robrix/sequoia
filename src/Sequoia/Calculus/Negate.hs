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
import Sequoia.Calculus.Structural
import Sequoia.Connective.Negate
import Sequoia.Connective.Negation
import Sequoia.Contextual
import Sequoia.Continuation as K
import Sequoia.Functor.K
import Sequoia.Polarity

-- Negate

class Core s => NegateIntro s where
  negateL
    :: Neg a
    =>        _Γ -|s e r|- _Δ > a
    -- --------------------------
    -> r -a < _Γ -|s e r|- _Δ

  negateR
    :: Neg a
    => a < _Γ -|s e r|- _Δ
    -- --------------------------
    ->     _Γ -|s e r|- _Δ > r -a


negateL'
  :: (NegateIntro s, Weaken s, Neg a)
  => r -a < _Γ -|s e r|- _Δ
  -- --------------------------
  ->        _Γ -|s e r|- _Δ > a
negateL' p = negateR init >>> wkR p

negateR'
  :: (NegateIntro s, Weaken s, Neg a)
  =>     _Γ -|s e r|- _Δ > r -a
  -- --------------------------
  -> a < _Γ -|s e r|- _Δ
negateR' p = wkL p >>> negateL init


shiftN
  :: (Control s, Contextual s)
  => r -a < _Γ -|s e r|- _Δ > r
  -- --------------------------
  ->        _Γ -|s e r|- _Δ > a
shiftN = shift . negateLK'


dnePK
  :: Contextual s
  => K r (K r a) < _Γ -|s e r|- _Δ
  -- -----------------------------
  ->      r -¬a  < _Γ -|s e r|- _Δ
dnePK = mapL (fmap getNegateNot)

dniPK
  :: Contextual s
  => _Γ -|s e r|- _Δ > K r (K r a)
  -- -----------------------------
  -> _Γ -|s e r|- _Δ >      r -¬a
dniPK = mapR (contramap negateNot)


negateLK
  :: Contextual s
  => K r  a < _Γ -|s e r|- _Δ
  -- ------------------------
  ->   r -a < _Γ -|s e r|- _Δ
negateLK = mapL (fmap getNegate)

negateRK
  :: Contextual s
  => _Γ -|s e r|- _Δ > K r  a
  -- ------------------------
  -> _Γ -|s e r|- _Δ >   r -a
negateRK = mapR (contramap Negate)


negateLK'
  :: Contextual s
  =>   r -a < _Γ -|s e r|- _Δ
  -- ------------------------
  -> K r  a < _Γ -|s e r|- _Δ
negateLK' = mapL (fmap Negate)

negateRK'
  :: Contextual s
  => _Γ -|s e r|- _Δ >   r -a
  -- ------------------------
  -> _Γ -|s e r|- _Δ > K r  a
negateRK' = mapR (contramap getNegate)
