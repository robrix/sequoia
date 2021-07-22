{-# LANGUAGE TypeFamilies #-}
module Sequoia.Calculus.Not
( -- * Not
  NotIntro(..)
, notL'
, notR'
, shiftP
, dneNK
, dniNK
, notLK
, notRK
, notLK'
, notRK'
  -- * Connectives
, module Sequoia.Connective.Not
) where

import Prelude hiding (init)
import Sequoia.Calculus.Context
import Sequoia.Calculus.Control
import Sequoia.Calculus.Core
import Sequoia.Calculus.Structural
import Sequoia.Connective.Negation
import Sequoia.Connective.Not
import Sequoia.Contextual
import Sequoia.Functor.Continuation as K
import Sequoia.Polarity

-- Not

class Core s => NotIntro s where
  notL
    :: Pos a
    =>        _Γ -|s e r|- _Δ > a
    -- --------------------------
    -> r ¬a < _Γ -|s e r|- _Δ

  notR
    :: Pos a
    => a < _Γ -|s e r|- _Δ
    -- --------------------------
    ->     _Γ -|s e r|- _Δ > r ¬a


notL'
  :: (NotIntro s, Weaken s, Pos a)
  => r ¬a < _Γ -|s e r|- _Δ
  -- --------------------------
  ->        _Γ -|s e r|- _Δ > a
notL' p = notR init >>> wkR p

notR'
  :: (NotIntro s, Weaken s, Pos a)
  =>     _Γ -|s e r|- _Δ > r ¬a
  -- --------------------------
  -> a < _Γ -|s e r|- _Δ
notR' p = wkL p >>> notL init


shiftP
  :: (Control s, Contextual s)
  => r ¬a < _Γ -|s e r|- _Δ > r
  -- --------------------------
  ->        _Γ -|s e r|- _Δ > a
shiftP = shift . notLK'


dneNK
  :: Contextual s
  => K r (K r a) < _Γ -|s e r|- _Δ
  -- -----------------------------
  ->      r ¬-a  < _Γ -|s e r|- _Δ
dneNK = mapL (fmap getNotNegate)

dniNK
  :: Contextual s
  => _Γ -|s e r|- _Δ > K r (K r a)
  -- -----------------------------
  -> _Γ -|s e r|- _Δ >      r ¬-a
dniNK = mapR (contramap notNegate)


notLK
  :: Contextual s
  => K r  a < _Γ -|s e r|- _Δ
  -- ------------------------
  ->   r ¬a < _Γ -|s e r|- _Δ
notLK = mapL (fmap getNot)

notRK
  :: Contextual s
  => _Γ -|s e r|- _Δ > K r  a
  -- ------------------------
  -> _Γ -|s e r|- _Δ >   r ¬a
notRK = mapR (contramap Not)


notLK'
  :: Contextual s
  =>   r ¬a < _Γ -|s e r|- _Δ
  -- ------------------------
  -> K r  a < _Γ -|s e r|- _Δ
notLK' = mapL (fmap Not)

notRK'
  :: Contextual s
  => _Γ -|s e r|- _Δ >   r ¬a
  -- ------------------------
  -> _Γ -|s e r|- _Δ > K r  a
notRK' = mapR (contramap getNot)
