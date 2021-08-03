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

import Data.Profunctor
import Prelude hiding (init)
import Sequoia.Calculus.Context
import Sequoia.Calculus.Control
import Sequoia.Calculus.Core
import Sequoia.Calculus.Structural
import Sequoia.Connective.Negation
import Sequoia.Connective.Not
import Sequoia.Contextual
import Sequoia.Polarity
import Sequoia.Profunctor.Continuation
import Sequoia.Profunctor.Value

-- Not

class Core s => NotIntro s where
  notL
    :: Pos a
    =>         _Γ -|s e r|- _Δ > a
    -- ---------------------------
    -> a ¬ r < _Γ -|s e r|- _Δ

  notR
    :: Pos a
    => a < _Γ -|s e r|- _Δ
    -- ---------------------------
    ->     _Γ -|s e r|- _Δ > a ¬ r


notL'
  :: (NotIntro s, Weaken s, Pos a)
  => a ¬ r < _Γ -|s e r|- _Δ
  -- ---------------------------
  ->         _Γ -|s e r|- _Δ > a
notL' p = notR init >>> wkR p

notR'
  :: (NotIntro s, Weaken s, Pos a)
  =>     _Γ -|s e r|- _Δ > a ¬ r
  -- ---------------------------
  -> a < _Γ -|s e r|- _Δ
notR' p = wkL p >>> notL init


shiftP
  :: (Control s, Contextual s)
  => a ¬ r < _Γ -|s e r|- _Δ > r
  -- ---------------------------
  ->         _Γ -|s e r|- _Δ > a
shiftP = shift . notLK'


dneNK
  :: Contextual s
  =>           a •• r < _Γ -|s e r|- _Δ
  -- ----------------------------------
  -> Negate e r a ¬ r < _Γ -|s e r|- _Δ
dneNK = mapL (\ v -> V (\ e -> getNotNegate e (e ∘ v)))

dniNK
  :: Contextual s
  => _Γ -|s e r|- _Δ > a •• r
  -- ----------------------------------
  -> _Γ -|s e r|- _Δ > Negate e r a ¬ r
dniNK = mapR (lmap notNegate)


notLK
  :: Contextual s
  => a • r < _Γ -|s e r|- _Δ
  -- -----------------------
  -> a ¬ r < _Γ -|s e r|- _Δ
notLK = mapL (fmap getNot)

notRK
  :: Contextual s
  => _Γ -|s e r|- _Δ > a • r
  -- -----------------------
  -> _Γ -|s e r|- _Δ > a ¬ r
notRK = mapR (lmap Not)


notLK'
  :: Contextual s
  => a ¬ r < _Γ -|s e r|- _Δ
  -- -----------------------
  -> a • r < _Γ -|s e r|- _Δ
notLK' = mapL (fmap Not)

notRK'
  :: Contextual s
  => _Γ -|s e r|- _Δ > a ¬ r
  -- -----------------------
  -> _Γ -|s e r|- _Δ > a • r
notRK' = mapR (lmap getNot)
