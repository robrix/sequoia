{-# LANGUAGE TypeFamilies #-}
module Focalized.Calculus.Not
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
, module Focalized.Connective.Not
) where

import Focalized.Calculus.Context
import Focalized.Calculus.Control
import Focalized.Calculus.Core
import Focalized.Connective.Negation
import Focalized.Connective.Not
import Focalized.Continuation
import Focalized.Polarity
import Prelude hiding (init)

-- Not

class Core s => NotIntro s where
  notL
    :: Pos a
    =>              _Γ -|s|- _Δ > a
    -- ----------------------------
    -> R (K s) ¬a < _Γ -|s|- _Δ

  notR
    :: Pos a
    => a < _Γ -|s|- _Δ
    -- ----------------------------
    ->     _Γ -|s|- _Δ > R (K s) ¬a


notL'
  :: (NotIntro s, Weaken s, Pos a)
  =>  R (K s) ¬a < _Γ -|s|- _Δ
  -- -----------------------------
  ->               _Γ -|s|- _Δ > a
notL' p = notR init >>> wkR p

notR'
  :: (NotIntro s, Weaken s, Pos a)
  =>     _Γ -|s|- _Δ > R (K s) ¬a
  -- ----------------------------
  -> a < _Γ -|s|- _Δ
notR' p = wkL p >>> notL init


shiftP
  :: (Control s, Contextual (s r), K (s r) ~ (•) r)
  =>  r ¬a < _Γ -|s r|- _Δ > r
  -- -------------------------
  ->         _Γ -|s r|- _Δ > a
shiftP = shift . notLK'


dneNK
  :: (Contextual s, K s ~ (•) (R (K s)))
  => K s (K s a) < _Γ -|s|- _Δ
  -- -------------------------
  -> R (K s) ¬-a < _Γ -|s|- _Δ
dneNK = mapL getNotNegate

dniNK
  :: (Contextual s, K s ~ (•) (R (K s)))
  => _Γ -|s|- _Δ > K s (K s a)
  -- -------------------------
  -> _Γ -|s|- _Δ > R (K s) ¬-a
dniNK = mapR notNegate


notLK
  :: Contextual s
  => R (K s) •a < _Γ -|s|- _Δ
  -- ------------------------
  -> R (K s) ¬a < _Γ -|s|- _Δ
notLK = mapL getNot

notRK
  :: Contextual s
  => _Γ -|s|- _Δ > R (K s) •a
  -- ------------------------
  -> _Γ -|s|- _Δ > R (K s) ¬a
notRK = mapR Not


notLK'
  :: Contextual s
  => R (K s) ¬a < _Γ -|s|- _Δ
  -- --------------------------
  -> R (K s) •a < _Γ -|s|- _Δ
notLK' = mapL Not

notRK'
  :: Contextual s
  => _Γ -|s|- _Δ > R (K s) ¬a
  -- ------------------------
  -> _Γ -|s|- _Δ > R (K s) •a
notRK' = mapR getNot
