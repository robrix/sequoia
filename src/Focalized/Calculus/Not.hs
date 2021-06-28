module Focalized.Calculus.Not
( -- * Negative negation
  NegNegation(..)
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
, module Focalized.Not
) where

import Focalized.CPS
import Focalized.Calculus.Context
import Focalized.Calculus.Control
import Focalized.Calculus.Core
import Focalized.Negation
import Focalized.Not
import Focalized.Polarity
import Prelude hiding (init)

-- Negative negation

class NegNegation s where
  notL
    :: Pos a
    =>        _Γ -|s r|- _Δ > a
    -- ------------------------
    -> r ¬a < _Γ -|s r|- _Δ

  notR
    :: Pos a
    => a < _Γ -|s r|- _Δ
    -- ------------------------
    ->     _Γ -|s r|- _Δ > r ¬a


notL'
  :: (NegNegation s, Weaken s, Pos a)
  => r ¬a < _Γ -|s r|- _Δ
  -- ------------------------
  ->        _Γ -|s r|- _Δ > a
notL' p = notR init >>> wkR p

notR'
  :: (NegNegation s, Weaken s, Pos a)
  =>     _Γ -|s r|- _Δ > r ¬a
  -- ------------------------
  -> a < _Γ -|s r|- _Δ
notR' p = wkL p >>> notL init


shiftP
  :: (Control s, Contextual s)
  => r ¬a < _Γ -|s r|- _Δ > r
  -- ------------------------
  ->        _Γ -|s r|- _Δ > a
shiftP = shift . notLK'


dneNK
  :: Contextual s
  => r ••a < _Γ -|s r|- _Δ
  -- ---------------------
  -> r ¬-a < _Γ -|s r|- _Δ
dneNK = mapL getNotNegate

dniNK
  :: Contextual s
  => _Γ -|s r|- _Δ > r ••a
  -- ---------------------
  -> _Γ -|s r|- _Δ > r ¬-a
dniNK = mapR notNegate


notLK
  :: Contextual s
  =>  r •a < _Γ -|s r|- _Δ
  -- ---------------------
  ->  r ¬a < _Γ -|s r|- _Δ
notLK = mapL getNot

notRK
  :: Contextual s
  => _Γ -|s r|- _Δ > r •a
  -- --------------------
  -> _Γ -|s r|- _Δ > r ¬a
notRK = mapR Not


notLK'
  :: Contextual s
  =>  r ¬a < _Γ -|s r|- _Δ
  -- ---------------------
  ->  r •a < _Γ -|s r|- _Δ
notLK' = mapL Not

notRK'
  :: Contextual s
  => _Γ -|s r|- _Δ > r ¬a
  -- --------------------
  -> _Γ -|s r|- _Δ > r •a
notRK' = mapR getNot
