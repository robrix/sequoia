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
import Sequoia.Connective.Negation
import Sequoia.Connective.Not
import Sequoia.Continuation as K
import Sequoia.Polarity

-- Not

class Core k v s => NotIntro k v s where
  notL
    :: Pos a
    =>        _Γ -|s|- _Δ > a
    -- ----------------------
    -> k ¬a < _Γ -|s|- _Δ

  notR
    :: Pos a
    => a < _Γ -|s|- _Δ
    -- ----------------------
    ->     _Γ -|s|- _Δ > k ¬a


notL'
  :: (NotIntro k v s, Weaken k v s, Pos a)
  =>  k ¬a < _Γ -|s|- _Δ
  -- -----------------------
  ->         _Γ -|s|- _Δ > a
notL' p = notR init >>> wkR p

notR'
  :: (NotIntro k v s, Weaken k v s, Pos a)
  =>     _Γ -|s|- _Δ > k ¬a
  -- ----------------------
  -> a < _Γ -|s|- _Δ
notR' p = wkL p >>> notL init


shiftP
  :: (Control k s, Contextual (k r) v (s r e), K.Rep (k r) ~ r)
  =>  k r ¬a < _Γ -|s r e|- _Δ > r
  -- -----------------------------
  ->           _Γ -|s r e|- _Δ > a
shiftP = shift . notLK'


dneNK
  :: Contextual k v s
  => k **a < _Γ -|s|- _Δ
  -- -------------------
  -> k ¬-a < _Γ -|s|- _Δ
dneNK = mapL getNotNegate

dniNK
  :: Contextual k v s
  => _Γ -|s|- _Δ > k **a
  -- -------------------
  -> _Γ -|s|- _Δ > k ¬-a
dniNK = mapR notNegate


notLK
  :: Contextual k v s
  => k  a < _Γ -|s|- _Δ
  -- ------------------
  -> k ¬a < _Γ -|s|- _Δ
notLK = mapL getNot

notRK
  :: Contextual k v s
  => _Γ -|s|- _Δ > k  a
  -- ------------------
  -> _Γ -|s|- _Δ > k ¬a
notRK = mapR Not


notLK'
  :: Contextual k v s
  => k ¬a < _Γ -|s|- _Δ
  -- ------------------
  -> k  a < _Γ -|s|- _Δ
notLK' = mapL Not

notRK'
  :: Contextual k v s
  => _Γ -|s|- _Δ > k ¬a
  -- ------------------
  -> _Γ -|s|- _Δ > k  a
notRK' = mapR getNot
