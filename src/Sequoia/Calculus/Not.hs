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
import Sequoia.Continuation
import Sequoia.Polarity

-- Not

class Core k s => NotIntro k s where
  notL
    :: Pos a
    =>             _Γ -|s|- _Δ > a
    -- ---------------------------
    -> (k ¬a) () < _Γ -|s|- _Δ

  notR
    :: Pos a
    => a < _Γ -|s|- _Δ
    -- ---------------------------
    ->     _Γ -|s|- _Δ > (k ¬a) ()


notL'
  :: (NotIntro k s, Weaken k s, Pos a)
  =>  (k ¬a) () < _Γ -|s|- _Δ
  -- ----------------------------
  ->              _Γ -|s|- _Δ > a
notL' p = notR init >>> wkR p

notR'
  :: (NotIntro k s, Weaken k s, Pos a)
  =>     _Γ -|s|- _Δ > (k ¬a) ()
  -- ---------------------------
  -> a < _Γ -|s|- _Δ
notR' p = wkL p >>> notL init


shiftP
  :: (Control s, Contextual k (s k))
  =>  (k ¬a) () < _Γ -|s k|- _Δ > KRep k ()
  -- ------------------------------------
  ->              _Γ -|s k|- _Δ > a
shiftP = shift . notLK'


dneNK
  :: Contextual k s
  => k **a < _Γ -|s|- _Δ
  -- -------------------
  -> k ¬-a < _Γ -|s|- _Δ
dneNK = mapL getNotNegate

dniNK
  :: Contextual k s
  => _Γ -|s|- _Δ > k **a
  -- -------------------
  -> _Γ -|s|- _Δ > k ¬-a
dniNK = mapR notNegate


notLK
  :: Contextual k s
  =>  k  a  () < _Γ -|s|- _Δ
  -- -----------------------
  -> (k ¬a) () < _Γ -|s|- _Δ
notLK = mapL getNot

notRK
  :: Contextual k s
  => _Γ -|s|- _Δ >  k  a  ()
  -- -----------------------
  -> _Γ -|s|- _Δ > (k ¬a) ()
notRK = mapR Not


notLK'
  :: Contextual k s
  => (k ¬a) () < _Γ -|s|- _Δ
  -- -----------------------
  ->  k  a  () < _Γ -|s|- _Δ
notLK' = mapL Not

notRK'
  :: Contextual k s
  => _Γ -|s|- _Δ > (k ¬a) ()
  -- -----------------------
  -> _Γ -|s|- _Δ >  k  a  ()
notRK' = mapR getNot
