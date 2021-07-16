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
import Sequoia.Contextual
import Sequoia.Continuation as K
import Sequoia.Functor.K
import Sequoia.Polarity

-- Not

class Core e r s => NotIntro e r s where
  notL
    :: Pos a
    =>        _Γ -|s|- _Δ > a
    -- ----------------------
    -> r ¬a < _Γ -|s|- _Δ

  notR
    :: Pos a
    => a < _Γ -|s|- _Δ
    -- ----------------------
    ->     _Γ -|s|- _Δ > r ¬a


notL'
  :: (NotIntro e r s, Weaken e r s, Pos a)
  =>  r ¬a < _Γ -|s|- _Δ
  -- -----------------------
  ->         _Γ -|s|- _Δ > a
notL' p = notR init >>> wkR p

notR'
  :: (NotIntro e r s, Weaken e r s, Pos a)
  =>     _Γ -|s|- _Δ > r ¬a
  -- ----------------------
  -> a < _Γ -|s|- _Δ
notR' p = wkL p >>> notL init


shiftP
  :: (Control s, Contextual e r (s e r))
  => r ¬a < _Γ -|s e r|- _Δ > r
  -- --------------------------
  ->        _Γ -|s e r|- _Δ > a
shiftP = shift . notLK'


dneNK
  :: Contextual e r s
  => K r **a < _Γ -|s|- _Δ
  -- ---------------------
  ->   r ¬-a < _Γ -|s|- _Δ
dneNK = mapL getNotNegate

dniNK
  :: Contextual e r s
  => _Γ -|s|- _Δ > K r **a
  -- ---------------------
  -> _Γ -|s|- _Δ >   r ¬-a
dniNK = mapR notNegate


notLK
  :: Contextual e r s
  => K r  a < _Γ -|s|- _Δ
  -- --------------------
  ->   r ¬a < _Γ -|s|- _Δ
notLK = mapL getNot

notRK
  :: Contextual e r s
  => _Γ -|s|- _Δ > K r  a
  -- --------------------
  -> _Γ -|s|- _Δ >   r ¬a
notRK = mapR Not


notLK'
  :: Contextual e r s
  =>   r ¬a < _Γ -|s|- _Δ
  -- --------------------
  -> K r  a < _Γ -|s|- _Δ
notLK' = mapL Not

notRK'
  :: Contextual e r s
  => _Γ -|s|- _Δ >   r ¬a
  -- --------------------
  -> _Γ -|s|- _Δ > K r  a
notRK' = mapR getNot
