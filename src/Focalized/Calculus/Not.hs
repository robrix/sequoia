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
, module Focalized.Negation
) where

import Focalized.CPS
import Focalized.Calculus.Context
import Focalized.Calculus.Control
import Focalized.Calculus.Core
import Focalized.Negation
import Focalized.Polarity
import Prelude hiding (init)

-- Negative negation

class NegNegation s where
  notL
    :: Pos a
    =>        i -|s r|- o > a
    -- ----------------------
    -> r ¬a < i -|s r|- o

  notR
    :: Pos a
    => a < i -|s r|- o
    -- ----------------------
    ->     i -|s r|- o > r ¬a


notL'
  :: (NegNegation s, Weaken s, Pos a)
  => r ¬a < i -|s r|- o
  -- ----------------------
  ->        i -|s r|- o > a
notL' p = notR init >>> wkR p

notR'
  :: (NegNegation s, Weaken s, Pos a)
  =>     i -|s r|- o > r ¬a
  -- ----------------------
  -> a < i -|s r|- o
notR' p = wkL p >>> notL init


shiftP
  :: (Control s, Contextual s)
  => r ¬a < i -|s r|- o > r
  -- ----------------------
  ->        i -|s r|- o > a
shiftP = shift . notLK'


dneNK
  :: Contextual s
  => r ••a < i -|s r|- o
  -- -------------------
  -> r ¬-a < i -|s r|- o
dneNK = mapL getNotNegate

dniNK
  :: Contextual s
  => i -|s r|- o > r ••a
  -- -------------------
  -> i -|s r|- o > r ¬-a
dniNK = mapR notNegate


notLK
  :: Contextual s
  =>  r •a < i -|s r|- o
  -- -------------------
  ->  r ¬a < i -|s r|- o
notLK = mapL getNot

notRK
  :: Contextual s
  => i -|s r|- o > r •a
  -- ------------------
  -> i -|s r|- o > r ¬a
notRK = mapR Not


notLK'
  :: Contextual s
  =>  r ¬a < i -|s r|- o
  -- --------------------
  ->  r •a < i -|s r|- o
notLK' = mapL Not

notRK'
  :: Contextual s
  => i -|s r|- o > r ¬a
  -- ------------------
  -> i -|s r|- o > r •a
notRK' = mapR getNot
