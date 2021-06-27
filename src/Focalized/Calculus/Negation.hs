{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DefaultSignatures #-}
module Focalized.Calculus.Negation
( -- * Negation
  Negation
  -- * Not
, type (¬)(..)
, notNegate
, getNotNegate
, type (¬-)
  -- * Negative negation
, NegNegation(..)
  -- * Negate
, type (-)(..)
, negateNot
, getNegateNot
, type (-¬)
  -- * Positive negation
, PosNegation(..)
) where

import Focalized.CPS
import Focalized.Calculus.Context
import Focalized.Calculus.Control
import Focalized.Calculus.Core
import Focalized.Negation
import Focalized.Polarity
import Prelude hiding (init)

-- Negation

type Negation s = (NegNegation s, PosNegation s)


-- Negative negation

class (Core s, Structural s, Contextual s, Control s) => NegNegation s where
  notL
    :: Pos a
    =>        i -|s r|- o > a
    -- ----------------------
    -> r ¬a < i -|s r|- o
  notL = notLK . kL
  notLK
    :: Pos a
    =>  r •a < i -|s r|- o
    -- -------------------
    ->  r ¬a < i -|s r|- o
  notLK = mapL getNot
  notL'
    :: Pos a
    => r ¬a < i -|s r|- o
    -- ----------------------
    ->        i -|s r|- o > a
  notL' p = notR init >>> wkR p
  notLK'
    :: Pos a
    =>  r ¬a < i -|s r|- o
    -- --------------------
    ->  r •a < i -|s r|- o
  notLK' = mapL Not
  notR
    :: Pos a
    => a < i -|s r|- o
    -- ----------------------
    ->     i -|s r|- o > r ¬a
  notR = notRK . kR
  notRK
    :: Pos a
    => i -|s r|- o > r •a
    -- ------------------
    -> i -|s r|- o > r ¬a
  notRK = mapR Not
  notR'
    :: Pos a
    =>     i -|s r|- o > r ¬a
    -- ----------------------
    -> a < i -|s r|- o
  notR' p = wkL p >>> notL init
  notRK'
    :: Pos a
    => i -|s r|- o > r ¬a
    -- ------------------
    -> i -|s r|- o > r •a
  notRK' = mapR getNot
  shiftP
    :: Pos a
    => r ¬a < i -|s r|- o > r
    -- ----------------------
    ->        i -|s r|- o > a
  shiftP = shift . notLK'

  dneNL
    :: Neg a
    =>     a < i -|s r|- o
    -- -------------------
    -> r ¬-a < i -|s r|- o
  default dneNL
    :: (PosNegation s, Neg a)
    =>     a < i -|s r|- o
    -- -------------------
    -> r ¬-a < i -|s r|- o
  dneNL = notL . negateR
  dneNLK
    :: Neg a
    => r ••a < i -|s r|- o
    -- -------------------
    -> r ¬-a < i -|s r|- o
  default dneNLK
    :: r ••a < i -|s r|- o
    -- -------------------
    -> r ¬-a < i -|s r|- o
  dneNLK = mapL getNotNegate
  dneNR
    :: Neg a
    => i -|s r|- o > a
    -- -------------------
    -> i -|s r|- o > r ¬-a
  default dneNR
    :: (PosNegation s, Neg a)
    => i -|s r|- o > a
    -- -------------------
    -> i -|s r|- o > r ¬-a
  dneNR = notR . negateL
  dneNRK
    :: Neg a
    => i -|s r|- o > r ••a
    -- -------------------
    -> i -|s r|- o > r ¬-a
  default dneNRK
    :: i -|s r|- o > r ••a
    -- -------------------
    -> i -|s r|- o > r ¬-a
  dneNRK = mapR notNegate


-- Positive negation

class (Core s, Structural s, Control s, Contextual s) => PosNegation s where
  negateL
    :: Neg a
    =>        i -|s r|- o > a
    -- ----------------------
    -> r -a < i -|s r|- o
  negateL = negateLK . kL
  negateLK
    :: Neg a
    => r •a < i -|s r|- o
    -- ------------------
    -> r -a < i -|s r|- o
  negateLK = mapL getNegate
  negateLK'
    :: Neg a
    => r -a < i -|s r|- o
    -- ------------------
    -> r •a < i -|s r|- o
  negateLK' = mapL Negate
  negateL'
    :: Neg a
    => r -a < i -|s r|- o
    -- ----------------------
    ->        i -|s r|- o > a
  negateL' p = negateR init >>> wkR p
  negateR
    :: Neg a
    => a < i -|s r|- o
    -- ----------------------
    ->     i -|s r|- o > r -a
  negateR = negateRK . kR
  negateRK
    :: Neg a
    => i -|s r|- o > r •a
    -- ------------------
    -> i -|s r|- o > r -a
  negateRK = mapR Negate
  negateR'
    :: Neg a
    =>     i -|s r|- o > r -a
    -- ----------------------
    -> a < i -|s r|- o
  negateR' p = wkL p >>> negateL init
  negateRK'
    :: Neg a
    => i -|s r|- o > r -a
    -- ------------------
    -> i -|s r|- o > r •a
  negateRK' = mapR getNegate
  shiftN
    :: Neg a
    => r -a < i -|s r|- o > r
    -- ----------------------
    ->        i -|s r|- o > a
  shiftN = shift . negateLK'

  dnePL
    :: Pos a
    =>     a < i -|s r|- o
    -- -------------------
    -> r -¬a < i -|s r|- o
  default dnePL
    :: (NegNegation s, Pos a)
    =>     a < i -|s r|- o
    -- -------------------
    -> r -¬a < i -|s r|- o
  dnePL = negateL . notR
  dnePLK
    :: Pos a
    => r ••a < i -|s r|- o
    -- -------------------
    -> r -¬a < i -|s r|- o
  default dnePLK
    :: r ••a < i -|s r|- o
    -- -------------------
    -> r -¬a < i -|s r|- o
  dnePLK = mapL getNegateNot
  dnePR
    :: Pos a
    => i -|s r|- o > a
    -- -------------------
    -> i -|s r|- o > r -¬a
  default dnePR
    :: (NegNegation s, Pos a)
    => i -|s r|- o > a
    -- -------------------
    -> i -|s r|- o > r -¬a
  dnePR = negateR . notL
  dnePRK
    :: Pos a
    => i -|s r|- o > r ••a
    -- -------------------
    -> i -|s r|- o > r -¬a
  default dnePRK
    :: i -|s r|- o > r ••a
    -- -------------------
    -> i -|s r|- o > r -¬a
  dnePRK = mapR negateNot
