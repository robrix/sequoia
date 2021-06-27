{-# LANGUAGE ConstraintKinds #-}
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
, notL'
, notR'
, shiftP
, dneN
, dniN
, dneNK
, dniNK
, notLK
, notRK
, notLK'
, notRK'
  -- * Negate
, type (-)(..)
, negateNot
, getNegateNot
, type (-¬)
  -- * Positive negation
, PosNegation(..)
, negateL'
, negateR'
, shiftN
, dneP
, dniP
, dnePK
, dniPK
, negateLK
, negateRK
, negateLK'
, negateRK'
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


dneN
  :: (NegNegation s, PosNegation s, Neg a)
  =>     a < i -|s r|- o
  -- -------------------
  -> r ¬-a < i -|s r|- o
dneN = notL . negateR

dniN
  :: (NegNegation s, PosNegation s, Neg a)
  => i -|s r|- o > a
  -- -------------------
  -> i -|s r|- o > r ¬-a
dniN = notR . negateL


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


-- Positive negation

class PosNegation s where
  negateL
    :: Neg a
    =>        i -|s r|- o > a
    -- ----------------------
    -> r -a < i -|s r|- o
  negateR
    :: Neg a
    => a < i -|s r|- o
    -- ----------------------
    ->     i -|s r|- o > r -a


negateL'
  :: (PosNegation s, Weaken s, Neg a)
  => r -a < i -|s r|- o
  -- ----------------------
  ->        i -|s r|- o > a
negateL' p = negateR init >>> wkR p

negateR'
  :: (PosNegation s, Weaken s, Neg a)
  =>     i -|s r|- o > r -a
  -- ----------------------
  -> a < i -|s r|- o
negateR' p = wkL p >>> negateL init


shiftN
  :: (Control s, Contextual s)
  => r -a < i -|s r|- o > r
  -- ----------------------
  ->        i -|s r|- o > a
shiftN = shift . negateLK'


dneP
  :: (NegNegation s, PosNegation s, Pos a)
  =>     a < i -|s r|- o
  -- -------------------
  -> r -¬a < i -|s r|- o
dneP = negateL . notR

dniP
  :: (NegNegation s, PosNegation s, Pos a)
  => i -|s r|- o > a
  -- -------------------
  -> i -|s r|- o > r -¬a
dniP = negateR . notL


dnePK
  :: Contextual s
  => r ••a < i -|s r|- o
  -- -------------------
  -> r -¬a < i -|s r|- o
dnePK = mapL getNegateNot

dniPK
  :: Contextual s
  => i -|s r|- o > r ••a
  -- -------------------
  -> i -|s r|- o > r -¬a
dniPK = mapR negateNot


negateLK
  :: Contextual s
  => r •a < i -|s r|- o
  -- ------------------
  -> r -a < i -|s r|- o
negateLK = mapL getNegate

negateRK
  :: Contextual s
  => i -|s r|- o > r •a
  -- ------------------
  -> i -|s r|- o > r -a
negateRK = mapR Negate


negateLK'
  :: Contextual s
  => r -a < i -|s r|- o
  -- ------------------
  -> r •a < i -|s r|- o
negateLK' = mapL Negate

negateRK'
  :: Contextual s
  => i -|s r|- o > r -a
  -- ------------------
  -> i -|s r|- o > r •a
negateRK' = mapR getNegate
