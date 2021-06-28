module Focalized.Calculus.Negate
( -- * Positive negation
  PosNegation(..)
, negateL'
, negateR'
, shiftN
, dnePK
, dniPK
, negateLK
, negateRK
, negateLK'
, negateRK'
  -- * Connectives
, module Focalized.Negate
) where

import Focalized.CPS
import Focalized.Calculus.Context
import Focalized.Calculus.Control
import Focalized.Calculus.Core
import Focalized.Negate
import Focalized.Negation
import Focalized.Polarity
import Prelude hiding (init)

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
