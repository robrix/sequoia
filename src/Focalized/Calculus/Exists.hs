{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}
module Focalized.Calculus.Exists
( -- * Existential quantification
  Existential(..)
, existsL'
  -- * Connectives
, module Focalized.Exists
) where

import Focalized.Calculus.Context
import Focalized.Calculus.Core
import Focalized.Exists
import Focalized.Polarity
import Focalized.Quantification
import Prelude hiding (init)

-- Existential quantification

class Existential s where
  existsL
    :: (forall x . Polarized n x => f x < i -|s r|- o)
    -- -----------------------------------------------
    ->                   Exists r n f   < i -|s r|- o

  existsR
    :: (Polarized n x, Pos (f x))
    => i -|s r|- o >            f x
    -- ----------------------------
    -> i -|s r|- o > Exists r n f


existsL'
  :: (Weaken s, Exchange s, Existential s, (Polarized n ==> Pos) f)
  =>                   Exists r n f   < i -|s r|- o
  -- -----------------------------------------------
  -> (forall x . Polarized n x => f x < i -|s r|- o)
existsL' p = existsR init >>> wkL' p
