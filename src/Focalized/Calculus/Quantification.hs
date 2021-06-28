{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}
module Focalized.Calculus.Quantification
( -- * Universal quantification
  Universal(..)
, forAllR'
  -- * Existential quantification
, Existential(..)
, existsL'
  -- * Quantified constraints
, ForAllC
  -- * Connectives
, module Focalized.Quantification
) where

import Data.Kind (Constraint)
import Focalized.Calculus.Context
import Focalized.Calculus.Core
import Focalized.Calculus.Negation
import Focalized.Polarity
import Focalized.Quantification
import Prelude hiding (init)

-- Universal quantification

class Universal s where
  forAllL
    :: (Polarized n x, Neg (f x))
    =>        r ¬-f x < i -|s r|- o
    -- ----------------------------
    -> ForAll r n f   < i -|s r|- o

  forAllR
    :: ForAllC (Polarized n) Neg f
    => (forall x . Polarized n x => i -|s r|- o >            f x)
    -- ---------------------------------------
    ->                              i -|s r|- o > ForAll r n f


forAllR'
  :: (Weaken s, Exchange s, Universal s, Negation s, ForAllC (Polarized n) Neg f)
  =>                              i -|s r|- o > ForAll r n f
  -- ---------------------------------------
  -> (forall x . Polarized n x => i -|s r|- o >            f x)
forAllR' p = wkR' p >>> forAllL (dneN init)


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
  :: (Weaken s, Exchange s, Existential s, ForAllC (Polarized n) Pos f)
  =>                   Exists r n f   < i -|s r|- o
  -- -----------------------------------------------
  -> (forall x . Polarized n x => f x < i -|s r|- o)
existsL' p = existsR init >>> wkL' p


-- Quantified constraints

type ForAllC cx cf f = (forall x . cx x => cf (f x)) :: Constraint
