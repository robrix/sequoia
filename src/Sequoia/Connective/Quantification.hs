{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}
module Sequoia.Connective.Quantification
( -- * Adjunction
  leftAdjunct
  -- * Quantified constraints
, type (==>)
  -- * Connectives
, module Sequoia.Connective.Exists
, module Sequoia.Connective.ForAll
) where

import Data.Kind (Constraint)
import Sequoia.Connective.Exists
import Sequoia.Connective.ForAll
import Sequoia.Polarity

-- Adjunction

leftAdjunct :: (forall x . Exists r p a -> b x) -> (forall x . Polarized p x => a x -> ForAll r p b)
leftAdjunct f a = forAll (f (exists a))


-- Quantified constraints

type (cx ==> cf) f = (forall x . cx x => cf (f x)) :: Constraint

infix 5 ==>
