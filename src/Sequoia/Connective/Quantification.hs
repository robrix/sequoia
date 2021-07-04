{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}
module Sequoia.Connective.Quantification
( -- * Quantified constraints
  type (==>)
  -- * Connectives
, module Sequoia.Connective.Exists
, module Sequoia.Connective.ForAll
) where

import Data.Kind (Constraint)
import Sequoia.Connective.Exists
import Sequoia.Connective.ForAll

-- Quantified constraints

type (cx ==> cf) f = (forall x . cx x => cf (f x)) :: Constraint

infix 5 ==>
