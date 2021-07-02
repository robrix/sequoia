{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}
module Focalized.Connective.Quantification
( -- * Quantified constraints
  type (==>)
  -- * Connectives
, module Focalized.Connective.Exists
, module Focalized.Connective.ForAll
) where

import Data.Kind (Constraint)
import Focalized.Connective.Exists
import Focalized.Connective.ForAll

-- Quantified constraints

type (cx ==> cf) f = (forall x . cx x => cf (f x)) :: Constraint

infix 5 ==>
