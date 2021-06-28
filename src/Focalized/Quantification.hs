{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}
module Focalized.Quantification
( -- * Quantified constraints
  type (==>)
  -- * Connectives
, module Focalized.Exists
, module Focalized.ForAll
) where

import Data.Kind (Constraint)
import Focalized.Exists
import Focalized.ForAll

-- Quantified constraints

type (cx ==> cf) f = (forall x . cx x => cf (f x)) :: Constraint

infix 5 ==>
