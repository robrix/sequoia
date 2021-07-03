{-# LANGUAGE ExistentialQuantification #-}
module Focalized.Connective.Nu
( -- * Corecursion
  Nu(..)
, NuF(..)
, nu
, runNu
) where

import Focalized.Connective.Down
import Focalized.Connective.Function
import Focalized.Connective.Quantification
import Focalized.Connective.Tensor
import Focalized.Continuation
import Focalized.Polarity

-- Corecursion

data Nu k f = forall x . Pos x => Nu { getNu :: Down (x ~~k~> f x) ⊗ x }

instance Polarized N (Nu k f) where

newtype NuF k f a = NuF { getNuF :: Down (a ~~k~> f a) ⊗ a }

instance (Neg (f a), Pos a) => Polarized P (NuF k f a)

nu :: Pos x => NuF k f x -> Nu k f
nu r = Nu (getNuF r)

runNu :: Continuation k => Nu k f -> Exists k P (NuF k f)
runNu (Nu r) = Exists (liftDN (NuF r))
