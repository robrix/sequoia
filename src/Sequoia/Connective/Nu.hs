{-# LANGUAGE ExistentialQuantification #-}
module Sequoia.Connective.Nu
( -- * Corecursion
  Nu(..)
, NuF(..)
, nu
, runNu
) where

import Sequoia.Connective.Down
import Sequoia.Connective.Function
import Sequoia.Connective.Quantification
import Sequoia.Connective.Tensor
import Sequoia.Continuation
import Sequoia.Polarity

-- Corecursion

data Nu k f = forall x . Pos x => Nu { getNu :: Down (x ~~k~> f x) ⊗ x }

instance Polarized N (Nu k f) where

newtype NuF k f a = NuF { getNuF :: Down (a ~~k~> f a) ⊗ a }

instance (Neg (f a), Pos a) => Polarized P (NuF k f a)

nu :: Pos x => NuF k f x -> Nu k f
nu r = Nu (getNuF r)

runNu :: Continuation k => Nu k f -> Exists k P (NuF k f)
runNu (Nu r) = Exists (liftDN (NuF r))
