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
import Sequoia.Polarity
import Sequoia.Profunctor.Continuation

-- Corecursion

data Nu e r f = forall x . Pos x => Nu { getNu :: Down (x ~~Fun e r~> f x) ⊗ x }

instance Polarized N (Nu e r f) where

newtype NuF e r f a = NuF { getNuF :: Down (a ~~Fun e r ~> f a) ⊗ a }

instance (Neg (f a), Pos a) => Polarized P (NuF e r f a)

nu :: Pos x => NuF e r f x -> Nu e r f
nu r = Nu (getNuF r)

runNu :: Nu e r f -> Exists r P (NuF e r f)
runNu (Nu r) = Exists (K (• NuF r))
