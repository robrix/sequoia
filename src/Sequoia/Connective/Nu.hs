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
import Sequoia.Continuation as K
import Sequoia.Polarity

-- Corecursion

data Nu r e f = forall x . Pos x => Nu { getNu :: Down (x ~~Fun r e~> f x) ⊗ x }

instance Polarized N (Nu r e f) where

newtype NuF r e f a = NuF { getNuF :: Down (a ~~Fun r e ~> f a) ⊗ a }

instance (Neg (f a), Pos a) => Polarized P (NuF r e f a)

nu :: Pos x => NuF r e f x -> Nu r e f
nu r = Nu (getNuF r)

runNu :: Nu r e f -> Exists r P (NuF r e f)
runNu (Nu r) = Exists (liftDN (NuF r))
