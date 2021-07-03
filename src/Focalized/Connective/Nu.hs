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

data Nu r f = forall x . Pos x => Nu { getNu :: Down (x ~~r~> f x) ⊗ x }

instance Polarized N (Nu r f) where

newtype NuF r f a = NuF { getNuF :: Down (a ~~r~> f a) ⊗ a }

instance (Neg (f a), Pos a) => Polarized P (NuF r f a)

nu :: Pos x => NuF r f x -> Nu r f
nu r = Nu (getNuF r)

runNu :: Nu r f -> Exists r P (NuF r f)
runNu (Nu r) = Exists (liftDN0 (NuF r))
