{-# LANGUAGE ExistentialQuantification #-}
module Focalized.Nu
( -- * Corecursion
  Nu(..)
, NuF(..)
, nu
, runNu
) where

import Focalized.CPS
import Focalized.Down
import Focalized.Function
import Focalized.Polarity
import Focalized.Quantification
import Focalized.Tensor

-- Corecursion

data Nu r f = forall x . Pos x => Nu { getNu :: Down (x ~~r~> f x) ⊗ x }

instance Polarized N (Nu r f) where

newtype NuF r f a = NuF { getNuF :: Down (a ~~r~> f a) ⊗ a }

instance (Neg (f a), Pos a) => Polarized P (NuF r f a)

nu :: Pos x => NuF r f x -> Nu r f
nu r = Nu (getNuF r)

runNu :: Nu r f -> Exists r P (NuF r f)
runNu (Nu r) = Exists (dnI (NuF r))
