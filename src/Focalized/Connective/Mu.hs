module Focalized.Connective.Mu
( -- * Recursion
  Mu(..)
, MuF(..)
, mu
, foldMu
, unfoldMu
, refoldMu
) where

import qualified Control.Category as Cat
import           Data.Functor.Contravariant
import           Focalized.CPS
import           Focalized.Connective.Down
import           Focalized.Connective.Function
import           Focalized.Connective.Quantification
import           Focalized.Continuation
import           Focalized.Polarity

-- Recursion

newtype Mu r f = Mu { getMu :: forall x . Neg x => Down (FAlg r f x) ~~r~> x }

type FAlg r f x = f x ~~r~> x

instance Polarized N (Mu r f) where

newtype MuF r f a = MuF { getMuF :: Down (FAlg r f a) ~~r~> a }

instance (Pos (f a), Neg a) => Polarized N (MuF r f a) where

mu :: ForAll r N (MuF r f) -> Mu r f
mu r = Mu (dnEFun (contramap (contramap getMuF) (runForAll r)))

foldMu :: Neg a => CPS r (f a) a -> CPS r (Mu r f) a
foldMu alg = liftCPS $ \ (Mu f) -> (appFun f (Down (Fun alg)) •)

unfoldMu :: Traversable f => CPS r a (f a) -> CPS r a (Mu r f)
unfoldMu coalg = cps $ \ a -> Mu $ liftFun' $ \ (Down (Fun alg)) -> runDN (appCPS (refoldCPS alg coalg) a)

refoldMu :: (Traversable f, Neg b) => CPS r (f b) b -> CPS r a (f a) -> CPS r a b
refoldMu f g = foldMu f Cat.<<< unfoldMu g
