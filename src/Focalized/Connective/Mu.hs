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

mu :: Continuation k => ForAll k N (MuF k f) -> Mu k f
mu r = Mu (dnEFun (contramap (contramap getMuF) (runForAll r)))

foldMu :: Continuation k => Neg a => CPS k (f a) a -> CPS k (Mu k f) a
foldMu (CPS alg) = CPS $ inK . \ k (Mu f) -> exK (appFun f (Down (Fun (coerceK1 alg)))) (coerceK k)

unfoldMu :: (Traversable f, Continuation k) => CPS k a (f a) -> CPS k a (Mu k f)
unfoldMu coalg = cps $ \ a -> Mu $ liftFun' $ \ (Down (Fun alg)) -> runDN0 (appCPS (refoldCPS (CPS alg) coalg) a)

refoldMu :: (Traversable f, Continuation k, Neg b) => CPS k (f b) b -> CPS k a (f a) -> CPS k a b
refoldMu f g = foldMu' f Cat.<<< unfoldMu g
  where
  foldMu' :: (Continuation k, Neg a) => CPS k (f a) a -> CPS k (Mu k f) a
  foldMu' = foldMu
