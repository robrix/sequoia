module Sequoia.Connective.Mu
( -- * Recursion
  Mu(..)
, MuF(..)
, mu
, foldMu
, unfoldMu
, refoldMu
) where

import qualified Control.Category as Cat
import           Data.Profunctor.Traversing
import           Sequoia.CPS
import           Sequoia.Connective.Down
import           Sequoia.Connective.Function
import           Sequoia.Connective.Quantification
import           Sequoia.Continuation
import           Sequoia.Functor.K
import           Sequoia.Polarity

-- Recursion

newtype Mu r f = Mu { getMu :: forall x . Neg x => Down (FAlg r f x) ~~r~> x }

type FAlg r f x = f x ~~r~> x

instance Polarized N (Mu r f) where

newtype MuF r f a = MuF { getMuF :: Down (FAlg r f a) ~~r~> a }

instance (Pos (f a), Neg a) => Polarized N (MuF r f a) where

mu :: ForAll r N (MuF r f) -> Mu r f
mu r = Mu (dnE (mapDN getMuF (runForAll r)))

foldMu :: ContPassing (K r) c => Neg a => f a `c` a -> Mu r f `c` a
foldMu alg = inC1 (\ k (Mu f) -> appC f (Down (coerceC alg)) k)

unfoldMu :: (Traversable f, ContPassing (K r) c) => a `c` f a -> a `c` Mu r f
unfoldMu coalg = cps (\ a -> Mu (Fun (inK1 (\ k (Down alg) -> appC (refoldCPS alg (coerceC coalg)) a k))))

refoldMu :: (Traversable f, ContPassing (K r) c, Neg b) => f b `c` b -> a `c` f a -> a `c` b
refoldMu f g = foldMu f Cat.<<< unfoldMu g


coerceC :: (ContPassing k c, ContPassing k d) => c a b -> d a b
coerceC = inC . exC


refoldCPS :: (Cat.Category c, Traversing c, Traversable f) => f b `c` b -> a `c` f a -> a `c` b
refoldCPS f g = go where go = f Cat.<<< traverse' go Cat.<<< g
