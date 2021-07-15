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
import           Sequoia.Connective.Down
import           Sequoia.Connective.Function
import           Sequoia.Connective.Quantification
import           Sequoia.Continuation
import           Sequoia.Polarity
import           Sequoia.Profunctor.ControlPassing
import           Sequoia.Value

-- Recursion

newtype Mu e r f = Mu { getMu :: forall x . Neg x => Down (FAlg e r f x) ~~Fun e r~> x }

type FAlg e r f x = f x ~~Fun e r~> x

instance Polarized N (Mu e r f) where

newtype MuF e r f a = MuF { getMuF :: Down (FAlg e r f a) ~~Fun e r~> a }

instance (Pos (f a), Neg a) => Polarized N (MuF e r f a) where

mu :: ForAll r N (MuF e r f) -> Mu e r f
mu r = Mu (dnE (mapDN getMuF (runForAll r)))

foldMu :: ControlPassing e r d => Neg a => f a `d` a -> Mu e r f `d` a
foldMu alg = inD (\ v k -> val (\ (Mu f) -> exD f (inV0 (Down (coerceD alg))) k) v)

unfoldMu :: (Traversable f, ControlPassing e r d) => a `d` f a -> a `d` Mu e r f
unfoldMu coalg = inD' (\ a -> Mu (inD (\ v k -> val (\ (Down alg) -> exD (refoldCat alg (coerceD coalg)) (inV0 a) k) v)))

refoldMu :: (Traversable f, ControlPassing e r d, Neg b) => f b `d` b -> a `d` f a -> a `d` b
refoldMu f g = foldMu f Cat.<<< unfoldMu g


refoldCat :: (Cat.Category c, Traversing c, Traversable f) => f b `c` b -> a `c` f a -> a `c` b
refoldCat f g = go where go = f Cat.<<< traverse' go Cat.<<< g
