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
import           Sequoia.Profunctor.D
import           Sequoia.Value

-- Recursion

newtype Mu r e f = Mu { getMu :: forall x . Neg x => Down (FAlg r e f x) ~~Fun r e~> x }

type FAlg r e f x = f x ~~Fun r e~> x

instance Polarized N (Mu r e f) where

newtype MuF r e f a = MuF { getMuF :: Down (FAlg r e f a) ~~Fun r e~> a }

instance (Pos (f a), Neg a) => Polarized N (MuF r e f a) where

mu :: ForAll r N (MuF r e f) -> Mu r e f
mu r = Mu (dnE (mapDN getMuF (runForAll r)))

foldMu :: Dual r e d => Neg a => f a `d` a -> Mu r e f `d` a
foldMu alg = inD (\ v k -> withVal (\ (Mu f) -> exD f (inV0 (Down (coerceD alg))) k) v)

unfoldMu :: (Traversable f, Dual r e d) => a `d` f a -> a `d` Mu r e f
unfoldMu coalg = inD' (\ a -> Mu (inD (\ v k -> withVal (\ (Down alg) -> exD (refoldCPS alg (coerceD coalg)) (inV0 a) k) v)))

refoldMu :: (Traversable f, Dual r e d, Neg b) => f b `d` b -> a `d` f a -> a `d` b
refoldMu f g = foldMu f Cat.<<< unfoldMu g


refoldCPS :: (Cat.Category c, Traversing c, Traversable f) => f b `c` b -> a `c` f a -> a `c` b
refoldCPS f g = go where go = f Cat.<<< traverse' go Cat.<<< g
