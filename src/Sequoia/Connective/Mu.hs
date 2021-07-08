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
import           Sequoia.Polarity

-- Recursion

newtype Mu k f = Mu { getMu :: forall x . Neg x => Down (FAlg k f x) ~~k~> x }

type FAlg k f x = f x ~~k~> x

instance Polarized N (Mu k f) where

newtype MuF k f a = MuF { getMuF :: Down (FAlg k f a) ~~k~> a }

instance (Pos (f a), Neg a) => Polarized N (MuF k f a) where

mu :: Continuation k => ForAll k N (MuF k f) -> Mu k f
mu r = Mu (dnE (mapDN getMuF (runForAll r)))

foldMu :: ContPassing k c => Neg a => f a `c` a -> Mu k f `c` a
foldMu alg = inC1 (\ k (Mu f) -> appC f (Down (coerceC alg)) k)

unfoldMu :: (Traversable f, ContPassing k c) => a `c` f a -> a `c` Mu k f
unfoldMu coalg = cps (\ a -> Mu (Fun (inK1 (\ k (Down alg) -> appC (refoldCPS alg (coerceC coalg)) a k))))

refoldMu :: (Traversable f, ContPassing k c, Neg b) => f b `c` b -> a `c` f a -> a `c` b
refoldMu f g = foldMu f Cat.<<< unfoldMu g


coerceC :: (ContPassing k c, ContPassing k d) => c a b -> d a b
coerceC = inC . exC


refoldCPS :: (Cat.Category c, Traversing c, Traversable f) => f b `c` b -> a `c` f a -> a `c` b
refoldCPS f g = go where go = f Cat.<<< traverse' go Cat.<<< g
