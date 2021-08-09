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
import           Data.Profunctor
import           Data.Profunctor.Traversing
import           Fresnel.Setter
import           Prelude hiding (exp)
import           Sequoia.Connective.Down
import           Sequoia.Connective.Function
import           Sequoia.Connective.Quantification
import           Sequoia.Polarity
import           Sequoia.Profunctor.Continuation
import           Sequoia.Profunctor.Exp (Exp, dnE, exp, exp', (↑), (↓))

-- Recursion

newtype Mu e r f = Mu { getMu :: forall x . Neg x => Down (FAlg e r f x) ~~Fun r~> x }

type FAlg e r f x = f x ~~Fun r~> x

instance Polarized N (Mu e r f) where

newtype MuF e r f a = MuF { getMuF :: Down (FAlg e r f a) ~~Fun r~> a }

instance (Pos (f a), Neg a) => Polarized N (MuF e r f a) where

mu :: ForAll r N (MuF e r f) -> Mu e r f
mu r = Mu (funExp (dnE (over _K (lmap (lmap (runFunExp . getMuF))) (runForAll r))))

foldMu :: Neg a => f a ~~Exp r~> a -> Mu e r f ~~Exp r~> a
foldMu alg = exp (\ k -> inK (\ (Mu f) -> k ↓ runFunExp f ↑ Down (funExp alg)))

unfoldMu :: Traversable f => a ~~Exp r~> f a -> a ~~Exp r~> Mu e r f
unfoldMu coalg = exp' (\ a -> Mu (fun (\ k (Down alg) -> k ↓ refoldCat (runFunExp alg) coalg ↑ a)))

refoldMu :: (Traversable f, Neg b) => f b ~~Exp r~> b -> a ~~Exp r~> f a -> a ~~Exp r~> b
refoldMu f g = foldMu f Cat.<<< unfoldMu g


refoldCat :: (Cat.Category c, Traversing c, Traversable f) => f b `c` b -> a `c` f a -> a `c` b
refoldCat f g = go where go = f Cat.<<< traverse' go Cat.<<< g
