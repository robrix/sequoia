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
import           Prelude hiding (exp)
import           Sequoia.Connective.Down
import           Sequoia.Connective.Function
import           Sequoia.Connective.Quantification
import           Sequoia.Optic.Setter
import           Sequoia.Polarity
import           Sequoia.Profunctor.Context
import           Sequoia.Profunctor.Continuation
import           Sequoia.Profunctor.Exponential

-- Recursion

newtype Mu e r f = Mu { getMu :: forall x . Neg x => Down (FAlg e r f x) ~~Fun e r~> x }

type FAlg e r f x = f x ~~Fun e r~> x

instance Polarized N (Mu e r f) where

newtype MuF e r f a = MuF { getMuF :: Down (FAlg e r f a) ~~Fun e r~> a }

instance (Pos (f a), Neg a) => Polarized N (MuF e r f a) where

mu :: ForAll r N (MuF e r f) -> Mu e r f
mu r = Mu (funExp (dnE (over _K (lmap (lmap (getFun . getMuF))) (runForAll r))))

foldMu :: Neg a => f a --|Exp e r|-> a -> Mu e r f --|Exp e r|-> a
foldMu alg = exp (\ k -> val (\ (Mu f) -> k ↓ getFun f ↑ pure (Down (funExp alg))))

unfoldMu :: Traversable f => a --|Exp e r|-> f a -> a --|Exp e r|-> Mu e r f
unfoldMu coalg = exp' (\ a -> Mu (fun (\ k -> val (\ (Down alg) -> k ↓ refoldCat (getFun alg) coalg ↑ pure a))))

refoldMu :: (Traversable f, Neg b) => f b --|Exp e r|-> b -> a --|Exp e r|-> f a -> a --|Exp e r|-> b
refoldMu f g = foldMu f Cat.<<< unfoldMu g


refoldCat :: (Cat.Category c, Traversing c, Traversable f) => f b `c` b -> a `c` f a -> a `c` b
refoldCat f g = go where go = f Cat.<<< traverse' go Cat.<<< g
