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
mu r = Mu (dnE (contramap (contramap getMuF) (runForAll r)))

foldMu :: CPS' k c => Neg a => f a `c` a -> Mu k f `c` a
foldMu alg = inC $ inK . \ k (Mu f) -> exK (appFun f (Down (Fun (coerceK1 (exC alg))))) (coerceK k)

unfoldMu :: (Traversable f, CPS' k c) => a `c` f a -> a `c` Mu k f
unfoldMu coalg = cps $ \ a -> Mu $ Fun $ inK . \ k (Down alg) -> exK (exC (refoldCPS alg (coerceC coalg)) k) a

refoldMu :: (Traversable f, CPS' k c, Neg b) => f b `c` b -> a `c` f a -> a `c` b
refoldMu f g = foldMu' f Cat.<<< unfoldMu g
  where
  foldMu' :: (CPS' k c, Neg a) => f a `c` a -> Mu k f `c` a
  foldMu' = foldMu


coerceC :: (CPS' k c, CPS' k d) => c a b -> d a b
coerceC = inC . exC
