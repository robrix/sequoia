module Sequoia.Connective.Implicative
( elimFun
, funPar1
, funPar2
  -- * Connectives
, module Sequoia.Connective.Function
, module Sequoia.Connective.Subtraction
) where

import Data.Profunctor
import Sequoia.Connective.Function
import Sequoia.Connective.Not
import Sequoia.Connective.Par
import Sequoia.Connective.Subtraction
import Sequoia.Disjunction
import Sequoia.Optic.Iso
import Sequoia.Profunctor.Context
import Sequoia.Profunctor.Continuation
import Sequoia.Profunctor.Exponential
import Sequoia.Profunctor.Value

elimFun :: a ~~Fun e r~> b -> b >-Sub e r-~ a -> C e r
elimFun = elimExp

funPar1 :: K (V e (r ¬a ⅋ b)) r <-> K (V e (a ~~Fun e r~> b)) r
funPar1
  =   (\ k -> K ((k •) . (mkPar (inrK (lmap inV0 k)) =<<)))
  <-> (\ k -> K ((k •) . fmap mkFun))

funPar2 :: K (K (V e (r ¬a ⅋ b)) r) r <-> K (K (V e (a ~~Fun e r~> b)) r) r
funPar2
  =   lmap (\ f -> K ((f •) . fmap mkFun))
  <-> lmap (\ p -> K ((p •) . (mkPar (inrK (lmap inV0 p)) =<<)))

mkPar :: K b r -> a ~~Fun e r~> b -> V e (r ¬a ⅋ b)
mkPar p f = V (\ e -> inl (Not (K (\ a -> runC (exExp f (inV0 a) p) e))))

mkFun :: r ¬a ⅋ b -> a ~~Fun e r~> b
mkFun p = inExp (\ a b -> ((•∘ a) . getNot <--> (b ••)) p)
