module Sequoia.Connective.Implicative
( elimFun
, funPar1
, funPar2
  -- * Connectives
, module Sequoia.Connective.Function
, module Sequoia.Connective.Subtraction
) where

import Data.Functor.Contravariant
import Sequoia.Connective.Function
import Sequoia.Connective.Not
import Sequoia.Connective.Par
import Sequoia.Connective.Subtraction
import Sequoia.Continuation
import Sequoia.Disjunction
import Sequoia.Functor.K
import Sequoia.Functor.V
import Sequoia.Optic.Iso
import Sequoia.Profunctor.Context
import Sequoia.Profunctor.Exponential
import Sequoia.Value

elimFun :: a ~~Fun e r~> b -> b >-Sub e r-~ a -> C e r
elimFun = elimExp

funPar1 :: K r (V e (r ¬a ⅋ b)) <-> K r (V e (a ~~Fun e r~> b))
funPar1
  =   (\ k -> K (runK k . (mkPar (inrK (contramap inV0 k)) =<<)))
  <-> (\ k -> K (runK k . fmap mkFun))

funPar2 :: K r (K r (V e (r ¬a ⅋ b))) <-> K r (K r (V e (a ~~Fun e r~> b)))
funPar2
  =   contramap (\ f -> K ((f •) . fmap mkFun))
  <-> contramap (\ p -> K ((p •) . (mkPar (inrK (contramap inV0 p)) =<<)))

mkPar :: K r b -> a ~~Fun e r~> b -> V e (r ¬a ⅋ b)
mkPar p f = V (\ e -> inl (Not (K (\ a -> runC (exExp f (inV0 a) p) e))))

mkFun :: r ¬a ⅋ b -> a ~~Fun e r~> b
mkFun p = inExp (\ a b -> ((•∘ a) <--> (b ••)) p)
