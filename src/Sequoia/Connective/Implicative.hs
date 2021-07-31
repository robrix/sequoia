module Sequoia.Connective.Implicative
( elimFun
, funPar1
, funPar2
  -- * Connectives
, module Sequoia.Connective.Function
, module Sequoia.Connective.Subtraction
) where

import Data.Profunctor
import Fresnel.Iso
import Sequoia.Connective.Function
import Sequoia.Connective.Not
import Sequoia.Connective.NotUntrue
import Sequoia.Connective.Par
import Sequoia.Connective.Subtraction
import Sequoia.Disjunction
import Sequoia.Profunctor.Context
import Sequoia.Profunctor.Continuation
import Sequoia.Profunctor.Exponential
import Sequoia.Profunctor.Value

elimFun :: a ~~Fun e r~> b -> b >-Sub e r-~ a -> e ==> r
elimFun f = elimExp (runFunExp f) . getSub

funPar1 :: Iso' (e ∘ (r ¬a ⅋ b) • r) (e ∘ (a ~~Fun e r~> b) • r)
funPar1 = iso
  (\ k -> K ((k •) . (mkPar (inrK (lmap pure k)) =<<)))
  (\ k -> K ((k •) . fmap mkFun))

funPar2 :: Iso' (e ∘ (r ¬a ⅋ b) • r • r) (e ∘ (a ~~Fun e r~> b) • r • r)
funPar2 = iso
  (lmap (\ f -> K ((f •) . fmap mkFun)))
  (lmap (\ p -> K ((p •) . (mkPar (inrK (lmap pure p)) =<<))))

mkPar :: b • r -> a ~~Fun e r~> b -> e ∘ (r ¬a ⅋ b)
mkPar p f = V (\ e -> inl (Not (K (\ a -> p ↓ runFunExp f ↑ pure a <== e))))

mkFun :: r ¬a ⅋ b -> a ~~Fun e r~> b
mkFun p = fun (\ b a -> C (\ e -> ((•¬ e ∘≁ a) <--> (b •¬)) p))
