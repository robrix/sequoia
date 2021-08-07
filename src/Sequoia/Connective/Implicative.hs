module Sequoia.Connective.Implicative
( elimFun
, funPar1
, funPar2
  -- * Connectives
, module Sequoia.Connective.Function
, module Sequoia.Connective.Subtraction
) where

import Fresnel.Iso
import Sequoia.Connective.Function
import Sequoia.Connective.Not
import Sequoia.Connective.NotUntrue
import Sequoia.Connective.Par
import Sequoia.Connective.Subtraction
import Sequoia.Disjunction
import Sequoia.Profunctor
import Sequoia.Profunctor.Context
import Sequoia.Profunctor.Continuation
import Sequoia.Profunctor.Exponential
import Sequoia.Profunctor.Value

elimFun :: a ~~Fun e r~> b -> b >-Sub e r-~ a -> e ==> r
elimFun f = elimExp (runFunExp f) . runSubCoexp

funPar1 :: Iso' (e ∘ (a ¬ r ⅋ b) • r) (e ∘ (a ~~Fun e r~> b) • r)
funPar1 = iso
  (\ k -> k <<^ (mkPar (inrL (k <<^ pure)) =<<))
  (<<^ fmap mkFun)

funPar2 :: Iso' (e ∘ (a ¬ r ⅋ b) •• r) (e ∘ (a ~~Fun e r~> b) •• r)
funPar2 = iso
  (<<^ (<<^ fmap mkFun))
  (<<^ (\ k -> k <<^ (mkPar (inrL (k <<^ pure)) =<<)))

mkPar :: b • r -> a ~~Fun e r~> b -> e ∘ (a ¬ r ⅋ b)
mkPar p f = V (\ e -> inl (Not (K (\ a -> p ↓ runFunExp f ↑ pure a <== e))))

mkFun :: a ¬ r ⅋ b -> a ~~Fun e r~> b
mkFun p = fun (\ b a -> C (\ e -> ((• e ∘≁ a) <--> (b •)) p))
