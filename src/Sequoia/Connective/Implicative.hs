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
import Sequoia.Connective.Par
import Sequoia.Connective.Subtraction
import Sequoia.Disjunction
import Sequoia.Profunctor
import Sequoia.Profunctor.Continuation
import Sequoia.Profunctor.Exp (elimExp, (↑), (↓))

elimFun :: a ~~Fun r~> b -> b >-Sub r-~ a -> r
elimFun f s = elimExp (runFunExp f) • runSubCoexp s

funPar1 :: Iso' ((a ¬ r ⅋ b) • r) ((a ~~Fun r~> b) • r)
funPar1 = iso
  (\ k -> k <<^ mkPar (inrL k))
  (<<^ mkFun)

funPar2 :: Iso' ((a ¬ r ⅋ b) •• r) ((a ~~Fun r~> b) •• r)
funPar2 = iso
  (<<^ (<<^ mkFun))
  (<<^ (\ k -> k <<^ mkPar (inrL k)))

mkPar :: b • r -> a ~~Fun r~> b -> (a ¬ r ⅋ b)
mkPar p f = inl (inK (\ a -> p ↓ runFunExp f ↑ a))

mkFun :: a ¬ r ⅋ b -> a ~~Fun r~> b
mkFun p = fun (\ b a -> ((• a) <--> (b •)) p)
