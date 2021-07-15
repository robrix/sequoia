module Sequoia.Connective.Implicative
( elimFun
, funPar1
, funPar2
  -- * Connectives
, module Sequoia.Connective.Function
, module Sequoia.Connective.Subtraction
) where

import Sequoia.Bijection
import Sequoia.Connective.Function
import Sequoia.Connective.Not
import Sequoia.Connective.Par
import Sequoia.Connective.Subtraction
import Sequoia.Continuation
import Sequoia.Disjunction
import Sequoia.Functor.K

elimFun :: a ~~r~> b -> a ~-r-< b -> r
elimFun f = (•) <$> appFun f . subA <*> subK

funPar1 :: K r (r ¬a ⅋ b) <-> K r (a ~~r~> b)
funPar1
  =   inK1 (\ k -> k . mkPar (inK k))
  <-> inK1 (. mkFun)

funPar2 :: K r **(r ¬a ⅋ b) <-> K r **(a ~~r~> b)
funPar2
  =   inK1 (\ k f -> k (inK ((f •) . mkFun)))
  <-> inK1 (\ k p -> k (inK ((p •) . mkPar p)))

mkPar :: K r (r ¬a ⅋ b) -> a ~~r~> b -> r ¬a ⅋ b
mkPar p f = inl (inK (\ a -> appFun f a • inK ((p •) . inr)))

mkFun :: r ¬a ⅋ b -> a ~~r~> b
mkFun p = Fun (inK1 (\ b a -> ((• a) <--> b) p))
