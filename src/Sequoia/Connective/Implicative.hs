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

elimFun :: Representable k => a ~~k~> b -> a ~-k-< b -> Rep k
elimFun f = (•) <$> appFun f . subA <*> subK

funPar1 :: Representable k => k (k ¬a ⅋ b) <-> k (a ~~k~> b)
funPar1
  =   inK1 (\ k f -> k (inl (inK (\ a -> appFun f a • inK (k . inr)))))
  <-> inK1 (\ k p -> k (Fun (inK1 (\ b a -> ((• a) <--> b) p))))

funPar2 :: Representable k => k **(k ¬a ⅋ b) <-> k **(a ~~k~> b)
funPar2
  =   inK1 (\ k f -> k (inK (\ p -> f • Fun (inK1 (\ b a -> ((• a) <--> b) p)))))
  <-> inK1 (\ k p -> k (inK (\ f -> p • inl (inK (\ a -> appFun f a • inK ((p •) . inr))))))
