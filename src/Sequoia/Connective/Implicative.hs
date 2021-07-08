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

elimFun :: Continuation k => a ~~k~> b -> a ~-k-< b -> KRep k
elimFun f = (•) <$> appFun f . subA <*> subK

funPar1 :: Continuation k => k (k ¬a ⅋ b) <-> k (a ~~k~> b)
funPar1
  =   inK1 (\ k -> k . mkPar (inK k))
  <-> inK1 (. mkFun)

funPar2 :: Continuation k => k **(k ¬a ⅋ b) <-> k **(a ~~k~> b)
funPar2
  =   inK1 (\ k f -> k (inK ((f •) . mkFun)))
  <-> inK1 (\ k p -> k (inK ((p •) . mkPar p)))

mkPar :: Continuation k => k (k ¬a ⅋ b) -> a ~~k~> b -> k ¬a ⅋ b
mkPar p f = inl (inK (\ a -> appFun f a • inK ((p •) . inr)))

mkFun :: Continuation k => k ¬a ⅋ b -> a ~~k~> b
mkFun p = Fun (inK1 (\ b a -> ((• a) <--> b) p))
