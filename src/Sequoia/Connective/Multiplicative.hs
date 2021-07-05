module Sequoia.Connective.Multiplicative
( elimPar
, elimTensor
  -- * Connectives
, module Sequoia.Connective.Bottom
, module Sequoia.Connective.One
, module Sequoia.Connective.Par
, module Sequoia.Connective.Tensor
) where

import Sequoia.Conjunction
import Sequoia.Connective.Bottom
import Sequoia.Connective.Negation
import Sequoia.Connective.One
import Sequoia.Connective.Par
import Sequoia.Connective.Tensor
import Sequoia.Continuation
import Sequoia.Disjunction

elimPar :: Representable k => a ⅋ b -> k -a ⊗ k -b -> Rep k
elimPar = (. exl) . flip (•) <--> (. exr) . flip (•)

elimTensor :: Representable k => a ⊗ b -> k ¬a ⅋ k ¬b -> Rep k
elimTensor = flip ((. exl) . (•) <--> (. exr) . (•))
