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
import Sequoia.Disjunction

elimPar :: a ⅋ b -> Negate e a r ⊗ Negate e b r -> r
elimPar = (. exl) . flip (•-) <--> (. exr) . flip (•-)

elimTensor :: a ⊗ b -> a ¬ r ⅋ b ¬ r -> r
elimTensor = flip ((. exl) . (•¬) <--> (. exr) . (•¬))
