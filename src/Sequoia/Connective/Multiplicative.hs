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

elimPar :: Continuation k => a ⅋ b -> (k -a) z ⊗ (k -b) z -> KRep k z
elimPar = (. exl) . flip (•) <--> (. exr) . flip (•)

elimTensor :: Continuation k => a ⊗ b -> (k ¬a) z ⅋ (k ¬b) z -> KRep k z
elimTensor = flip ((. exl) . (•) <--> (. exr) . (•))
