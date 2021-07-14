module Sequoia.Connective.Additive
( -- * Duals
  elimWith
, elimSum
  -- * Connectives
, module Sequoia.Connective.Sum
, module Sequoia.Connective.Top
, module Sequoia.Connective.With
, module Sequoia.Connective.Zero
) where

import Sequoia.Conjunction
import Sequoia.Connective.Negation
import Sequoia.Connective.Sum
import Sequoia.Connective.Top
import Sequoia.Connective.With
import Sequoia.Connective.Zero
import Sequoia.Continuation as K
import Sequoia.Disjunction

elimWith :: K.Representable k => a & b -> k -a ⊕ k -b -> KRep k
elimWith = flip ((. exl) . (•) <--> (. exr) . (•))

elimSum :: K.Representable k => a ⊕ b -> k ¬a & k ¬b -> KRep k
elimSum = (. exl) . flip (•) <--> (. exr) . flip (•)
