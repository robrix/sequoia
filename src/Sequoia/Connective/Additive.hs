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
import Sequoia.Disjunction

elimWith :: a & b -> r -a ⊕ r -b -> r
elimWith = flip ((. exl) . (•-) <--> (. exr) . (•-))

elimSum :: a ⊕ b -> r ¬a & r ¬b -> r
elimSum = (. exl) . flip (•¬) <--> (. exr) . flip (•¬)
