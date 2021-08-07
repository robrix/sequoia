module Sequoia.Profunctor.Exp.Par
( Exp(..)
) where

import Sequoia.Calculus.Not
import Sequoia.Calculus.NotUntrue
import Sequoia.Calculus.Par

newtype Exp e r a b = Exp { getExp :: a ¬ r ⅋ e ≁ b }
