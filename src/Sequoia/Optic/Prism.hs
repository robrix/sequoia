module Sequoia.Optic.Prism
( -- * Prisms
  Prism
, prism
, _Left
, _Right
) where

import Data.Profunctor
import Sequoia.Bijection

-- Prisms

type Prism s t a b = forall p . Choice p => Optic p s t a b

prism :: (b -> t) -> (s -> Either t a) -> Prism s t a b
prism inj prj = dimap prj (either id inj) . right'


_Left :: Prism (Either a b) (Either a' b) a a'
_Left = prism Left (either Right (Left . Right))

_Right :: Prism (Either a b) (Either a b') b b'
_Right = prism Right (either (Left . Left) Right)
