module Sequoia.Optic.Prism
( -- * Prisms
  Prism
, Prism'
, prism
, _Left
, _Right
) where

import Data.Profunctor
import Sequoia.Optic.Optic

-- Prisms

type Prism s t a b = forall p . Choice p => Optic p s t a b

type Prism' s a = Prism s s a a

prism :: (b -> t) -> (s -> Either t a) -> Prism s t a b
prism inj prj = dimap prj (either id inj) . right'


_Left :: Prism (Either a b) (Either a' b) a a'
_Left = prism Left (either Right (Left . Right))

_Right :: Prism (Either a b) (Either a b') b b'
_Right = prism Right (either (Left . Left) Right)
