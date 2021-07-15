module Sequoia.Connective.Function
( -- * Implication
  appFun
, appFun2
, Fun(..)
, type (~~)
, type (~>)
) where

import qualified Control.Category as Cat
import           Data.Kind (Type)
import           Data.Profunctor
import           Data.Profunctor.Traversing
import           Sequoia.Continuation
import           Sequoia.Functor.K
import           Sequoia.Functor.V
import           Sequoia.Polarity
import           Sequoia.Profunctor.D

-- Implication

appFun :: (a ~~Fun r e~> b) -> V e (V e a -> K r **b)
appFun = appD

appFun2 :: (a ~~Fun r e~> b ~~Fun r e~> c) -> V e (V e a -> V e b -> K r **c)
appFun2 = appD2

newtype Fun r e a b = Fun { getFun :: V e a -> K r b -> Context r e }
  deriving (Cat.Category, Choice, Dual r e, Profunctor, Strong, Traversing) via D r e
  deriving (Functor) via D r e a

instance (Pos a, Neg b) => Polarized N (Fun r e a b) where

type l ~~(r :: Type -> Type -> Type) = r l
type l~> r = l r

infixr 6 ~~
infixr 5 ~>
