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
import           Sequoia.Functor.Continuation
import           Sequoia.Functor.Value
import           Sequoia.Polarity
import           Sequoia.Profunctor.Context
import           Sequoia.Profunctor.Exponential

-- Implication

appFun :: (a ~~Fun e r~> b) -> V e (V e a -> K r (K r b))
appFun = appExp

appFun2 :: (a ~~Fun e r~> b ~~Fun e r~> c) -> V e (V e a -> V e b -> K r (K r c))
appFun2 = appExp2

newtype Fun e r a b = Fun { getFun :: V e a -> K r b -> C e r }
  deriving (Exponential) via Exp
  deriving (Cat.Category, Choice, Profunctor, Strong, Traversing) via Exp e r
  deriving (Functor) via Exp e r a

instance (Pos a, Neg b) => Polarized N (Fun e r a b) where

type l ~~(r :: Type -> Type -> Type) = r l
type l~> r = l r

infixr 6 ~~
infixr 5 ~>
