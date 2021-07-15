module Sequoia.Connective.Function
( -- * Implication
  appFun
, appFun2
, Fun(..)
, type (~~)
, type (~>)
) where

import qualified Control.Category as Cat
import           Data.Profunctor
import           Data.Profunctor.Traversing
import           Sequoia.CPS
import           Sequoia.Continuation
import           Sequoia.Functor.K
import           Sequoia.Polarity

-- Implication

appFun :: (a ~~r~> b) -> (a -> K r **b)
appFun = (-<<) . getFun

appFun2 :: (a ~~r~> b ~~r~> c) -> (a -> b -> K r **c)
appFun2 f a b = inDN (appC2 f a b)

newtype Fun r a b = Fun { getFun :: K r b -> K r a }
  deriving (Cat.Category, Choice, Profunctor, Strong, Traversing) via C (K r)

instance ContPassing (K r) (Fun r) where
  inC = Fun
  exC = getFun

instance Functor (Fun r a) where
  fmap f (Fun r) = Fun (r . contramap f)

instance (Pos a, Neg b) => Polarized N (Fun r a b) where

type a ~~ r = Fun r a
type f ~> b = f b

infixr 6 ~~
infixr 5 ~>
