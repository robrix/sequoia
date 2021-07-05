module Sequoia.Connective.Function
( -- * Implication
  appFun
, appFun2
, liftFun
, liftFun'
, Fun(..)
, type (~~)
, type (~>)
) where

import qualified Control.Category as Cat
import           Data.Functor.Contravariant
import           Data.Profunctor
import           Data.Profunctor.Traversing
import           Sequoia.CPS
import           Sequoia.Continuation
import           Sequoia.Polarity

-- Implication

appFun :: Representable k => (a ~~k~> b) -> (a -> k **b)
appFun = (-<<) . getFun

appFun2 :: Representable k => (a ~~k~> b ~~k~> c) -> (a -> b -> k **c)
appFun2 f = appK2 (getFun (getFun <$> f))

liftFun :: Representable k => ((b -> Rep k) -> (a -> Rep k)) -> (a ~~k~> b)
liftFun = Fun . inK1

liftFun' :: Representable k => (a -> (b -> Rep k) -> Rep k) -> (a ~~k~> b)
liftFun' = liftFun . flip

newtype Fun k a b = Fun { getFun :: k b -> k a }
  deriving (Cat.Category, Choice, Profunctor, Strong, Traversing) via ViaCPS (Fun k) k

instance Representable k => CPS k (Fun k) where
  inC = Fun
  exC = getFun

instance Contravariant k => Functor (Fun k a) where
  fmap f (Fun r) = Fun (r . contramap f)

instance (Pos a, Neg b) => Polarized N (Fun k a b) where

type a ~~ r = Fun r a
type f ~> b = f b

infixr 6 ~~
infixr 5 ~>
