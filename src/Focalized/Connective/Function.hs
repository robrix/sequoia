module Focalized.Connective.Function
( -- * Implication
  appFun
, appFun2
, liftFun
, liftFun'
, dnEFun
, Fun(..)
, type (~~)
, type (~>)
) where

import qualified Control.Category as Cat
import           Data.Functor.Contravariant
import           Data.Profunctor
import           Focalized.CPS
import           Focalized.Continuation
import           Focalized.Polarity

-- Implication

appFun :: Continuation k => (a ~~k~> b) -> (a -> k **b)
appFun (Fun f) = appK1 f

appFun2 :: Continuation k => (a ~~k~> b ~~k~> c) -> (a -> b -> k **c)
appFun2 f = appK2 (getFun (getFun <$> f))

liftFun :: Continuation k => ((b -> R k) -> (a -> R k)) -> (a ~~k~> b)
liftFun = Fun . inK1

liftFun' :: Continuation k => (a -> (b -> R k) -> R k) -> (a ~~k~> b)
liftFun' = liftFun . flip

dnEFun :: Continuation k => k **(a ~~k~> b) -> (a ~~k~> b)
dnEFun = dnE

newtype Fun k a b = Fun { getFun :: k b -> k a }
  deriving (Cat.Category, Profunctor) via ViaCPS (Fun k)

instance Continuation k => CPS' k (Fun k) where
  inC = Fun
  exC = getFun

instance Contravariant k => Functor (Fun k a) where
  fmap f (Fun r) = Fun (r . contramap f)

instance (Pos a, Neg b) => Polarized N (Fun k a b) where

type a ~~ r = Fun r a
type f ~> b = f b

infixr 6 ~~
infixr 5 ~>
