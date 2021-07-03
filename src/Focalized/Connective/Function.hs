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

import Data.Functor.Contravariant
import Focalized.Continuation
import Focalized.Polarity

-- Implication

appFun :: Continuation k => (a ~~k~> b) -> (a -> k (k b))
appFun (Fun f) = appK1 f

appFun2 :: Continuation k => (a ~~k~> b ~~k~> c) -> (a -> b -> k (k c))
appFun2 f = appK2 (getFun (getFun <$> f))

liftFun :: Continuation k => ((b -> R k) -> (a -> R k)) -> (a ~~k~> b)
liftFun = Fun . inK1

liftFun' :: Continuation k => (a -> (b -> R k) -> R k) -> (a ~~k~> b)
liftFun' = liftFun . flip

dnEFun :: Continuation k => k (k (a ~~k~> b)) -> (a ~~k~> b)
dnEFun = Fun . dnE' . contramap (contramap getFun)

dnE' :: Continuation k => k (k (k b -> k a)) -> (k b -> k a)
dnE' f = inK1 (\ k a -> exK f (inK (\ f -> exK1 f k a)))

newtype Fun k a b = Fun { getFun :: k b -> k a }

instance Contravariant k => Functor (Fun k a) where
  fmap f (Fun r) = Fun (r . contramap f)

instance (Pos a, Neg b) => Polarized N (Fun k a b) where

type a ~~ r = Fun r a
type f ~> b = f b

infixr 6 ~~
infixr 5 ~>
