module Focalized.Function
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
import Focalized.CPS
import Focalized.Polarity

-- Implication

appFun :: (a ~~r~> b) -> a -> (b -> r) -> r
appFun = flip . lowerK . runCPS . getFun

appFun2 :: (a ~~r~> b ~~r~> c) -> a -> b -> (c -> r) -> r
appFun2 f a b = appFun f a . flip (`appFun` b)

liftFun :: ((b -> r) -> (a -> r)) -> a ~~r~> b
liftFun = Fun . CPS . liftK

liftFun' :: (a -> (b -> r) -> r) -> a ~~r~> b
liftFun' = liftFun . flip

dnEFun :: r ••(a ~~r~> b) -> (a ~~r~> b)
dnEFun = Fun . dnE . contramap (contramap getFun)

newtype Fun r a b = Fun { getFun :: CPS r a b }

instance (Pos a, Neg b) => Polarized N (Fun r a b) where

type a ~~ r = Fun r a
type f ~> b = f b

infixr 6 ~~
infixr 5 ~>
