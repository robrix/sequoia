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
import Focalized.CPS
import Focalized.Continuation
import Focalized.Polarity

-- Implication

appFun :: (a ~~r~> b) -> a -> r ••b
appFun = appCPS . getFun

appFun2 :: (a ~~r~> b ~~r~> c) -> (a -> b -> r ••c)
appFun2 = appCPS2 . fmap getFun . getFun

liftFun :: ((b -> r) -> (a -> r)) -> (a ~~r~> b)
liftFun = Fun . CPS . liftK1

liftFun' :: (a -> (b -> r) -> r) -> (a ~~r~> b)
liftFun' = liftFun . flip

dnEFun :: r ••(a ~~r~> b) -> (a ~~r~> b)
dnEFun = Fun . CPS . dnE . contramap (contramap (runCPS . getFun))

newtype Fun r a b = Fun { getFun :: CPS r a b }

instance (Pos a, Neg b) => Polarized N (Fun r a b) where

type a ~~ r = Fun r a
type f ~> b = f b

infixr 6 ~~
infixr 5 ~>
