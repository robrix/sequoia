module Focalized.Implication
( -- * Implication
  appFun
, appFun2
, liftFun
, liftFun'
, Fun(..)
, type (~~)
, type (~>)
  -- * Subtraction
, Sub(..)
, type (~-)
, type (-<)
) where

import Focalized.CPS
import Focalized.Negation
import Focalized.Polarity

-- Implication

appFun :: (a ~~r~> b) -> a -> (b -> r) -> r
appFun = appCPS . getFun

appFun2 :: (a ~~r~> b ~~r~> c) -> a -> b -> (c -> r) -> r
appFun2 = appCPS2 . fmap getFun . getFun

liftFun :: ((b -> r) -> (a -> r)) -> a ~~r~> b
liftFun = Fun . CPS

liftFun' :: (a -> (b -> r) -> r) -> a ~~r~> b
liftFun' = liftFun . flip

newtype Fun r a b = Fun { getFun :: CPS r a b }

instance (Pos a, Neg b) => Polarized N (Fun r a b) where

type a ~~ r = Fun r a
type f ~> b = f b

infixr 6 ~~
infixr 5 ~>


-- Subtraction

data Sub r a b = Sub { subA :: !a, subK :: !(r -b) }

instance (Pos a, Neg b) => Polarized P (Sub r a b) where

type a ~-r = Sub r a
type r-< b = r b

infixr 6 ~-
infixr 5 -<
