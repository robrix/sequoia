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

appFun :: Continuation k => (a ~~k~> b) -> (a -> k **b)
appFun = (-<<) . getFun

appFun2 :: Continuation k => (a ~~k~> b ~~k~> c) -> (a -> b -> k **c)
appFun2 f a b = inDN (appC2 f a b)

liftFun :: Continuation k => ((b -> KRep k) -> (a -> KRep k)) -> (a ~~k~> b)
liftFun = Fun . inK1

liftFun' :: Continuation k => (a -> (b -> KRep k) -> KRep k) -> (a ~~k~> b)
liftFun' = liftFun . flip

newtype Fun k a b = Fun { getFun :: k b -> k a }
  deriving (Cat.Category, Choice, Profunctor, Strong, Traversing) via ViaCPS (Fun k) k

instance Continuation k => CPS k (Fun k) where
  inC = Fun
  exC = getFun

instance Contravariant k => Functor (Fun k a) where
  fmap f (Fun r) = Fun (r . contramap f)

instance (Pos a, Neg b) => Polarized N (Fun k a b) where

type a ~~ r = Fun r a
type f ~> b = f b

infixr 6 ~~
infixr 5 ~>
