module Sequoia.Connective.Function
( -- * Implication
  Fun(..)
, type (~~)
, type (~>)
  -- * Construction
, fun
, fun'
, funExp
  -- * Elimination
, appFun
, runFunExp
) where

import qualified Control.Category as Cat
import           Data.Coerce
import           Data.Kind (Type)
import           Data.Profunctor.Traversing
import           Prelude hiding (exp)
import           Sequoia.Polarity
import           Sequoia.Profunctor
import           Sequoia.Profunctor.Continuation
import           Sequoia.Profunctor.Exp (Exp(..))

-- Implication

newtype Fun r a b = Fun { getFun :: (b • r) -> (a • r) }
  deriving (Cat.Category, Choice, Profunctor, Strong, Traversing) via Exp r
  deriving (Functor) via Exp r a

instance (Pos a, Neg b) => Polarized N (Fun r a b) where

type l ~~(r :: Type -> Type -> Type) = r l
type l~> r = l r

infixr 6 ~~
infixr 5 ~>


-- Construction

fun :: (b • r -> a -> r) -> a ~~Fun r~> b
fun = coerce

fun' :: (a -> b) -> a ~~Fun r~> b
fun' = Fun . (^>>)

funExp :: Exp r a b -> a ~~Fun r~> b
funExp = coerce


-- Elimination

appFun :: Fun r a b -> a -> DN r b
appFun f a = DN (K ((• a) . getFun f))

runFunExp :: Fun r a b -> Exp r a b
runFunExp = coerce
