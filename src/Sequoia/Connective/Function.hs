module Sequoia.Connective.Function
( -- * Implication
  Fun(getFun)
, type (~~)
, type (~>)
  -- * Construction
, fun
, funExp
) where

import qualified Control.Category as Cat
import           Data.Kind (Type)
import           Data.Profunctor
import           Data.Profunctor.Traversing
import           Prelude hiding (exp)
import           Sequoia.Polarity
import           Sequoia.Profunctor.Context
import           Sequoia.Profunctor.Continuation
import           Sequoia.Profunctor.Exponential
import           Sequoia.Profunctor.Value

-- Implication

newtype Fun e r a b = Fun { getFun :: Exp e r a b }
  deriving (Cat.Category, Choice, Profunctor, Strong, Traversing) via Exp e r
  deriving (Functor) via Exp e r a

instance (Pos a, Neg b) => Polarized N (Fun e r a b) where

type l ~~(r :: Type -> Type -> Type) = r l
type l~> r = l r

infixr 6 ~~
infixr 5 ~>


-- Construction

fun :: (b • r -> e ∘ a -> e ==> r) -> a ~~Fun e r~> b
fun = funExp . exp

funExp :: Exp e r a b -> a ~~Fun e r~> b
funExp = Fun
