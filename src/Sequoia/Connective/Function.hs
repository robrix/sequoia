module Sequoia.Connective.Function
( -- * Implication
  Fun(getFun)
, type (~~)
, type (~>)
  -- * Construction
, fun
, funExp
  -- * Elimination
, runFunExp
) where

import qualified Control.Category as Cat
import           Data.Kind (Type)
import           Data.Profunctor
import           Data.Profunctor.Traversing
import           Prelude hiding (exp)
import           Sequoia.Connective.Not
import           Sequoia.Connective.NotUntrue
import           Sequoia.Polarity
import           Sequoia.Profunctor.Context
import           Sequoia.Profunctor.Continuation
import           Sequoia.Profunctor.Exponential
import           Sequoia.Profunctor.Value

-- Implication

newtype Fun e r a b = Fun { getFun :: b ¬ r -> e ≁ a -> e ==> r }
  deriving (Cat.Category, Choice, Profunctor, Strong, Traversing) via Exp e r
  deriving (Functor) via Exp e r a

instance (Pos a, Neg b) => Polarized N (Fun e r a b) where

type l ~~(r :: Type -> Type -> Type) = r l
type l~> r = l r

infixr 6 ~~
infixr 5 ~>


-- Construction

fun :: (b ¬ r -> e ≁ a -> e ==> r) -> a ~~Fun e r~> b
fun = Fun

funExp :: Exp e r a b -> a ~~Fun e r~> b
funExp = fun . dimap getNot (lmap runNotUntrue) . runExp


-- Elimination

runFunExp :: a ~~Fun e r~> b -> Exp e r a b
runFunExp = exp . dimap Not (lmap NotUntrue) . getFun
