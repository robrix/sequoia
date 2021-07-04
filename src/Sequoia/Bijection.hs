module Sequoia.Bijection
( -- * Bijections
  type (<->)(..)
  -- ** Elimination
, exBl
, exBr
, (<~)
, (~>)
  -- ** Construction
, (<->)
, inv
, constant
, involuted
  -- ** Coercion
, coerced
, coercedFrom
, coercedTo
  -- ** Adjunction
, contraadjuncted
) where

import qualified Control.Category as Cat
import           Data.Coerce
import qualified Data.Functor.Contravariant.Adjunction as Contra

-- Bijections

newtype a <-> b = Bij { runBij :: forall r . ((a -> b) -> (b -> a) -> r) -> r }

infix 1 <->

instance Cat.Category (<->) where
  id = id <-> id
  f . g = (exBl f . exBl g) <-> (exBr g . exBr f)


-- Elimination

exBl :: a <-> b -> (a -> b)
exBl b = runBij b const

exBr :: a <-> b -> (b -> a)
exBr b = runBij b (const id)

(<~) :: a <-> b -> (a -> b)
(<~) = exBl

infixr 9 <~

(~>) :: b -> a <-> b -> a
b ~> x = exBr x b

infixl 9 ~>


-- Construction

(<->) :: (a -> b) -> (b -> a) -> a <-> b
l <-> r = Bij (\ f -> f l r)

inv :: a <-> b -> b <-> a
inv b = (~> b) <-> (b <~)

constant :: a -> (a -> b) <-> b
constant a = ($ a) <-> const

involuted :: (a -> a) -> a <-> a
involuted f = f <-> f


-- Coercion

coerced :: Coercible a b => a <-> b
coerced = coerce <-> coerce

coercedTo   :: Coercible a b => (a -> b) -> a <-> b
coercedTo   = (<-> coerce)

coercedFrom :: Coercible a b => (b -> a) -> a <-> b
coercedFrom = (coerce <->)


-- Adjunction

contraadjuncted :: Contra.Adjunction f u => (a -> f b) <-> (b -> u a)
contraadjuncted = Contra.leftAdjunct <-> Contra.rightAdjunct
