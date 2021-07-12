{-# LANGUAGE TypeFamilies #-}
module Sequoia.Profunctor.D
( -- * Dual profunctor
  D(..)
  -- ** Mixfix notation
, type (--|)
, type (|->)
  -- ** Construction
, inD'
, inDK
, inDV
  -- ** Elimination
, evalD
, exDK
  -- ** Composition
, (<<<)
, (>>>)
  -- ** Computation
, (↑)
, (<↑)
, (↓)
, (↓>)
) where

import           Control.Category ((<<<), (>>>))
import qualified Control.Category as Cat
import           Data.Function
import           Data.Kind (Type)
import           Data.Profunctor
import           Sequoia.Conjunction
import           Sequoia.Continuation as K
import           Sequoia.Disjunction
import           Sequoia.Functor.K
import           Sequoia.Functor.V
import           Sequoia.Value as V

-- Dual profunctor

newtype D r s a b = D { exD :: s -> (s -> a) -> (b -> r) -> r }

instance Profunctor (D r s) where
  dimap f g = D . rmap (dimap (rmap f) (lmap (lmap g))) . exD

instance Cat.Category (D r s) where
  id = D (fmap (&) . (&))
  D f . D g = D (\ e a c -> g e a (\ b -> f e (const b) c))

instance Functor (D r s c) where
  fmap = rmap

instance Applicative (D r s a) where
  pure a = D (\ _ _ b -> b a)

  D df <*> D da = D (\ e a b -> df e a (da e a . (b .)))

instance Monad (D r s a) where
  D m >>= f = D (\ e a c -> m e a (\ b -> exD (f b) e a c))


-- Mixfix notation

type l --|(r :: Type -> Type -> Type) = r l
type l|-> r = l r

infixr 6 --|
infixr 5 |->


-- Construction

inD' :: (a -> b) -> a --|D r s|-> b
inD' f = D (\ e a b -> b (f (a e)))

inDK :: (K r b -> K r a) -> a --|D r s|-> b
inDK f = D (\ e a b -> f (K b) • e ∘ a)

inDV :: (V s a -> V s b) -> a --|D r s|-> b
inDV f = D (\ e a b -> b (e ∘ f (V a)))


-- Elimination

exDK :: a --|D r s|-> b -> V s (K r b -> K r a)
exDK f = V (\ e k -> K (\ a -> exD f e (const a) (exK k)))

evalD :: a --|D r s|-> r -> V s (K r a)
evalD = (idK ↓)


-- Computation

(↑) :: a --|D r s|-> b -> V s a -> V s (K r (K r b))
f ↑ a = V (\ e -> K (\ k -> exD f e (exV a) (k •)))

infixl 7 ↑

(<↑) :: Conj c => (a `c` _Γ) --|D r s|-> _Δ -> a -> _Γ --|D r s|-> _Δ
f <↑ a = f Cat.<<< inD' (inlr a)

infixl 7 <↑

(↓) :: K r b -> a --|D r s|-> b -> V s (K r a)
k ↓ f = V (\ e -> K (\ a -> exD f e (const a) (exK k)))

infixl 8 ↓

-- FIXME: this is quite limited by the need for the continuation to return locally at r.
(↓>) :: Disj d => K r c -> a --|D r s|-> (b `d` c) -> a --|D r s|-> b
c ↓> f = D (\ e v k -> (K k <••> c) • v e) <<< f

infixr 9 ↓>
