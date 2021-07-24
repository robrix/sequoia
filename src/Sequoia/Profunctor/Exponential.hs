{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE TypeFamilies #-}
module Sequoia.Profunctor.Exponential
( -- * Exponential profunctor
  _Exp
, Exp(..)
  -- ** Mixfix notation
, type (--|)
, type (|->)
  -- ** Construction
, exp
, exp'
, expV
, expK
, expVK
, expC
, expFn
, expCoexp
  -- ** Elimination
, evalExp
, appExp
, appExp2
, runExp
, runExp'
, elimExp
, runExpFn
, (↑)
, (↓)
  -- ** Composition
, (<<<)
, (>>>)
  -- ** Computation
, dnE
, reset
, shift
) where

import           Control.Arrow
import qualified Control.Category as Cat
import           Data.Coerce
import           Data.Function
import           Data.Profunctor
import           Data.Profunctor.Traversing
import           Prelude hiding (exp)
import           Sequoia.Conjunction
import           Sequoia.Disjunction
import           Sequoia.Optic.Iso
import           Sequoia.Profunctor.Applicative
import           Sequoia.Profunctor.Coexponential
import           Sequoia.Profunctor.Context
import           Sequoia.Profunctor.Continuation as K
import           Sequoia.Profunctor.Value as V

-- Exponential profunctor

_Exp :: Iso (Exp e r a b) (Exp e' r' a' b') (e ∘ a -> b • r -> e ==> r) (e' ∘ a' -> b' • r' -> e' ==> r')
_Exp = coerced

newtype Exp e r a b = Exp (e ∘ a -> b • r -> e ==> r)

instance Profunctor (Exp e r) where
  dimap f g = exp . dimap (fmap f) (lmap (lmap g)) . runExp

instance Strong (Exp e r) where
  first'  r = exp (\ a b -> val (\ (a, c) -> lmap (,c) b ↓ r ↑ pure a) a)
  second' r = exp (\ a b -> val (\ (c, a) -> lmap (c,) b ↓ r ↑ pure a) a)

instance Choice (Exp e r) where
  left'  r = exp (\ a b -> val ((\ v -> inlK b ↓ r ↑ pure v) <--> pure . (inrK b •)) a)
  right' r = exp (\ a b -> val (pure . (inlK b •) <--> (\ v -> inrK b ↓ r ↑ pure v)) a)

instance Traversing (Exp e r) where
  wander traverse r = exp (\ v k -> val (\ s -> k ↓ traverse ((r <<<) . pure) s ↑ idV) v)

instance Cat.Category (Exp e r) where
  id = exp (\ v k -> C ((k •) . (v ∘)))
  f . g = exp (\ a c -> C (\ e -> K (\ b -> c ↓ f ↑ pure b <== e) ↓ g ↑ a <== e))

instance Functor (Exp e r c) where
  fmap = rmap

instance Applicative (Exp e r a) where
  pure a = exp (\ v k -> C ((k •) . const a . (v ∘)))
  -- FIXME: K, ↑, and ↓ could b actions in MonadEnv
  df <*> da = exp (\ a b -> C (\ e -> K (\ f -> lmap f b ↓ da ↑ a <== e) ↓ df ↑ a <== e))

instance Monad (Exp e r a) where
  m >>= f = exp (\ v k -> C (\ e -> K (\ b -> k ↓ f b ↑ v <== e) ↓ m ↑ v <== e))

instance MonadEnv e (Exp e r a) where
  env f = exp (\ v k -> env (\ e -> k ↓ f e ↑ v))

instance MonadRes r (Exp e r a) where
  res = exp . const . const . pure
  liftRes f = exp (\ v k -> env (\ e -> let run f = k ↓ f ↑ v in run (f ((<== e) . run))))

instance Coapply (Exp e r) where
  coliftA2 f a b = exp (\ v k -> env (((\ v -> k ↓ a ↑ v) <∘∘> (\ v -> k ↓ b ↑ v)) (f <$> v)))

instance Arrow (Exp e r) where
  arr = exp'
  first  = first'
  second = second'

instance ArrowChoice (Exp e r) where
  left  = left'
  right = right'

instance ArrowApply (Exp e r) where
  app = exp (\ v k -> val (runExp' (exrF v) k) (exlF v))


-- Mixfix notation

type l --|r = r l
type l|-> r = l r

infixr 6 --|
infixr 5 |->


-- Construction

exp :: (e ∘ a -> b • r -> e ==> r) -> Exp e r a b
exp = Exp

exp' :: (a -> b) -> a --|Exp e r|-> b
exp' f = exp (\ v k -> C ((k •) . f . (v ∘)))

expV :: e ∘ a -> e --|Exp e r|-> a
expV = exp' . (∘)

expK :: a • r -> a --|Exp e r|-> r
expK = exp' . (•)

expVK :: e ∘ a -> a • r -> e --|Exp e r|-> r
expVK v k = expC (C ((k •) . (v ∘)))

expC :: e ==> r -> e --|Exp e r|-> r
expC = exp' . (<==)

expFn :: ((e -> a) -> (b -> r) -> (e -> r)) -> Exp e r a b
expFn = coerce

expCoexp :: (Coexp e r b a -> e ==> r) -> Exp e r a b
expCoexp f = exp (fmap f . (>-))


-- Elimination

evalExp :: e --|Exp e r|-> r -> (e -> r)
evalExp f = (idK ↓ f ↑ idV <==)

appExp :: a --|Exp e r|-> b -> e ∘ (e ∘ a -> b • r • r)
appExp f = V (\ e a -> K (\ b -> b ↓ f ↑ a <== e))

appExp2 :: a --|Exp e r|-> b --|Exp e r|-> c -> e ∘ (e ∘ a -> e ∘ b -> c • r • r)
appExp2 f = V (\ e a b -> K (\ c -> K (\ g -> c ↓ g ↑ b <== e) ↓ f ↑ a <== e))

runExp :: a --|Exp e r|-> b -> e ∘ a -> b • r -> e ==> r
runExp = coerce

runExp' :: e ∘ a -> b • r -> a --|Exp e r|-> b -> e ==> r
runExp' v k f = runExp f v k

elimExp :: a --|Exp e r|-> b -> Coexp e r b a -> e ==> r
elimExp = unCoexp . runExp

runExpFn :: Exp e r a b -> ((e -> a) -> (b -> r) -> (e -> r))
runExpFn = coerce . runExp

(↑) :: a --|Exp e r|-> b -> e ∘ a -> b • r -> e ==> r
(↑) = coerce

infixl 3 ↑

(↓) :: b • r -> (b • r -> e ==> r) -> e ==> r
(↓) = (&)

infixl 2 ↓


-- Computation

dnE :: ((a --|Exp e r|-> b) • r) • r -> a --|Exp e r|-> b
dnE k = exp (\ v k' -> C (\ e -> k • K (\ f -> k' ↓ f ↑ v <== e)))

reset :: a --|Exp e b|-> b -> a --|Exp e r|-> b
reset f = exp (\ v k -> C (\ e -> k • (idK ↓ f ↑ v <== e)))

shift :: (a • r --|Exp e r|-> r) -> e --|Exp e r|-> a
shift f = exp (\ v k -> idK ↓ f ↑ pure k <<∘ v)
