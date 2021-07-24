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
, runExp'
, elimExp
, runExpFn
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
import           Data.Profunctor
import           Data.Profunctor.Traversing
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

newtype Exp e r a b = Exp { runExp :: e ∘ a -> b • r -> e ==> r }

instance Profunctor (Exp e r) where
  dimap f g = Exp . dimap (fmap f) (lmap (lmap g)) . runExp

instance Strong (Exp e r) where
  first'  r = Exp (\ a b -> val (\ (a, c) -> runExp r (pure a) (lmap (,c) b)) a)
  second' r = Exp (\ a b -> val (\ (c, a) -> runExp r (pure a) (lmap (c,) b)) a)

instance Choice (Exp e r) where
  left'  r = Exp (\ a b -> val (flip (runExp r) (inlK b) . pure <--> pure . (inrK b •)) a)
  right' r = Exp (\ a b -> val (pure . (inlK b •) <--> flip (runExp r) (inrK b) . pure) a)

instance Traversing (Exp e r) where
  wander traverse r = Exp (\ v k -> val (\ s -> runExp (traverse ((r <<<) . pure) s) (V id) k) v)

instance Cat.Category (Exp e r) where
  id = Exp (\ v k -> C ((k •) . (v ∘)))
  f . g = expFn (\ a c e -> runExpFn g a (\ b -> runExpFn f (pure b) c e) e)

instance Functor (Exp e r c) where
  fmap = rmap

instance Applicative (Exp e r a) where
  pure a = Exp (\ v k -> C ((k •) . const a . (v ∘)))
  df <*> da = expFn (\ a b e -> runExpFn df a (\ f -> runExpFn da a (lmap f b) e) e)

instance Monad (Exp e r a) where
  m >>= f = expFn (\ v k e -> runExpFn m v (\ b -> runExpFn (f b) v k e) e)

instance MonadEnv e (Exp e r a) where
  env f = Exp (\ v k -> env (runExp' v k . f))

instance MonadRes r (Exp e r a) where
  res = Exp . const . const . pure
  liftRes f = Exp (\ v k -> env (\ e -> let run f = runExp f v k in run (f ((<== e) . run))))

instance Coapply (Exp e r) where
  coliftA2 f a b = Exp (\ v k -> env ((flip (runExp a) k <∘∘> flip (runExp b) k) (f <$> v)))

instance Arrow (Exp e r) where
  arr = exp'
  first  = first'
  second = second'

instance ArrowChoice (Exp e r) where
  left  = left'
  right = right'

instance ArrowApply (Exp e r) where
  app = Exp (\ v k -> val (runExp' (exrF v) k) (exlF v))


-- Mixfix notation

type l --|r = r l
type l|-> r = l r

infixr 6 --|
infixr 5 |->


-- Construction

exp' :: (a -> b) -> a --|Exp e r|-> b
exp' f = Exp (\ v k -> C ((k •) . f . (v ∘)))

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
expCoexp f = Exp (fmap f . (>-))


-- Elimination

evalExp :: e --|Exp e r|-> r -> (e -> r)
evalExp f = runExpFn f id id

appExp :: a --|Exp e r|-> b -> e ∘ (e ∘ a -> b • r • r)
appExp f = V (\ e a -> K (\ b -> runExp f a b <== e))

appExp2 :: a --|Exp e r|-> b --|Exp e r|-> c -> e ∘ (e ∘ a -> e ∘ b -> c • r • r)
appExp2 f = V (\ e a b -> K (\ c -> runExp f a (K (\ g -> runExp g b c <== e)) <== e))

runExp' :: e ∘ a -> b • r -> a --|Exp e r|-> b -> e ==> r
runExp' v k f = runExp f v k

elimExp :: a --|Exp e r|-> b -> Coexp e r b a -> e ==> r
elimExp = unCoexp . runExp

runExpFn :: Exp e r a b -> ((e -> a) -> (b -> r) -> (e -> r))
runExpFn = coerce . runExp


-- Computation

dnE :: ((a --|Exp e r|-> b) • r) • r -> a --|Exp e r|-> b
dnE k = expFn (\ v k' e -> k • K (\ f -> runExpFn f v k' e))

reset :: a --|Exp e b|-> b -> a --|Exp e r|-> b
reset f = expFn (\ v k e -> k (runExpFn f v id e))

shift :: (a • r --|Exp e r|-> r) -> e --|Exp e r|-> a
shift f = Exp (\ v k -> runExp f (pure k) idK <<∘ v)
