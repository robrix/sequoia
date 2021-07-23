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
, inExp'
, inExpV
, inExpK
, inExpVK
, inExpC
, inExpFn
, inExpCoexp
  -- ** Elimination
, evalExp
, appExp
, appExp2
, runExp
, elimExp
, exExpFn
  -- ** Composition
, (<<<)
, (>>>)
  -- ** Computation
, dnE
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

newtype Exp e r a b = Exp { exExp :: e ∘ a -> b • r -> e ==> r }

instance Profunctor (Exp e r) where
  dimap f g = Exp . dimap (fmap f) (lmap (lmap g)) . exExp

instance Strong (Exp e r) where
  first'  r = Exp (\ a b -> val (\ (a, c) -> exExp r (pure a) (lmap (,c) b)) a)
  second' r = Exp (\ a b -> val (\ (c, a) -> exExp r (pure a) (lmap (c,) b)) a)

instance Choice (Exp e r) where
  left'  r = Exp (\ a b -> val (flip (exExp r) (inlK b) . pure <--> (inrK b ••)) a)
  right' r = Exp (\ a b -> val ((inlK b ••) <--> flip (exExp r) (inrK b) . pure) a)

instance Traversing (Exp e r) where
  wander traverse r = Exp (\ v k -> val (\ s -> exExp (traverse ((r <<<) . pure) s) (V id) k) v)

instance Cat.Category (Exp e r) where
  id = Exp (flip (•∘))
  f . g = Exp (\ a c -> cont (\ _K -> exExp g a (_K (\ b -> exExp f (pure b) c))))

instance Functor (Exp e r c) where
  fmap = rmap

instance Applicative (Exp e r a) where
  pure = Exp . const . flip (••)
  df <*> da = Exp (\ a b -> cont (\ _K -> exExp df a (_K (\ f -> exExp da a (lmap f b)))))

instance Monad (Exp e r a) where
  m >>= f = Exp (\ v k -> cont (\ _K -> exExp m v (_K (\ b -> exExp (f b) v k))))

instance Coapply (Exp e r) where
  coliftA2 f a b = Exp (\ v k -> env ((flip (exExp a) k <∘∘> flip (exExp b) k) (f <$> v)))

instance Arrow (Exp e r) where
  arr = inExp'
  first  = first'
  second = second'

instance ArrowChoice (Exp e r) where
  left  = left'
  right = right'

instance ArrowApply (Exp e r) where
  app = Exp (\ v k -> val (runExp (exrF v) k) (exlF v))

instance Env e (Exp e r a b) where
  env f = Exp (\ v k -> env (runExp v k . f))

instance Res r (Exp e r a b) where
  res = Exp . const . const . res
  liftRes f = Exp (\ v k -> let run = runExp v k in liftRes (dimap (. run) run f))


-- Mixfix notation

type l --|r = r l
type l|-> r = l r

infixr 6 --|
infixr 5 |->


-- Construction

inExp' :: (a -> b) -> a --|Exp e r|-> b
inExp' f = Exp (flip (•∘) . fmap f)

inExpV :: e ∘ a -> e --|Exp e r|-> a
inExpV a = Exp (\ v k -> k •∘ (a <<< v))

inExpK :: a • r -> a --|Exp e r|-> r
inExpK a = Exp (\ v k -> (k <<< a) •∘ v)

inExpVK :: e ∘ a -> a • r -> e --|Exp e r|-> r
inExpVK = fmap inExpC . flip (•∘)

inExpC :: e ==> r -> e --|Exp e r|-> r
inExpC (C c) = inExpFn (\ v k -> k . c . v)

inExpFn :: ((e -> a) -> (b -> r) -> (e -> r)) -> Exp e r a b
inExpFn = coerce

inExpCoexp :: (Coexp e r b a -> e ==> r) -> Exp e r a b
inExpCoexp f = Exp (fmap f . Coexp)


-- Elimination

evalExp :: e --|Exp e r|-> r -> (e -> r)
evalExp f = exExpFn f id id

appExp :: a --|Exp e r|-> b -> e ∘ (e ∘ a -> b • r • r)
appExp f = V (\ e a -> K (\ b -> exExp f a b <== e))

appExp2 :: a --|Exp e r|-> b --|Exp e r|-> c -> e ∘ (e ∘ a -> e ∘ b -> c • r • r)
appExp2 f = V (\ e a b -> K (\ c -> exExp f a (K (\ g -> exExp g b c <== e)) <== e))

runExp :: e ∘ a -> b • r -> a --|Exp e r|-> b -> e ==> r
runExp v k f = exExp f v k

elimExp :: a --|Exp e r|-> b -> Coexp e r b a -> e ==> r
elimExp = unCoexp . exExp

exExpFn :: Exp e r a b -> ((e -> a) -> (b -> r) -> (e -> r))
exExpFn = coerce . exExp


-- Computation

dnE :: ((a --|Exp e r|-> b) • r) • r -> a --|Exp e r|-> b
dnE k = Exp (\ v k' -> cont (\ _K -> k •• _K (\ f -> exExp f v k')))
