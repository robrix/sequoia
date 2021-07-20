{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE TypeFamilies #-}
module Sequoia.Profunctor.Exponential
( -- * Exponential profunctor
  Exp(..)
  -- ** Mixfix notation
, type (--|)
, type (|->)
  -- ** Exponential profunctor abstraction
, _Exponential
, Exponential(..)
  -- ** Construction
, inExp'
  -- ** Elimination
, evalExp
, appExp
, appExp2
, runExp
, elimExp
  -- ** Composition
, (<<<)
, (>>>)
  -- ** Computation
, (↑)
, (↓)
, dnE
, coerceExp
, liftRunExp
, dimapVK
, lmapV
, rmapK
  -- * Defaults
, dimapExp
, lmapExp
, rmapExp
, firstExp
, secondExp
, leftExp
, rightExp
, wanderExp
, idExp
, composeExp
, pureExp
, apExp
, bindExp
) where

import           Control.Category ((<<<), (>>>))
import qualified Control.Category as Cat
import           Data.Kind (Type)
import           Data.Profunctor
import           Data.Profunctor.Traversing
import           Sequoia.Continuation as K
import           Sequoia.Disjunction
import           Sequoia.Functor.K
import           Sequoia.Functor.V
import           Sequoia.Optic.Iso
import           Sequoia.Profunctor.Applicative
import           Sequoia.Profunctor.Coexponential
import           Sequoia.Profunctor.Context
import           Sequoia.Value as V

-- Exponential profunctor

newtype Exp e r a b = Exp { getExp :: V e a -> K r b -> C e r }

instance Exponential Exp where
  inExp = Exp
  exExp = getExp

instance Profunctor (Exp e r) where
  dimap = dimapExp

instance Strong (Exp e r) where
  first'  = firstExp
  second' = secondExp

instance Choice (Exp e r) where
  left'  = leftExp
  right' = rightExp

instance Traversing (Exp e r) where
  wander = wanderExp

instance Cat.Category (Exp e r) where
  id = idExp
  (.) = composeExp

instance Functor (Exp e r c) where
  fmap = rmap

instance Applicative (Exp e r a) where
  pure = pureExp
  (<*>) = apExp

instance Monad (Exp e r a) where
  (>>=) = bindExp

instance Coapply (Exp e r) where
  coliftA2 f a b = Exp (\ v k -> env ((flip (exExp a) k <∘∘> flip (exExp b) k) (f <$> v)))

instance Env2 Exp where
  env2 f = inExp (\ v k -> env (runExp v k . f))

instance Res2 Exp where
  res2 = inExp . const . const . res
  liftRes2 f = liftRunExp (\ run -> liftRes (dimap (. run) run f))


-- Mixfix notation

type l --|(r :: Type -> Type -> Type) = r l
type l|-> r = l r

infixr 6 --|
infixr 5 |->


-- Exponential profunctor abstraction

_Exponential :: (Exponential f, Exponential f') => Iso (f e r a b) (f' e' r' a' b') (V e a -> K r b -> C e r) (V e' a' -> K r' b' -> C e' r')
_Exponential = exExp <-> inExp

class (forall e r . Cat.Category (f e r), forall e r . Profunctor (f e r)) => Exponential f where
  inExp :: (V e a -> K r b -> C e r) -> f e r a b
  exExp :: f e r a b -> V e a -> K r b -> C e r


-- Construction

inExp' :: Exponential f => (a -> b) -> a --|f e r|-> b
inExp' f = inExp (\ a b -> b •∘ (f <$> a))


-- Elimination

evalExp :: Exponential f => e --|f e r|-> r -> (e -> r)
evalExp f = runC (exExp f idV idK)

appExp :: Exponential f => a --|f e r|-> b -> V e (V e a -> K r **b)
appExp f = inV (\ e a -> inK (\ b -> runC (exExp f a b) e))

appExp2 :: Exponential f => a --|f e r|-> b --|f e r|-> c -> V e (V e a -> V e b -> K r **c)
appExp2 f = inV (\ e a b -> inK (\ c -> runC (exExp f a (inK (\ g -> runC (exExp g b c) e))) e))

runExp :: Exponential f => V e a -> K r b -> a --|f e r|-> b -> C e r
runExp v k f = exExp f v k

elimExp :: (Exponential f, Coexponential s) => a --|f e r|-> b -> s e r a b -> C e r
elimExp f = (exExp f <$> recall <*> forget) . exCoexp


-- Computation

(↑) :: Exponential f => a --|f e r|-> b -> V e a -> f e r e|-> b
f ↑ a = f <<< inExp (const (•∘ a))

infixl 7 ↑

(↓) :: Exponential f => K r b -> a --|f e r|-> b -> a --|f e r|-> r
k ↓ f = inExp (const . (k •∘)) <<< f

infixl 8 ↓

dnE :: Exponential f => K r **(a --|f e r|-> b) -> a --|f e r|-> b
dnE k = inExp (\ a b -> cont (\ _K -> k •• _K (\ f -> exExp f a b)))

coerceExp :: (Exponential c, Exponential d) => c e r a b -> d e r a b
coerceExp = inExp . exExp


liftRunExp :: Exponential f => ((f e r a b -> C e r) -> C e r) -> f e r a b
liftRunExp f = inExp (fmap f . runExp)


dimapVK :: Exponential f => (V e a' -> V e a) -> (K r b' -> K r b) -> (a --|f e r|-> b -> a' --|f e r|-> b')
dimapVK f g = inExp . dimap f (lmap g) . exExp

lmapV :: Exponential f => (V e a' -> V e a) -> (a --|f e r|-> b -> a' --|f e r|-> b)
lmapV = (`dimapVK` id)

rmapK :: Exponential f => (K r b' -> K r b) -> (a --|f e r|-> b -> a --|f e r|-> b')
rmapK = (id `dimapVK`)


-- Defaults

dimapExp :: Exponential f => (a' -> a) -> (b -> b') -> a --|f e r|-> b -> a' --|f e r|-> b'
dimapExp f g = dimapVK (fmap f) (contramap g)

lmapExp :: Exponential f => (a' -> a) -> a --|f e r|-> b -> a' --|f e r|-> b
lmapExp = lmapV . fmap

rmapExp :: Exponential f => (b -> b') -> a --|f e r|-> b -> a --|f e r|-> b'
rmapExp = rmapK . contramap

firstExp  :: Exponential f => a --|f e r|-> b -> (a, c) --|f e r|-> (b, c)
firstExp  r = inExp (\ a b -> val (\ (a, c) -> exExp r (inV0 a) (contramap (,c) b)) a)

secondExp :: Exponential f => a --|f e r|-> b -> (c, a) --|f e r|-> (c, b)
secondExp r = inExp (\ a b -> val (\ (c, a) -> exExp r (inV0 a) (contramap (c,) b)) a)

leftExp  :: Exponential f => a --|f e r|-> b -> Either a c --|f e r|-> Either b c
leftExp  r = inExp (\ a b -> val (flip (exExp r) (inlK b) . inV0 <--> (inrK b ••)) a)

rightExp :: Exponential f => a --|f e r|-> b -> Either c a --|f e r|-> Either c b
rightExp r = inExp (\ a b -> val ((inlK b ••) <--> flip (exExp r) (inrK b) . inV0) a)

wanderExp :: (Exponential f, Applicative (f e r e)) => (forall m . Applicative m => (a -> m b) -> (s -> m t)) -> a --|f e r|-> b -> s --|f e r|-> t
wanderExp traverse r = inExp (\ s t -> val (\ s -> exExp (traverse ((r ↑) . inV0) s) idV t) s)

idExp :: Exponential f => a --|f e r|-> a
idExp = inExp (flip (•∘))

composeExp :: Exponential f => b --|f e r|-> c -> a --|f e r|-> b -> a --|f e r|-> c
composeExp f g = inExp (\ a c -> cont (\ _K -> exExp g a (_K (\ b -> exExp f (inV0 b) c))))

pureExp :: Exponential f => b -> a --|f e r|-> b
pureExp = inExp . const . flip (••)

apExp :: Exponential f => a --|f e r|-> (b -> c) -> a --|f e r|-> b -> a --|f e r|-> c
apExp df da = inExp (\ a b -> cont (\ _K -> exExp df a (_K (\ f -> exExp da a (contramap f b)))))

bindExp :: Exponential f => a --|f e r|-> b -> (b -> a --|f e r|-> c) -> a --|f e r|-> c
bindExp m f = inExp (\ a c -> cont (\ _K -> exExp m a (_K (\ b -> exExp (f b) a c))))
