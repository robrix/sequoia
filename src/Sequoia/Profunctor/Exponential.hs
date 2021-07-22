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
, dnE
, coerceExp
, liftRunExp
, dimapVK
, lmapV
, rmapK
  -- * Profunctor
, dimapExp
, lmapExp
, rmapExp
  -- * Strong
, firstExp
, secondExp
  -- * Choice
, leftExp
, rightExp
  -- * Traversing
, wanderExp
  -- * Category
, idExp
, composeExp
  -- * Applicative
, pureExp
, apExp
  -- * Monad
, bindExp
) where

import           Control.Category ((<<<), (>>>))
import qualified Control.Category as Cat
import           Data.Kind (Type)
import           Data.Profunctor
import           Data.Profunctor.Traversing
import           Sequoia.Disjunction
import           Sequoia.Optic.Iso
import           Sequoia.Profunctor.Applicative
import           Sequoia.Profunctor.Coexponential
import           Sequoia.Profunctor.Context
import           Sequoia.Profunctor.Continuation as K
import           Sequoia.Profunctor.Value as V

-- Exponential profunctor

newtype Exp e r a b = Exp { getExp :: V e a -> K b r -> C e r }

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

instance Env e (Exp e r a b) where
  env f = inExp (\ v k -> env (runExp v k . f))

instance Res r (Exp e r a b) where
  res = inExp . const . const . res
  liftRes f = liftRunExp (\ run -> liftRes (dimap (. run) run f))


-- Mixfix notation

type l --|(r :: Type -> Type -> Type) = r l
type l|-> r = l r

infixr 6 --|
infixr 5 |->


-- Exponential profunctor abstraction

_Exponential :: (Exponential f, Exponential f') => Iso (f e r a b) (f' e' r' a' b') (V e a -> K b r -> C e r) (V e' a' -> K b' r' -> C e' r')
_Exponential = exExp <-> inExp

class (forall e r . Cat.Category (f e r), forall e r . Profunctor (f e r)) => Exponential f where
  inExp :: (V e a -> K b r -> C e r) -> f e r a b
  exExp :: f e r a b -> (V e a -> K b r -> C e r)


-- Construction

inExp' :: Exponential f => (a -> b) -> a --|f e r|-> b
inExp' f = inExp (flip (•∘) . fmap f)


-- Elimination

evalExp :: Exponential f => e --|f e r|-> r -> (e -> r)
evalExp f = runC (exExp f (V id) (K id))

appExp :: Exponential f => a --|f e r|-> b -> V e (V e a -> K (K b r) r)
appExp f = V (\ e a -> K (\ b -> runC (exExp f a b) e))

appExp2 :: Exponential f => a --|f e r|-> b --|f e r|-> c -> V e (V e a -> V e b -> K (K c r) r)
appExp2 f = V (\ e a b -> K (\ c -> runC (exExp f a (K (\ g -> runC (exExp g b c) e))) e))

runExp :: Exponential f => V e a -> K b r -> a --|f e r|-> b -> C e r
runExp v k f = exExp f v k

elimExp :: (Exponential f, Coexponential s) => a --|f e r|-> b -> s e r b a -> C e r
elimExp f = unCoexp (exExp f) . coerceCoexp


-- Computation

dnE :: Exponential f => K (K (a --|f e r|-> b) r) r -> a --|f e r|-> b
dnE k = inExp (\ v k' -> cont (\ _K -> k •• _K (\ f -> exExp f v k')))

coerceExp :: (Exponential c, Exponential d) => c e r a b -> d e r a b
coerceExp = inExp . exExp


liftRunExp :: Exponential f => ((f e r a b -> C e r) -> C e r) -> f e r a b
liftRunExp f = inExp (\ v k -> f (runExp v k))


dimapVK :: Exponential f => (V e a' -> V e a) -> (K b' r -> K b r) -> (a --|f e r|-> b -> a' --|f e r|-> b')
dimapVK f g = inExp . dimap f (lmap g) . exExp

lmapV :: Exponential f => (V e a' -> V e a) -> (a --|f e r|-> b -> a' --|f e r|-> b)
lmapV = (`dimapVK` id)

rmapK :: Exponential f => (K b' r -> K b r) -> (a --|f e r|-> b -> a --|f e r|-> b')
rmapK = (id `dimapVK`)


-- Profunctor

dimapExp :: Exponential f => (a' -> a) -> (b -> b') -> a --|f e r|-> b -> a' --|f e r|-> b'
dimapExp f g = dimapVK (fmap f) (lmap g)

lmapExp :: Exponential f => (a' -> a) -> a --|f e r|-> b -> a' --|f e r|-> b
lmapExp = lmapV . fmap

rmapExp :: Exponential f => (b -> b') -> a --|f e r|-> b -> a --|f e r|-> b'
rmapExp = rmapK . lmap


-- Strong

firstExp  :: Exponential f => a --|f e r|-> b -> (a, c) --|f e r|-> (b, c)
firstExp  r = inExp (\ a b -> val (\ (a, c) -> exExp r (inV0 a) (lmap (,c) b)) a)

secondExp :: Exponential f => a --|f e r|-> b -> (c, a) --|f e r|-> (c, b)
secondExp r = inExp (\ a b -> val (\ (c, a) -> exExp r (inV0 a) (lmap (c,) b)) a)


-- Choice

leftExp  :: Exponential f => a --|f e r|-> b -> Either a c --|f e r|-> Either b c
leftExp  r = inExp (\ a b -> val (flip (exExp r) (inlK b) . inV0 <--> (inrK b ••)) a)

rightExp :: Exponential f => a --|f e r|-> b -> Either c a --|f e r|-> Either c b
rightExp r = inExp (\ a b -> val ((inlK b ••) <--> flip (exExp r) (inrK b) . inV0) a)


-- Traversing

wanderExp :: (Exponential f, Applicative (f e r e)) => (forall m . Applicative m => (a -> m b) -> (s -> m t)) -> a --|f e r|-> b -> s --|f e r|-> t
wanderExp traverse r = inExp (\ v k -> val (\ s -> exExp (traverse (((r <<<) . inExp . const . flip (•∘)) . inV0) s) (V id) k) v)


-- Category

idExp :: Exponential f => a --|f e r|-> a
idExp = inExp' id

composeExp :: Exponential f => b --|f e r|-> c -> a --|f e r|-> b -> a --|f e r|-> c
composeExp f g = inExp (\ a c -> cont (\ _K -> exExp g a (_K (\ b -> exExp f (inV0 b) c))))


-- Applicative

pureExp :: Exponential f => b -> a --|f e r|-> b
pureExp = inExp . const . flip (••)

apExp :: Exponential f => a --|f e r|-> (b -> c) -> a --|f e r|-> b -> a --|f e r|-> c
apExp df da = inExp (\ a b -> cont (\ _K -> exExp df a (_K (\ f -> exExp da a (lmap f b)))))


-- Monad

bindExp :: Exponential f => a --|f e r|-> b -> (b -> a --|f e r|-> c) -> a --|f e r|-> c
bindExp m f = inExp (\ v k -> cont (\ _K -> exExp m v (_K (\ b -> exExp (f b) v k))))
