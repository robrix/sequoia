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
  left'  r = Exp (\ a b -> val (flip (runExp r) (inlK b) . pure <--> (inrK b ••)) a)
  right' r = Exp (\ a b -> val ((inlK b ••) <--> flip (runExp r) (inrK b) . pure) a)

instance Traversing (Exp e r) where
  wander traverse r = Exp (\ v k -> val (\ s -> runExp (traverse ((r <<<) . pure) s) (V id) k) v)

instance Cat.Category (Exp e r) where
  id = Exp (flip (•∘))
  f . g = Exp (\ a c -> cont (\ _K -> runExp g a (_K (\ b -> runExp f (pure b) c))))

instance Functor (Exp e r c) where
  fmap = rmap

instance Applicative (Exp e r a) where
  pure = Exp . const . flip (••)
  df <*> da = Exp (\ a b -> cont (\ _K -> runExp df a (_K (\ f -> runExp da a (lmap f b)))))

instance Monad (Exp e r a) where
  m >>= f = Exp (\ v k -> cont (\ _K -> runExp m v (_K (\ b -> runExp (f b) v k))))

instance MonadEnv e (Exp e r a) where
  env f = Exp (\ v k -> env (runExp' v k . f))

instance MonadRes r (Exp e r a) where
  mres = res
  mliftRes = liftRes

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

instance Res r (Exp e r a b) where
  res = Exp . const . const . res
  liftRes f = Exp (\ v k -> let run = runExp' v k in liftRes (dimap (. run) run f))


-- Mixfix notation

type l --|r = r l
type l|-> r = l r

infixr 6 --|
infixr 5 |->


-- Construction

exp' :: (a -> b) -> a --|Exp e r|-> b
exp' f = Exp (flip (•∘) . fmap f)

expV :: e ∘ a -> e --|Exp e r|-> a
expV a = Exp (\ v k -> k •∘ (a <<< v))

expK :: a • r -> a --|Exp e r|-> r
expK a = Exp (\ v k -> (k <<< a) •∘ v)

expVK :: e ∘ a -> a • r -> e --|Exp e r|-> r
expVK = fmap expC . flip (•∘)

expC :: e ==> r -> e --|Exp e r|-> r
expC (C c) = expFn (\ v k -> k . c . v)

expFn :: ((e -> a) -> (b -> r) -> (e -> r)) -> Exp e r a b
expFn = coerce

expCoexp :: (Coexp e r b a -> e ==> r) -> Exp e r a b
expCoexp f = Exp (fmap f . Coexp)


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
dnE k = Exp (\ v k' -> cont (\ _K -> k •• _K (\ f -> runExp f v k')))

reset :: a --|Exp e b|-> b -> a --|Exp e r|-> b
reset f = Exp (\ v k -> k •∘ toV (runExp f v idK))

shift :: (a • r --|Exp e r|-> r) -> e --|Exp e r|-> a
shift f = Exp (\ v k -> runExp f (pure k) idK <<∘ v)
