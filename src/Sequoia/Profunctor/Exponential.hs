{-# LANGUAGE PolyKinds #-}
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
, expKV
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

_Exp :: Iso (Exp e r a b) (Exp e' r' a' b') (b • r -> e ∘ a -> e ==> r) (b' • r' -> e' ∘ a' -> e' ==> r')
_Exp = coerced

newtype Exp e r a b = Exp ((b -> r) -> (e -> a) -> (e -> r))

instance Profunctor (Exp e r) where
  dimap f g = exp . dimap (lmap g) (lmap (rmap f)) . runExp

instance Strong (Exp e r) where
  first'  r = exp (\ b -> val (\ (a, c) -> lmap (,c) b ↓ r ↑ pure a))
  second' r = exp (\ b -> val (\ (c, a) -> lmap (c,) b ↓ r ↑ pure a))

instance Choice (Exp e r) where
  left'  r = exp (\ b -> val ((\ v -> inlK b ↓ r ↑ pure v) <--> pure . (inrK b •)))
  right' r = exp (\ b -> val (pure . (inlK b •) <--> (\ v -> inrK b ↓ r ↑ pure v)))

instance Traversing (Exp e r) where
  wander traverse r = exp (\ k v -> val (\ s -> k ↓ traverse ((r <<<) . pure) s ↑ idV) v)

instance Cat.Category (Exp e r) where
  id = exp (↓↑)
  f . g = exp (\ c a -> env (\ e -> K (\ b -> c ↓ f ↑ pure b <== e) ↓ g ↑ a))

instance Functor (Exp e r c) where
  fmap = rmap

instance Applicative (Exp e r a) where
  pure = exp . ckv . pure
  df <*> da = exp (\ b a -> env (\ e -> K (\ f -> lmap f b ↓ da ↑ a <== e) ↓ df ↑ a))

instance Monad (Exp e r a) where
  m >>= f = exp (\ k v -> env (\ e -> K (\ b -> k ↓ f b ↑ v <== e) ↓ m ↑ v))

instance MonadEnv e (Exp e r a) where
  env f = exp (\ k v -> env (\ e -> k ↓ f e ↑ v))

instance MonadRes r (Exp e r a) where
  res = exp . ckv . pure
  liftRes f = exp (\ k v -> env (\ e -> let run f = k ↓ f ↑ v in run (f ((<== e) . run))))

instance Coapply (Exp e r) where
  coliftA2 f a b = exp (\ k -> env (((\ v -> k ↓ a ↑ v) <∘∘> (\ v -> k ↓ b ↑ v)) . fmap f))

instance Arrow (Exp e r) where
  arr = exp'
  first  = first'
  second = second'

instance ArrowChoice (Exp e r) where
  left  = left'
  right = right'

instance ArrowApply (Exp e r) where
  app = exp (\ k -> val . runExp' k . exrF <*> exlF)


-- Mixfix notation

type l --|r = r l
type l|-> r = l r

infixr 6 --|
infixr 5 |->


-- Construction

exp :: (b • r -> e ∘ a -> e ==> r) -> Exp e r a b
exp = coerce

exp' :: (a -> b) -> a --|Exp e r|-> b
exp' = exp . ckv

expV :: e ∘ a -> e --|Exp e r|-> a
expV = exp' . (∘)

expK :: a • r -> a --|Exp e r|-> r
expK = exp' . (•)

expKV :: a • r -> e ∘ a -> e --|Exp e r|-> r
expKV = fmap expC . (↓↑)

expC :: e ==> r -> e --|Exp e r|-> r
expC = exp' . (<==)

expFn :: ((b -> r) -> (e -> a) -> (e -> r)) -> Exp e r a b
expFn = coerce

expCoexp :: (Coexp e r b a -> e ==> r) -> Exp e r a b
expCoexp f = exp (fmap f . (>-))


-- Elimination

evalExp :: MonadEnv e m => e --|Exp e r|-> r -> m r
evalExp f = idK ↓ f ↑ idV

appExp :: a --|Exp e r|-> b -> e ∘ (e ∘ a -> b • r • r)
appExp f = V (\ e a -> K (\ b -> b ↓ f ↑ a <== e))

appExp2 :: a --|Exp e r|-> b --|Exp e r|-> c -> e ∘ (e ∘ a -> e ∘ b -> c • r • r)
appExp2 f = V (\ e a b -> K (\ c -> K (\ g -> c ↓ g ↑ b <== e) ↓ f ↑ a <== e))

runExp :: a --|Exp e r|-> b -> b • r -> e ∘ a -> e ==> r
runExp = coerce

runExp' :: b • r -> e ∘ a -> a --|Exp e r|-> b -> e ==> r
runExp' k v f = runExp f k v

elimExp :: a --|Exp e r|-> b -> Coexp e r b a -> e ==> r
elimExp = unCoexp . runExp

runExpFn :: Exp e r a b -> ((b -> r) -> (e -> a) -> (e -> r))
runExpFn = coerce . runExp

(↑) :: (e ∘ a -> m r) -> e ∘ a -> m r
(↑) = ($)

infixl 2 ↑

(↓) :: MonadEnv e m => b • r -> a --|Exp e r|-> b -> e ∘ a -> m r
(k ↓ f) a = env (\ e -> pure (runExp f k a <== e))

infixl 3 ↓


-- Computation

dnE :: ((a --|Exp e r|-> b) • r) • r -> a --|Exp e r|-> b
dnE k = exp (\ k' v -> cont (\ _K -> pure (k • _K (\ f -> k' ↓ f ↑ v))))

reset :: a --|Exp e b|-> b -> a --|Exp e r|-> b
reset f = exp (\ k v -> env (\ e -> pure (k • (idK ↓ f ↑ v <== e))))

shift :: (a • r --|Exp e r|-> r) -> e --|Exp e r|-> a
shift f = exp (\ k v -> idK ↓ f ↑ pure k <<∘ v)
