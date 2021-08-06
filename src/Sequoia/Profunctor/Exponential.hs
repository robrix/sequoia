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
, runExp
, runExp'
, elimExp
, runExpFn
, runExpK
, (↑)
, (↓)
  -- ** Composition
, (<<<)
, (>>>)
  -- ** Computation
, mapExpE
, mapExpR
, mapExpFnK
, mapExpFnV
, mapExpFnC
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
import           Fresnel.Getter
import           Fresnel.Iso
import           Fresnel.Review
import           Fresnel.Setter
import           Prelude hiding (exp)
import           Sequoia.Conjunction
import           Sequoia.Disjunction
import           Sequoia.Monad.Run
import           Sequoia.Profunctor.Applicative
import           Sequoia.Profunctor.Coexponential
import           Sequoia.Profunctor.Context
import           Sequoia.Profunctor.Continuation as K
import           Sequoia.Profunctor.Diagonal
import           Sequoia.Profunctor.Value as V

-- Exponential profunctor

_Exp :: Iso
  (Exp e1 r1 a1 b1)                   (Exp e2 r2 a2 b2)
  (b1 • r1 -> e1 ∘ a1 -> e1 ==> r1)   (b2 • r2 -> e2 ∘ a2 -> e2 ==> r2)
_Exp = coerced

newtype Exp env res inn out = Exp ((out -> res) -> (env -> inn) -> (env -> res))

instance Profunctor (Exp e r) where
  dimap f g = exp . dimap (lmap g) (lmap (rmap f)) . runExp

instance Strong (Exp e r) where
  first'  r = exp (\ b -> val (\ (a, c) -> lmap (,c) b ↓ r ↑ pure a))
  second' r = exp (\ b -> val (\ (c, a) -> lmap (c,) b ↓ r ↑ pure a))

instance Choice (Exp e r) where
  left'  r = exp (\ b -> val ((\ v -> inlL b ↓ r ↑ pure v) <--> pure . (inrL b •)))
  right' r = exp (\ b -> val (pure . (inlL b •) <--> (\ v -> inrL b ↓ r ↑ pure v)))

instance Traversing (Exp e r) where
  wander traverse r = exp (\ k v -> val (\ s -> k ↓ traverse ((r <<<) . pure) s ↑ idV) v)

instance Diagonal (Exp e r) where
  dup = exp' dup

instance Codiagonal (Exp e r) where
  dedup = exp' dedup

instance Cat.Category (Exp e r) where
  id = exp (↓↑)
  f . g = contK (\ _K -> exp (\ c a -> _K (\ b -> c ↓ f ↑ pure b) ↓ g ↑ a))

instance Functor (Exp e r c) where
  fmap = rmap

instance Applicative (Exp e r a) where
  pure = exp . ckv . pure
  df <*> da = exp (\ b a -> cont (\ _K -> _K (\ f -> lmap f b ↓ da ↑ a) ↓ df ↑ a))

instance Monad (Exp e r a) where
  m >>= f = exp (\ k v -> cont (\ _K -> _K (\ b -> k ↓ f b ↑ v) ↓ m ↑ v))

instance MonadEnv e (Exp e r a) where
  env f = exp (\ k v -> env (\ e -> k ↓ f e ↑ v))

instance MonadRes r (Exp e r a) where
  res = exp . ckv . pure
  liftRes f = exp (\ k v -> env (\ e -> let run f = k ↓ f ↑ v in run (f ((<== e) . run))))

instance MonadRunK r (Exp e r a) where
  withRunK f = exp (\ k v -> withRun (\ run -> k ↓ f (\ k' m -> run (k' ↓ m ↑ v)) ↑ v))

instance Coapply (Coexp e r) (Exp e r) where
  coliftC2 f a b = exp (\ k v -> k ↓ a ↑ V (\ e -> f (v -< runExpK b e k)))
  f <&> a = exp (\ k v -> k ↓ f ↑ V (\ e -> v -< runExpK a e k))

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
expV = exp' . flip (∘)

expK :: a • r -> a --|Exp e r|-> r
expK = exp' . (•)

expKV :: a • r -> e ∘ a -> e --|Exp e r|-> r
expKV = fmap expC . (↓↑)

expC :: e ==> r -> e --|Exp e r|-> r
expC = exp' . (<==)

expFn :: ((b -> r) -> (e -> a) -> (e -> r)) -> Exp e r a b
expFn = coerce

expCoexp :: (Coexp e r b a -> e ==> r) -> Exp e r a b
expCoexp f = exp (fmap f . flip (-<))


-- Elimination

evalExp :: MonadEnv e m => e --|Exp e r|-> r -> m r
evalExp f = idK ↓ f ↑ idV

runExp :: a --|Exp e r|-> b -> b • r -> e ∘ a -> e ==> r
runExp = coerce

runExp' :: b • r -> e ∘ a -> a --|Exp e r|-> b -> e ==> r
runExp' k v f = runExp f k v

elimExp :: a --|Exp e r|-> b -> Coexp e r b a -> e ==> r
elimExp = unCoexp . flip . runExp

runExpFn :: Exp e r a b -> ((b -> r) -> (e -> a) -> (e -> r))
runExpFn = coerce

runExpK :: Exp e r a b -> e -> (b • r -> a • r)
runExpK f e k = K (\ a -> runExp f k (pure a) <== e)

(↑) :: (e ∘ a -> m r) -> e ∘ a -> m r
(↑) = ($)

infixl 2 ↑

(↓) :: MonadEnv e m => b • r -> a --|Exp e r|-> b -> e ∘ a -> m r
(k ↓ f) a = env (\ e -> pure (runExp f k a <== e))

infixl 3 ↓


-- Computation

mapExpE :: (forall x . Iso' (e1 ∘ x) (e2 ∘ x)) -> (Exp e1 r i o -> Exp e2 r i o)
mapExpE b = exp . mapExpFnC (over _CV (view b)) . mapExpFnV (review b) . runExp

mapExpR :: (forall x . Iso' (x • r2) (x • r1)) -> (Exp e r1 i o -> Exp e r2 i o)
mapExpR b = exp . mapExpFnC (over _CK (review b)) . mapExpFnK (view b) . runExp


mapExpFnK :: (forall x . x • r2 -> x • r1) -> (b • r1 -> e ∘ a -> e ==> r) -> (b • r2 -> e ∘ a -> e ==> r)
mapExpFnK = lmap

mapExpFnV :: (forall x . e2 ∘ x -> e1 ∘ x) -> (b • r -> e1 ∘ a -> e ==> r) -> (b • r -> e2 ∘ a -> e ==> r)
mapExpFnV = fmap . lmap

mapExpFnC :: (e1 ==> r1 -> e2 ==> r2) -> (b • r -> e ∘ a -> e1 ==> r1) -> (b • r -> e ∘ a -> e2 ==> r2)
mapExpFnC = rmap . rmap


dnE :: (a --|Exp e r|-> b) •• r -> a --|Exp e r|-> b
dnE k = exp (\ k' v -> cont (\ _K -> pure (k • _K (\ f -> k' ↓ f ↑ v))))

reset :: a --|Exp e b|-> b -> a --|Exp e r|-> b
reset f = exp (\ k v -> env (\ e -> pure (k • (idK ↓ f ↑ v <== e))))

shift :: (a • r --|Exp e r|-> r) -> e --|Exp e r|-> a
shift f = exp (\ k v -> idK ↓ f ↑ pure k <<∘ v)
