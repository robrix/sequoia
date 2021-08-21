module Sequoia.Syntax
( NExpr(..)
, PExpr(..)
) where

import Control.Applicative (liftA2)
import Control.Monad (ap)
import Data.Distributive
import Data.Profunctor
import Sequoia.Calculus.Bottom
import Sequoia.Conjunction
import Sequoia.Connective.Negate as Negate
import Sequoia.Connective.Not
import Sequoia.Connective.NotUntrue
import Sequoia.Connective.One
import Sequoia.Connective.Par
import Sequoia.Connective.Sum
import Sequoia.Connective.Tensor
import Sequoia.Connective.Top
import Sequoia.Connective.True
import Sequoia.Connective.With
import Sequoia.Connective.Zero
import Sequoia.Disjunction
import Sequoia.Monad.Run
import Sequoia.Profunctor.Command
import Sequoia.Profunctor.Continuation
import Sequoia.Profunctor.Value

class NExpr rep where
  bottomL :: rep e r (Bottom r) -> rep e r a
  topR :: rep e r Top
  withL1 :: rep e r (a • r) -> rep e r ((a & b) • r)
  withL2 :: rep e r (b • r) -> rep e r ((a & b) • r)
  withR :: rep e r a -> rep e r b -> rep e r (a & b)
  parL :: rep e r (a • r) -> rep e r (b • r) -> rep e r ((a ⅋ b) • r)
  parR :: Either (rep e r a) (rep e r b) -> rep e r (a ⅋ b)
  funL :: rep e r a -> rep e r (b • r) -> rep e r (Fun e r a b • r)
  funR :: (rep e r a -> rep e r b) -> rep e r (Fun e r a b)
  notUntrueL :: rep e r (a • r) -> rep e r (NotUntrue e a • r)
  notUntrueR :: rep e r a -> rep e r (NotUntrue e a)
  notL :: rep e r a -> rep e r (Not a r • r)
  notR :: rep e r (a • r) -> rep e r (Not a r)

class PExpr rep where
  zeroL :: rep e r Zero -> rep e r a
  oneR :: rep e r (One e)
  sumL :: rep e r (a • r) -> rep e r (b • r) -> rep e r ((a ⊕ b) • r)
  sumR1 :: rep e r a -> rep e r (a ⊕ b)
  sumR2 :: rep e r b -> rep e r (a ⊕ b)
  tensorL :: (rep e r a -> rep e r b -> rep e r r) -> rep e r ((a ⊗ b) • r)
  tensorR :: rep e r a -> rep e r b -> rep e r (a ⊗ b)
  subL :: (rep e r a -> rep e r b) -> rep e r (Sub r a b • r)
  subR :: rep e r a -> rep e r (b • r) -> rep e r (Sub r a b)
  trueL :: rep e r (a • r) -> rep e r (True r a • r)
  trueR :: rep e r a -> rep e r (True r a)
  negateL :: rep e r a -> rep e r (Negate e a r • r)
  negateR :: rep e r (a • r) -> rep e r (Negate e a r)


runEval :: a • r -> Eval e r a -> e |-- r
runEval k m = getEval m k

evalF :: (Eval e r a -> Eval e r b) -> Eval e r (b • r -> a • r)
evalF f = env (\ e -> pure (\ k -> K ((<== e) . runEval k . f . pure)))

elim :: (a -> Eval e r r) -> Eval e r (a • r)
elim f = Eval (\ k -> C (\ e -> k • K (\ a -> runEval idK (f a) <== e)))

newtype Eval e r a = Eval { getEval :: a • r -> e |-- r }

instance Functor (Eval e r) where
  fmap f = Eval . lmap (lmap f) . getEval

instance Applicative (Eval e r) where
  pure a = Eval (pure . (• a))
  (<*>) = ap

instance Monad (Eval e r) where
  Eval m >>= f = Eval (\ k -> withRun (\ run -> m (K (run . runEval k . f))))

instance MonadEnv e (Eval e r) where
  env f = Eval (\ k -> env (runEval k . f))

instance MonadRes r (Eval e r) where
  res = Eval . const . pure
  liftRes f = Eval (\ k -> let run = runEval k in withRun (\ runC -> run (f (runC . run))))

instance NExpr Eval where
  bottomL b = Eval (\ _ -> runEval (K absurdN) b)
  topR = pure Top
  withL1 = fmap (lmap exl)
  withL2 = fmap (lmap exr)
  withR = liftA2 inlr
  parL f g = elim ((distribute f <••> distribute g) •)
  parR r = bisequenceDisj (coerceDisj r)
  funL a b = elim (\ f -> appFun f <$> a <*> b)
  funR f = Fun . fmap (Not . rmap Bottom) <$> evalF f
  notUntrueL a = env (\ e -> lmap ((e ∘) . runNotUntrue) <$> a)
  -- FIXME: this is always scoped statically
  notUntrueR = fmap (NotUntrue . pure)
  notL = fmap (runElim (rmap absurdN . getNot))
  notR = fmap (Not . rmap Bottom)

instance PExpr Eval where
  zeroL = fmap absurdP
  oneR = Eval (\ k -> C ((k •) . One))
  sumL f g = elim (collect (•) f <--> collect (•) g)
  sumR1 = fmap InL
  sumR2 = fmap InR
  tensorL f = elim (\ (a :⊗ b) -> f (pure a) (pure b))
  tensorR = liftA2 (:⊗)
  subL f = elim (\ s -> appSub s <$> evalF f)
  subR = liftA2 (:-<)
  trueL = fmap (lmap trueA)
  trueR = fmap true
  negateL = fmap (runElim negateK)
  negateR f = env (\ e -> Negate e <$> f)


newtype Fun e r a b = Fun (b • r -> a ¬ r)

instance Profunctor (Fun e r) where
  dimap f g (Fun r) = Fun (dimap (lmap g) (lmap f) r)

appFun :: Fun e r a b -> a -> b • r -> r
appFun (Fun f) a b = f b • a


data Sub r a b = a :-< (b • r)

appSub :: Sub r a b -> (b • r -> a • r) -> r
appSub (a :-< k) f = f k • a


runElim :: (a -> b • r) -> (b -> a • r)
runElim = fmap K . flip . fmap (•)
