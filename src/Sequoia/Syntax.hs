module Sequoia.Syntax
( NExpr(..)
, PExpr(..)
) where

import Control.Applicative (liftA2)
import Control.Monad (ap)
import Data.Profunctor
import Sequoia.Calculus.Bottom
import Sequoia.Conjunction
import Sequoia.Connective.Negate as Negate
import Sequoia.Connective.Not
import Sequoia.Connective.One
import Sequoia.Connective.Sum
import Sequoia.Connective.Tensor
import Sequoia.Connective.Top
import Sequoia.Connective.True
import Sequoia.Connective.With
import Sequoia.Connective.Zero
import Sequoia.Monad.Run
import Sequoia.Profunctor.Context
import Sequoia.Profunctor.Continuation

class NExpr rep where
  bottomL :: rep e r (Bottom r) -> rep e r a
  topR :: rep e r Top
  withL1 :: rep e r (a • r) -> rep e r ((a & b) • r)
  withL2 :: rep e r (b • r) -> rep e r ((a & b) • r)
  withR :: rep e r a -> rep e r b -> rep e r (a & b)
  parL :: rep e r (a • r) -> rep e r (b • r) -> rep e r (Par r a b • r)
  parR :: (forall x . (rep e r a -> rep e r x) -> (rep e r b -> rep e r x) -> rep e r x) -> rep e r (Par r a b)
  funL :: rep e r a -> (rep e r b -> rep e r r) -> (rep e r (Fun r a b) -> rep e r r)
  funR :: (rep e r a -> rep e r b) -> rep e r (Fun r a b)
  notL :: rep e r a -> (rep e r (Not r a) -> rep e r r)
  notR :: (rep e r a -> rep e r r) -> rep e r (Not r a)

class PExpr rep where
  zeroL :: rep e r Zero -> rep e r a
  oneR :: rep e r (One e)
  sumL :: rep e r (a • r) -> rep e r (b • r) -> rep e r ((a ⊕ b) • r)
  sumR1 :: rep e r a -> rep e r (a ⊕ b)
  sumR2 :: rep e r b -> rep e r (a ⊕ b)
  tensorL :: (rep e r a -> rep e r b -> rep e r o) -> (rep e r (a ⊗ b) -> rep e r o)
  tensorR :: rep e r a -> rep e r b -> rep e r (a ⊗ b)
  subL :: (rep e r a -> rep e r b) -> (rep e r (Sub r a b) -> rep e r r)
  subR :: rep e r a -> (rep e r b -> rep e r r) -> rep e r (Sub r a b)
  trueR :: rep e r a -> rep e r (True r a)
  negateL :: rep e r a -> (rep e r (Negate e r a) -> rep e r r)
  negateR :: (rep e r a -> rep e r r) -> rep e r (Negate e r a)

runEval :: a • r -> Eval e r a -> e ==> r
runEval k m = getEval m k

runEvalK :: e -> Eval e r (a • r) -> a • r
runEvalK e m = K (\ a -> runEval (dn a) m <== e)

evalEval :: Eval e r r -> e ==> r
evalEval = runEval idK

newtype Eval e r a = Eval { getEval :: a • r -> e ==> r }

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
  withR l r = inlr <$> l <*> r
  parL f g = Eval (\ k -> C (\ e -> k • K (\ s -> runPar s (runEvalK e f) (runEvalK e g))))
  parR f = env (\ e -> pure (Par (\ g h -> evalEval (f (fmap (g •)) (fmap (h •))) <== e)))
  funL a b f = appFun <$> f <*> a <*> evalK b
  funR f = Fun <$> evalF f
  notL a n = (•) . getNot <$> n <*> a
  notR f = Not <$> evalK f

instance PExpr Eval where
  zeroL = fmap absurdP
  oneR = Eval (\ k -> C ((k •) . One))
  sumL f g = Eval (\ k -> C (\ e -> k • (K (\ a -> runEval (dn a) f <== e) <••> K (\ b -> runEval (dn b) g <== e))))
  sumR1 = fmap InL
  sumR2 = fmap InR
  tensorL f s = do
    a :⊗ b <- s
    f (pure a) (pure b)
  tensorR = liftA2 (:⊗)
  subL f s = do
    f <- evalF f
    s <- s
    pure (f (subK s) • subA s)
  subR a b = Sub <$> a <*> evalK b
  trueR = fmap true
  negateL a n = (•) . negateK <$> n <*> a
  negateR f = env (\ e -> Negate.negate e <$> evalK f)

newtype Par r a b = Par { runPar :: a • r -> b • r -> r }

newtype Fun r a b = Fun { runFun :: b • r -> a • r }

appFun :: Fun r a b -> a -> b • r -> r
appFun f a b = runFun f b • a

evalK :: (Eval e r a -> Eval e r r) -> Eval e r (a • r)
evalK = fmap ($ idK) . evalF

evalF :: (Eval e r a -> Eval e r b) -> Eval e r (b • r -> a • r)
evalF f = env (\ e -> pure (\ k -> K ((<== e) . runEval k . f . pure)))


data Sub r a b = Sub { subA :: a, subK :: b • r }
