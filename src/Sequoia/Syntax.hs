module Sequoia.Syntax
( NExpr(..)
, PExpr(..)
) where

import Control.Applicative (liftA2)
import Control.Monad (ap)
import Sequoia.Conjunction
import Sequoia.Connective.Negate as Negate
import Sequoia.Connective.Not
import Sequoia.Connective.One
import Sequoia.Connective.Sum
import Sequoia.Connective.Tensor
import Sequoia.Connective.Top
import Sequoia.Connective.With
import Sequoia.Profunctor.Context
import Sequoia.Profunctor.Continuation

class NExpr rep where
  top :: rep e r Top
  (&) :: rep e r a -> rep e r b -> rep e r (a & b)
  exlN :: rep e r (a & b) -> rep e r a
  exrN :: rep e r (a & b) -> rep e r b
  par :: (forall x . (rep e r a -> rep e r x) -> (rep e r b -> rep e r x) -> rep e r x) -> rep e r (Par r a b)
  exlrN :: rep e r (Par r a b) -> (rep e r a -> rep e r o) -> (rep e r b -> rep e r o) -> rep e r o
  lam :: (rep e r a -> rep e r b) -> rep e r (Fun r a b)
  lamL :: rep e r a -> (rep e r b -> rep e r r) -> (rep e r (Fun r a b) -> rep e r r)
  not :: (rep e r a -> rep e r r) -> rep e r (Not r a)

class PExpr rep where
  one :: rep e r (One e)
  inlP :: rep e r a -> rep e r (a ⊕ b)
  inrP :: rep e r b -> rep e r (a ⊕ b)
  exlrP :: rep e r (a ⊕ b) -> (rep e r a -> rep e r o) -> (rep e r b -> rep e r o) -> rep e r o
  (⊗) :: rep e r a -> rep e r b -> rep e r (a ⊗ b)
  extensor :: rep e r (a ⊗ b) -> (rep e r a -> rep e r b -> rep e r o) -> rep e r o
  negate :: (rep e r a -> rep e r r) -> rep e r (Negate e r a)

runEval :: (a -> r) -> e -> Eval e r a -> r
runEval k e m = getEval m k e

evalEval :: e -> Eval e r r -> r
evalEval = runEval id

newtype Eval e r a = Eval { getEval :: (a -> r) -> (e -> r) }
  deriving (Functor)

instance Applicative (Eval e r) where
  pure a = Eval (\ k _ -> k a)
  (<*>) = ap

instance Monad (Eval e r) where
  Eval m >>= f = Eval (\ k e -> m (runEval k e . f) e)

instance MonadEnv e (Eval e r) where
  env f = Eval (\ k -> runEval k <*> f)

instance NExpr Eval where
  top = pure Top
  l & r = inlr <$> l <*> r
  exlN = fmap exl
  exrN = fmap exr
  par f = env (\ e -> pure (Par (\ g h -> evalEval e (f (fmap g) (fmap h)))))
  exlrN s f g = do
    s' <- s
    Eval (\ k e -> runPar s' (runEval k e . f . pure) (runEval k e . g . pure))
  lam f = env (\ e -> pure (Fun (\ b -> runEval b e . f . pure)))
  lamL a b f = do
    f <- f
    a <- a
    env (\ e -> pure (appFun f a (evalEval e . b . pure)))
  not f = env (\ e -> pure (Not (K (evalEval e . f . pure))))

instance PExpr Eval where
  one = Eval (. One)
  inlP = fmap InL
  inrP = fmap InR
  exlrP s f g = s >>= \case
    InL a -> f (pure a)
    InR b -> g (pure b)
  (⊗) = liftA2 (:⊗)
  extensor s f = do
    a :⊗ b <- s
    f (pure a) (pure b)
  negate f = env (\ e -> pure (Negate.negate e (K (evalEval e . f . pure))))

newtype Par r a b = Par { runPar :: (a -> r) -> (b -> r) -> r }

newtype Fun r a b = Fun { runFun :: (b -> r) -> (a -> r) }

appFun :: Fun r a b -> a -> (b -> r) -> r
appFun f = flip (runFun f)
