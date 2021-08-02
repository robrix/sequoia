{-# LANGUAGE FunctionalDependencies #-}
module Sequoia.Syntax
( Expr(..)
) where

import Control.Applicative (liftA2)
import Control.Monad (ap)
import Sequoia.Conjunction
import Sequoia.Connective.Negate
import Sequoia.Connective.Not
import Sequoia.Connective.One
import Sequoia.Connective.Sum
import Sequoia.Connective.Tensor
import Sequoia.Connective.Top
import Sequoia.Connective.With
import Sequoia.Profunctor.Context
import Sequoia.Profunctor.Continuation

class Expr e r rep | rep -> e r where
  top :: rep Top
  (&) :: rep a -> rep b -> rep (a & b)
  exlN :: rep (a & b) -> rep a
  exrN :: rep (a & b) -> rep b
  par :: (forall x . (rep a -> rep x) -> (rep b -> rep x) -> rep x) -> rep (Par r a b)
  exlrN :: rep (Par r a b) -> (rep a -> rep o) -> (rep b -> rep o) -> rep o
  not :: rep (a -> r) -> rep (Not r a)

  one :: rep (One e)
  inlP :: rep a -> rep (a ⊕ b)
  inrP :: rep b -> rep (a ⊕ b)
  exlrP :: rep (a ⊕ b) -> (rep a -> rep o) -> (rep b -> rep o) -> rep o
  (⊗) :: rep a -> rep b -> rep (a ⊗ b)
  extensor :: rep (a ⊗ b) -> (rep a -> rep b -> rep o) -> rep o
  negate :: rep (a -> r) -> rep (Negate e r a)

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

instance Expr e r (Eval e r) where
  top = pure Top
  l & r = inlr <$> l <*> r
  exlN = fmap exl
  exrN = fmap exr
  par f = env (\ e -> pure (Par (\ g h -> evalEval e (f (fmap g) (fmap h)))))
  exlrN s f g = do
    s' <- s
    Eval (\ k e -> runPar s' (runEval k e . f . pure) (runEval k e . g . pure))
  not = fmap (Not . K)

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
  negate a = do
    a' <- a
    Eval (\ k e -> k (Negate (\ f -> f e (K a'))))

newtype Par r a b = Par { runPar :: (a -> r) -> (b -> r) -> r }
