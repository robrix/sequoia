{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}
module Focalized.Calculus
( -- * Sequents
  runSeq
, evalSeq
, Seq(..)
, liftLR
, lowerLR
  -- * Effectful sequents
, runSeqT
, SeqT(..)
  -- * Contexts
, module Focalized.Calculus.Context
  -- * Core rules
, module Focalized.Calculus.Core
  -- * Control
, module Focalized.Calculus.Control
  -- * Connectives
, module Focalized.Calculus.Bottom
, module Focalized.Calculus.Disjunction
, module Focalized.Calculus.Implication
, module Focalized.Calculus.Negation
, module Focalized.Calculus.One
, module Focalized.Calculus.Quantification
, module Focalized.Calculus.Recursion
, module Focalized.Calculus.Tensor
, module Focalized.Calculus.Top
, module Focalized.Calculus.With
, module Focalized.Calculus.Zero
  -- * Additive
, Additive
  -- * Multiplicative
, Multiplicative
  -- * Implication
, runFun
  -- * Quantification
, Quantification
, ForAll(..)
, Universal(..)
, Exists(..)
, Existential(..)
  -- * Polarity
, module Focalized.Polarity
  -- * Polarity shifts
, Shifting
, module Focalized.Calculus.Shift
) where

import           Control.Applicative (liftA2)
import qualified Control.Category as Cat
import           Control.Monad.Trans.Class
import           Data.Functor.Contravariant (contramap)
import           Data.Profunctor
import           Focalized.CPS
import           Focalized.Calculus.Bottom
import           Focalized.Calculus.Context
import           Focalized.Calculus.Control
import           Focalized.Calculus.Core
import           Focalized.Calculus.Disjunction
import           Focalized.Calculus.Implication
import           Focalized.Calculus.Negation
import           Focalized.Calculus.One
import           Focalized.Calculus.Quantification
import           Focalized.Calculus.Recursion
import           Focalized.Calculus.Shift
import           Focalized.Calculus.Tensor
import           Focalized.Calculus.Top
import           Focalized.Calculus.With
import           Focalized.Calculus.Zero
import           Focalized.Polarity
import           Prelude hiding (init)

-- Sequents

runSeq :: Seq r i o -> ((o -> r) -> (i -> r))
runSeq = runCPS . getSeq

evalSeq :: Seq o i o -> (i -> o)
evalSeq = (`runSeq` id)

sequent :: ((o -> r) -> (i -> r)) -> Seq r i o
sequent = Seq . CPS

dnESeq :: r ••Seq r a b -> Seq r a b
dnESeq = Seq . dnE . contramap (contramap getSeq)

newtype Seq r i o = Seq { getSeq :: CPS r i o }
  deriving (Applicative, Cat.Category, Functor, Monad, Profunctor)

liftLR :: CPS r a b -> Seq r (a < i) (o > b)
liftLR = Seq . dimap exl inr


lowerLR :: (CPS r a b -> Seq r i o) -> Seq r (a < i) (o > b) -> Seq r i o
lowerLR f p = sequent $ \ k i -> runSeq (f (CPS (\ kb a -> runSeq p (k |> kb) (a <| i)))) k i


-- Effectful sequents

runSeqT :: SeqT r i m o -> ((o -> m r) -> (i -> m r))
runSeqT = runSeq . getSeqT

newtype SeqT r i m o = SeqT { getSeqT :: Seq (m r) i o }
  deriving (Applicative, Functor, Monad)

instance MonadTrans (SeqT r i) where
  lift m = SeqT (Seq (CPS (\ k _ -> m >>= k)))


-- Core rules

instance Core Seq where
  f >>> g = f >>= pure |> pushL g

  init = popL liftR


-- Structural rules

deriving via Contextually Seq instance Weaken   Seq
deriving via Contextually Seq instance Contract Seq
deriving via Contextually Seq instance Exchange Seq


-- Contextual rules

instance Contextual Seq where
  popL f = sequent $ \ k -> uncurryConj ((`runSeq` k) . f)
  pushL s a = sequent $ \ k -> runSeq s k . (a <|)

  popR f = sequent $ \ k -> runSeq (f (K (k . inr))) (k . inl)
  pushR s a = sequent $ \ k -> runSeq s (k |> runK a)


-- Control

instance Control Seq where
  reset s = sequent (. evalSeq s)
  shift p = sequent (\ k -> runSeq p (k . inl |> id) . (K (k . inr) <|))


-- Negation

instance NegNegation Seq where
  notL = notLK . kL
  notR = notRK . kR

instance PosNegation Seq where
  negateL = negateLK . kL
  negateR = negateRK . kR


-- Additive

type Additive s = (NegTruth s, PosFalsity s, NegConjunction s, AdditiveDisj s)


instance NegTruth Seq where
  topR = pure (inr Top)

instance PosFalsity Seq where
  zeroL = liftL (K absurdP)


instance NegConjunction Seq where
  withL1 p = popL (pushL p . exl)
  withL2 p = popL (pushL p . exr)
  withR = liftA2 (liftA2 inlr)


instance AdditiveDisj Seq where
  sumL a b = popL (exlr (pushL a) (pushL b))
  sumR1 = mapR inl
  sumR2 = mapR inr


-- Multiplicative

type Multiplicative s = (NegFalsity s, PosTruth s, MultiplicativeDisj s, PosConjunction s)


instance NegFalsity Seq where
  botL = liftL (K absurdN)
  botR = wkR

instance PosTruth Seq where
  oneL = wkL
  oneR = liftR One


instance MultiplicativeDisj Seq where
  parL a b = popL (exlr (pushL a) (pushL b))
  parR ab = (>>= inr . inl) |> inr . inr <$> ab


instance PosConjunction Seq where
  tensorL p = popL (pushL2 p . exl <*> exr)
  tensorR = liftA2 (liftA2 inlr)


-- Implication

runFun :: (a ~~r~> b) -> Seq r (a < i) (o > b)
runFun = Seq . dimap exl inr . getFun


instance Implication Seq where
  funL a b = popL (\ f -> a >>> runFun f >>> wkL' b)
  funR = lowerLR (liftR . Fun) . wkR'

instance Subtraction Seq where
  subL b = popL (\ s -> liftR (subA s) >>> b >>> liftL (getNegate (subK s)))
  subR a b = liftA2 Sub <$> a <*> negateR b


-- Quantification

type Quantification s = (Universal s, Existential s)


instance Universal Seq where
  forAllL p = mapL (notNegate . runForAll) p
  forAllR p = sequent $ \ k a -> k (inr (ForAll (K (\ k' -> runSeq p (k . inl |> runK k') a))))


instance Existential Seq where
  existsL p = popL (dnESeq . runExists (pushL p))
  existsR p = mapR (Exists . dnI) p


-- Recursion

instance Corecursion Seq where
  nuL = mapL runNu
  nuR s = wkR' s >>> existsL (mapL nu init)

instance Recursion Seq where
  muL f k = wkL (downR f) >>> exL (mapL getMu (funL init (wkL' k)))
  muR = mapR mu


-- Polarity shifts

type Shifting s = (NegShift s, PosShift s)


instance NegShift Seq where
  upL   = mapL getUp
  upR   = mapR Up

instance PosShift Seq where
  downL = mapL getDown
  downR = mapR Down
