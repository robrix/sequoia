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
, module Focalized.Calculus.Negation
, module Focalized.Calculus.Falsity
, module Focalized.Calculus.Truth
, module Focalized.Calculus.Conjunction
, module Focalized.Calculus.Disjunction
, module Focalized.Calculus.Implication
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
  -- * Recursive
, Nu(..)
, NuF(..)
, Corecursive(..)
, Mu(..)
, MuF(..)
, foldMu
, unfoldMu
, refoldMu
, refold
, Recursive(..)
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
import           Focalized.Calculus.Conjunction
import           Focalized.Calculus.Context
import           Focalized.Calculus.Control
import           Focalized.Calculus.Core
import           Focalized.Calculus.Disjunction
import           Focalized.Calculus.Falsity
import           Focalized.Calculus.Implication
import           Focalized.Calculus.Negation
import           Focalized.Calculus.Quantification
import           Focalized.Calculus.Shift
import           Focalized.Calculus.Truth
import           Focalized.Polarity
import           Prelude hiding (init)

-- Sequents

runSeq :: Seq r i o -> ((o -> r) -> (i -> r))
runSeq = runCPS . getSeq

evalSeq :: Seq o i o -> (i -> o)
evalSeq = (`runSeq` id)

sequent :: ((o -> r) -> (i -> r)) -> Seq r i o
sequent = Seq . CPS

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

type Additive s = (AdditiveTruth s, AdditiveFalsity s, AdditiveConj s, AdditiveDisj s)


instance AdditiveTruth Seq where
  topR = pure (inr Top)

instance AdditiveFalsity Seq where
  zeroL = liftL (K absurdP)


instance AdditiveConj Seq where
  withL1 p = popL (pushL p . exl)
  withL2 p = popL (pushL p . exr)
  withR = liftA2 (liftA2 inlr)


instance AdditiveDisj Seq where
  sumL a b = popL (exlr (pushL a) (pushL b))
  sumR1 = mapR inl
  sumR2 = mapR inr


-- Multiplicative

type Multiplicative s = (MultiplicativeFalsity s, MultiplicativeTruth s, MultiplicativeDisj s, MultiplicativeConj s)


instance MultiplicativeFalsity Seq where
  botL = liftL (K absurdN)
  botR = wkR

instance MultiplicativeTruth Seq where
  oneL = wkL
  oneR = liftR One


instance MultiplicativeDisj Seq where
  parL a b = popL (exlr (pushL a) (pushL b))
  parR ab = (>>= inr . inl) |> inr . inr <$> ab


instance MultiplicativeConj Seq where
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


-- Recursive

data Nu r f = forall x . Pos x => Nu { getNu :: Down (x ~~r~> f x) ⊗ x }

instance Polarized N (Nu r f) where

newtype NuF r f a = NuF { getNuF :: Down (a ~~r~> f a) ⊗ a }

instance (Neg (f a), Pos a) => Polarized P (NuF r f a)

nu :: Pos x => NuF r f x -> Nu r f
nu r = Nu (getNuF r)

runNu :: Nu r f -> Exists r P (NuF r f)
runNu (Nu r) = Exists (dnI (NuF r))


class (Core s, Structural s, Implication s) => Corecursive s where
  nuL
    :: ForAllC Pos Neg f
    => Exists r P (NuF r f) < i -|s r|- o
    -- ----------------------------------
    ->             Nu  r f  < i -|s r|- o
  nuR
    :: ForAllC Pos Neg f
    => i -|s r|- o > Exists r P (NuF r f)
    -- ----------------------------------
    -> i -|s r|- o >             Nu  r f
  nuR'
    :: ForAllC Pos Neg f
    => i -|s r|- o >             Nu  r f
    -- ----------------------------------
    -> i -|s r|- o > Exists r P (NuF r f)
  nuR' p = wkR' p >>> nuL init

instance Corecursive Seq where
  nuL = mapL runNu
  nuR s = wkR' s >>> existsL (mapL nu init)


newtype Mu r f = Mu { getMu :: forall x . Neg x => Down (FAlg r f x) ~~r~> x }

type FAlg r f x = f x ~~r~> x

instance Polarized N (Mu r f) where

newtype MuF r f a = MuF { getMuF :: Down (FAlg r f a) ~~r~> a }

instance (Pos (f a), Neg a) => Polarized N (MuF r f a) where

mu :: ForAll r N (MuF r f) -> Mu r f
mu r = Mu (dnEFun (contramap (contramap getMuF) (runForAll r)))

foldMu :: Neg a => CPS r (f a) a -> CPS r (Mu r f) a
foldMu alg = liftCPS $ \ (Mu f) -> appFun f (Down (Fun alg))

unfoldMu :: Traversable f => CPS r a (f a) -> CPS r a (Mu r f)
unfoldMu coalg = cps $ \ a -> Mu $ liftFun' $ \ (Down (Fun alg)) -> appCPS (refoldCPS alg coalg) a

refoldMu :: (Traversable f, Neg b) => CPS r (f b) b -> CPS r a (f a) -> CPS r a b
refoldMu f g = foldMu f Cat.<<< unfoldMu g


refold :: Functor f => (f b -> b) -> (a -> f a) -> (a -> b)
refold f g = go where go = f . fmap go . g

dnESeq :: r ••Seq r a b -> Seq r a b
dnESeq = Seq . dnE . contramap (contramap getSeq)

dnEFun :: r ••(a ~~r~> b) -> (a ~~r~> b)
dnEFun = Fun . dnE . contramap (contramap getFun)


class (Core s, Structural s, Implication s, Universal s) => Recursive s where
  muL
    :: (ForAllC Neg Pos f, Neg a)
    => i -|s r|- o > f a ~~r~> a   ->   a < i -|s r|- o
    -- ------------------------------------------------
    ->              Mu r f < i -|s r|- o
  muL'
    :: ForAllC Neg Pos f
    =>             Mu  r f  < i -|s r|- o
    -- ----------------------------------
    -> ForAll r N (MuF r f) < i -|s r|- o
  muL' p = muR init >>> wkL' p
  muR
    :: ForAllC Neg Pos f
    => i -|s r|- o > ForAll r N (MuF r f)
    -- ----------------------------------
    -> i -|s r|- o >             Mu  r f

instance Recursive Seq where
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


-- Utilities

newtype (f · g) a = C { getC :: f (g a) }
  deriving (Eq, Foldable, Functor, Ord, Show)

infixr 7 ·

deriving instance (Traversable f, Traversable g) => Traversable (f · g)

instance Polarized p (f (g a)) => Polarized p ((f · g) a) where

instance (Applicative f, Applicative g) => Applicative (f · g) where
  pure = C . pure . pure
  f <*> a = C ((<*>) <$> getC f <*> getC a)
