module Focalized.Sequent
( -- * Sequents
  runSeq
, evalSeq
, sequent
, dnESeq
, Seq(..)
, liftLR
, lowerLR
  -- * Effectful sequents
, runSeqT
, SeqT(..)
) where

import           Control.Applicative (liftA2)
import qualified Control.Category as Cat
import           Control.Monad.Trans.Class
import           Data.Functor.Contravariant
import           Data.Profunctor
import           Focalized.CPS
import           Focalized.Calculus.Additive
import           Focalized.Calculus.Context
import           Focalized.Calculus.Control
import           Focalized.Calculus.Core
import           Focalized.Calculus.Function
import           Focalized.Calculus.Mu
import           Focalized.Calculus.Multiplicative
import           Focalized.Calculus.Negation
import           Focalized.Calculus.Nu
import           Focalized.Calculus.Quantification
import           Focalized.Calculus.Shift
import           Focalized.Calculus.Subtraction
import           Focalized.Conjunction
import           Focalized.Disjunction
import           Prelude hiding (init)

-- Sequents

runSeq :: _Γ -|Seq r|- _Δ -> ((_Δ -> r) -> (_Γ -> r))
runSeq = runCPS . getSeq

evalSeq :: _Γ -|Seq _Δ|- _Δ -> (_Γ -> _Δ)
evalSeq = (`runSeq` id)

sequent :: ((_Δ -> r) -> (_Γ -> r)) -> _Γ -|Seq r|- _Δ
sequent = Seq . CPS

dnESeq :: r ••(_Γ -|Seq r|- _Δ) -> _Γ -|Seq r|- _Δ
dnESeq = Seq . dnE . contramap (contramap getSeq)

newtype Seq r _Γ _Δ = Seq { getSeq :: _Γ -|CPS r|- _Δ }
  deriving (Applicative, Cat.Category, Functor, Monad, Profunctor)

liftLR :: CPS r a b -> Seq r (a < _Γ) (_Δ > b)
liftLR = Seq . dimap exl inr


lowerLR :: (a -|CPS r|- b -> _Γ -|Seq r|- _Δ) -> a < _Γ -|Seq r|- _Δ > b -> _Γ -|Seq r|- _Δ
lowerLR f p = sequent $ \ k i -> runSeq (f (CPS (\ kb a -> runSeq p (k |> kb) (a <| i)))) k i


-- Effectful sequents

runSeqT :: SeqT r _Γ m _Δ -> ((_Δ -> m r) -> (_Γ -> m r))
runSeqT = runSeq . getSeqT

newtype SeqT r _Γ m _Δ = SeqT { getSeqT :: Seq (m r) _Γ _Δ }
  deriving (Applicative, Functor, Monad)

instance MonadTrans (SeqT r _Γ) where
  lift m = SeqT (Seq (CPS (\ k _ -> m >>= k)))


-- Core rules

instance Core (Seq r) where
  f >>> g = f >>= pure |> pushL g

  init = popL liftR


-- Structural rules

deriving via Contextually (Seq r) r instance Weaken   (Seq r)
deriving via Contextually (Seq r) r instance Contract (Seq r)
deriving via Contextually (Seq r) r instance Exchange (Seq r)


-- Contextual rules

instance Contextual r (Seq r) where
  popL f = sequent $ \ k -> uncurryConj ((`runSeq` k) . f)
  pushL s a = sequent $ \ k -> runSeq s k . (a <|)

  popR f = sequent $ \ k -> runSeq (f (K (k . inr))) (k . inl)
  pushR s a = sequent $ \ k -> runSeq s (k |> runK a)


-- Control

instance Control Seq where
  reset s = sequent (. evalSeq s)
  shift p = sequent (\ k -> runSeq p (k . inl |> id) . (K (k . inr) <|))


-- Negation

instance NegNegation r (Seq r) where
  notL = notLK . kL
  notR = notRK . kR

instance PosNegation r (Seq r) where
  negateL = negateLK . kL
  negateR = negateRK . kR


-- Additive

instance NegTruth (Seq r) where
  topR = pure (inr Top)

instance PosFalsity (Seq r) where
  zeroL = liftL (K absurdP)

instance NegConjunction (Seq r) where
  withL1 p = popL (pushL p . exl)
  withL2 p = popL (pushL p . exr)
  withR = liftA2 (liftA2 (-><-))

instance PosDisjunction (Seq r) where
  sumL a b = popL (pushL a <--> pushL b)
  sumR1 = mapR inl
  sumR2 = mapR inr


-- Multiplicative

instance NegFalsity (Seq r) where
  botL = liftL (K absurdN)
  botR = wkR

instance PosTruth (Seq r) where
  oneL = wkL
  oneR = liftR One

instance NegDisjunction (Seq r) where
  parL a b = popL (pushL a <--> pushL b)
  parR ab = (>>= inr . inl) |> inr . inr <$> ab

instance PosConjunction (Seq r) where
  tensorL p = popL (pushL2 p . exl <*> exr)
  tensorR = liftA2 (liftA2 (-><-))


-- Implication

instance Implication r (Seq r) where
  funL a b = popL (\ f -> a >>> liftLR (getFun f) >>> wkL' b)
  funR = lowerLR (liftR . Fun) . wkR'

instance Subtraction r (Seq r) where
  subL b = popL (\ s -> liftR (subA s) >>> b >>> liftL (getNegate (subK s)))
  subR a b = liftA2 Sub <$> a <*> negateR b


-- Quantification

instance Universal r (Seq r) where
  forAllL p = mapL (notNegate . runForAll) p
  forAllR p = sequent $ \ k a -> k (inr (ForAll (K (\ k' -> runSeq p (k . inl |> runK k') a))))

instance Existential r (Seq r) where
  existsL p = popL (dnESeq . runExists (pushL p))
  existsR p = mapR (Exists . dnI) p


-- Recursion

instance Corecursion r (Seq r) where
  nuL = mapL runNu
  nuR s = wkR' s >>> existsL (mapL nu init)

instance Recursion r (Seq r) where
  muL f k = wkL (downR f) >>> exL (mapL getMu (funL init (wkL' k)))
  muR = mapR mu


-- Polarity shifts

instance NegShift (Seq r) where
  upL   = mapL getUp
  upR   = mapR Up

instance PosShift (Seq r) where
  downL = mapL getDown
  downR = mapR Down
