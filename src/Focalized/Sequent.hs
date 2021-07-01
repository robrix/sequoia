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
import           Focalized.Calculus.Implicative
import           Focalized.Calculus.Mu
import           Focalized.Calculus.Multiplicative
import           Focalized.Calculus.Negation
import           Focalized.Calculus.Nu
import           Focalized.Calculus.Quantification
import           Focalized.Calculus.Shift
import           Focalized.Conjunction
import           Focalized.Disjunction
import           Prelude hiding (init)

-- Sequents

runSeq :: _Γ -|Seq r|- _Δ -> (r •_Δ -> r •_Γ)
runSeq = runCPS . getSeq

evalSeq :: _Γ -|Seq _Δ|- _Δ -> _Δ •_Γ
evalSeq = (`runSeq` idK)

sequent :: (r •_Δ -> r •_Γ) -> _Γ -|Seq r|- _Δ
sequent = Seq . CPS

dnESeq :: r ••(_Γ -|Seq r|- _Δ) -> _Γ -|Seq r|- _Δ
dnESeq = Seq . dnE . contramap (contramap getSeq)

newtype Seq r _Γ _Δ = Seq { getSeq :: _Γ -|CPS r|- _Δ }
  deriving (Applicative, Cat.Category, Functor, Monad, Profunctor)

liftLR :: CPS r a b -> Seq r (a < _Γ) (_Δ > b)
liftLR = Seq . dimap exl inr


lowerLR :: (a -|CPS r|- b -> _Γ -|Seq r|- _Δ) -> a < _Γ -|Seq r|- _Δ > b -> _Γ -|Seq r|- _Δ
lowerLR f p = sequent $ K . \ k i -> runSeq (f (CPS (\ kb -> runSeq p (k |> kb) •<< (<| i)))) k • i


-- Effectful sequents

runSeqT :: SeqT r _Γ m _Δ -> (m r •_Δ -> m r •_Γ)
runSeqT = runSeq . getSeqT

newtype SeqT r _Γ m _Δ = SeqT { getSeqT :: Seq (m r) _Γ _Δ }
  deriving (Applicative, Functor, Monad)

instance MonadTrans (SeqT r _Γ) where
  lift m = SeqT (Seq (CPS (liftK (const . (m >>=)))))


-- Core rules

instance Core Seq where
  f >>> g = f >>= pure <--> pushL g

  init = popL liftR


-- Structural rules

deriving via Contextually Seq instance Weaken   Seq
deriving via Contextually Seq instance Contract Seq
deriving via Contextually Seq instance Exchange Seq


-- Contextual rules

instance Contextual Seq where
  swapΓΔ f _Δ' _Γ' = sequent $ K . \ _Δ _Γ -> runSeq (f _Δ _Γ) _Δ' • _Γ'


-- Control

instance Control Seq where
  reset s = sequent (•<< (evalSeq s •))
  shift p = sequent (\ k -> runSeq p ((k •<< inl) |> idK) •<< ((k •<< inr) <|))


-- Negation

instance NegNegation Seq where
  notL = notLK . kL
  notR = notRK . kR

instance PosNegation Seq where
  negateL = negateLK . kL
  negateR = negateRK . kR


-- Additive

instance TopIntro Seq where
  topR = pure (inr Top)

instance ZeroIntro Seq where
  zeroL = liftL (K absurdP)

instance WithIntro Seq where
  withL1 p = popL (pushL p . exl)
  withL2 p = popL (pushL p . exr)
  withR = liftA2 (liftA2 (-><-))

instance SumIntro Seq where
  sumL a b = popL (pushL a <--> pushL b)
  sumR1 = mapR inl
  sumR2 = mapR inr


-- Multiplicative

instance BottomIntro Seq where
  botL = liftL (K absurdN)
  botR = wkR

instance OneIntro Seq where
  oneL = wkL
  oneR = liftR One

instance ParIntro Seq where
  parL a b = popL (pushL a <--> pushL b)
  parR = fmap ((>>= inr . inl) <--> inr . inr)

instance TensorIntro Seq where
  tensorL p = popL (pushL2 p . exl <*> exr)
  tensorR = liftA2 (liftA2 (-><-))


-- Implication

instance FunctionIntro Seq where
  funL a b = popL (\ f -> a >>> liftLR (getFun f) >>> wkL' b)
  funR = lowerLR (liftR . Fun) . wkR'

instance SubtractionIntro Seq where
  subL b = popL (\ s -> liftR (subA s) >>> b >>> liftL (subK s))
  subR a b = liftA2 Sub <$> a <*> kR b


-- Quantification

instance Universal Seq where
  forAllL p = mapL (notNegate . runForAll) p
  forAllR p = sequent $ K . \ k a -> k • inr (ForAll (K ((• a) . runSeq p . ((k •<< inl) |>))))

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

instance NegShift Seq where
  upL   = mapL getUp
  upR   = mapR Up

instance PosShift Seq where
  downL = mapL getDown
  downR = mapR Down
