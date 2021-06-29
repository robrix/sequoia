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

instance Core Seq where
  f >>> g = f >>= pure |> pushL g

  init = popL liftR


-- Structural rules

deriving via Contextually Seq instance Weaken   Seq
deriving via Contextually Seq instance Contract Seq
deriving via Contextually Seq instance Exchange Seq


-- Contextual rules

instance Contextual Seq where
  popLn f = sequent $ \ k _Γ -> runSeq (f _Γ) k Γ
  popRn f = sequent $ \ k _Γ -> runSeq (f (K k)) absurdΔ _Γ

  pushLn s _Γ = sequent $ \ k -> runSeq s k . const _Γ
  pushRn s _Δ = sequent $ \ _ -> runSeq s (_Δ •)


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

instance NegTruth Seq where
  topR = pure (inr Top)

instance PosFalsity Seq where
  zeroL = liftL (K absurdP)

instance NegConjunction Seq where
  withL1 p = popL (pushL p . exl)
  withL2 p = popL (pushL p . exr)
  withR = liftA2 (liftA2 (-><-))

instance PosDisjunction Seq where
  sumL a b = popL (pushL a <--> pushL b)
  sumR1 = mapR inl
  sumR2 = mapR inr


-- Multiplicative

instance NegFalsity Seq where
  botL = liftL (K absurdN)
  botR = wkR

instance PosTruth Seq where
  oneL = wkL
  oneR = liftR One

instance NegDisjunction Seq where
  parL a b = popL (pushL a <--> pushL b)
  parR ab = (>>= inr . inl) |> inr . inr <$> ab

instance PosConjunction Seq where
  tensorL p = popL (pushL2 p . exl <*> exr)
  tensorR = liftA2 (liftA2 (-><-))


-- Implication

instance Implication Seq where
  funL a b = popL (\ f -> a >>> liftLR (getFun f) >>> wkL' b)
  funR = lowerLR (liftR . Fun) . wkR'

instance Subtraction Seq where
  subL b = popL (\ s -> liftR (subA s) >>> b >>> liftL (subK s))
  subR a b = liftA2 Sub <$> a <*> kR b


-- Quantification

instance Universal Seq where
  forAllL p = mapL (notNegate . runForAll) p
  forAllR p = sequent $ \ k a -> k (inr (ForAll (K (\ k' -> runSeq p (k . inl |> (k' •)) a))))

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
