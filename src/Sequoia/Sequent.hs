module Sequoia.Sequent
( -- * Sequents
  evalSeq
, runSeq
, Seq(..)
, liftLR
, lowerLR
  -- * Effectful sequents
, runSeqT
, SeqT(..)
) where

import qualified Control.Category as Cat
import           Control.Monad.Trans.Class
import           Data.Profunctor
import           Data.Profunctor.Traversing
import           Prelude hiding (init)
import           Sequoia.Calculus.Additive
import           Sequoia.Calculus.Context
import           Sequoia.Calculus.Control as Calculus
import           Sequoia.Calculus.Core
import           Sequoia.Calculus.Iff
import           Sequoia.Calculus.Implicative
import           Sequoia.Calculus.Mu
import           Sequoia.Calculus.Multiplicative
import           Sequoia.Calculus.Negation
import           Sequoia.Calculus.NotUntrue
import           Sequoia.Calculus.Nu
import           Sequoia.Calculus.Quantification
import           Sequoia.Calculus.Shift
import           Sequoia.Calculus.Structural
import           Sequoia.Calculus.True
import           Sequoia.Calculus.XOr
import           Sequoia.Conjunction
import           Sequoia.Contextual
import           Sequoia.Continuation as K
import           Sequoia.Disjunction
import           Sequoia.Functor.Source
import           Sequoia.Optic.Getter
import           Sequoia.Optic.Review
import           Sequoia.Profunctor.Coexponential
import           Sequoia.Profunctor.Context
import           Sequoia.Profunctor.Exponential as Exponential hiding ((>>>))
import           Sequoia.Value

-- Sequents

evalSeq :: _Γ -|Seq _Γ _Δ|- _Δ -> (_Γ -> _Δ)
evalSeq = evalExp

runSeq :: Seq e r _Γ _Δ -> ((e -> _Γ) -> (_Δ -> r) -> (e -> r))
runSeq s f g = evalSeq (dimap f g s)

newtype Seq e r _Γ _Δ = Seq { getSeq :: Coexp e r _Δ _Γ -> C e r }
  deriving (Applicative, Functor, Monad) via (Exp e r _Γ)
  deriving (Cat.Category, Choice, Profunctor, Strong, Traversing) via (Exp e r)
  deriving (Env2, Exponential) via Exp


liftLR :: Exponential d => d e r a b -> Seq e r (a < _Γ) (_Δ > b)
liftLR = dimap exl inr . coerceExp

lowerLR :: Exponential d => (d e r a b -> _Γ -|Seq e r|- _Δ) -> a < _Γ -|Seq e r|- _Δ > b -> _Γ -|Seq e r|- _Δ
lowerLR f p = inExp (\ c -> exExp (f (inExp (exExp p . extendContexts c))) c)

extendContexts :: Coexp e r _Δ _Γ -> Coexp e r b a -> Coexp e r (_Δ > b) (a < _Γ)
extendContexts (Coexp _Γ _Δ) (Coexp a b) = Coexp (a <| _Γ) (_Δ |> b)


-- Effectful sequents

runSeqT :: SeqT e r _Γ m _Δ -> ((e -> _Γ) -> (_Δ -> m r) -> (e -> m r))
runSeqT = runSeq . getSeqT

newtype SeqT e r _Γ m _Δ = SeqT { getSeqT :: Seq e (m r) _Γ _Δ }
  deriving (Applicative, Functor, Monad)

instance MonadTrans (SeqT r s _Γ) where
  lift m = SeqT (inExp (C . const . (m >>=) . (•) . forget))


-- Core rules

instance Core Seq where
  f >>> g = f >>= pure <--> pushL g . inV0

  init = dimap exl inr Cat.id


-- Structural rules

deriving via Contextually Seq instance Weaken   Seq
deriving via Contextually Seq instance Contract Seq
deriving via Contextually Seq instance Exchange Seq


-- Contextual rules

instance Contextual Seq where
  swapΓΔ f c' = inExp (\ c -> exExp (f c) c')


-- Control

instance Calculus.Control Seq where
  reset s = inExp (\ (Coexp _Γ _Δ) -> C (exK _Δ . runC (exExp s (Coexp _Γ idK))))
  shift s = inExp (\ (Coexp _Γ _Δ) -> exExp s (Coexp (inV0 (inrK _Δ) <| _Γ) (inlK _Δ |> idK)))


-- Assertion

instance NotUntrueIntro Seq where
  notUntrueL e a = popL (val2 (\ (NotUntrue r) -> e >>> liftLR @Exp (r ^. _SrcExp @_ @Exp) >>> wkL' a))
  notUntrueR s = mapR (\ f -> NotUntrue (_SrcExp @Fun # f)) (funR s)

instance TrueIntro Seq where
  trueL = mapL trueA
  trueR = mapR true


-- Negation

instance NotIntro Seq where
  notL = notLK . kL
  notR = notRK . kR

instance NegateIntro Seq where
  negateL = negateLK . kL
  negateR = negateRK . kR


-- Additive

instance TopIntro Seq where
  topR = pure (inr Top)

instance ZeroIntro Seq where
  zeroL = liftL (inK absurdP)

instance WithIntro Seq where
  withL1 p = popL (pushL p . exlF)
  withL2 p = popL (pushL p . exrF)
  withR = mapR2 inlr

instance SumIntro Seq where
  sumL a b = popL (env2 . (pushL a <∘∘> pushL b))
  sumR1 = mapR inl
  sumR2 = mapR inr


-- Multiplicative

instance BottomIntro Seq where
  botL = liftL (inK absurdN)
  botR = wkR

instance OneIntro Seq where
  oneL = wkL
  oneR = liftR (inV0 One)

instance ParIntro Seq where
  parL a b = popL (env2 . (pushL a <∘∘> pushL b))
  parR = fmap ((>>= inr . inl) <--> inr . inr)

instance TensorIntro Seq where
  tensorL p = popL (pushL2 p . exlF <*> exrF)
  tensorR = mapR2 inlr


-- Logical biconditional/exclusive disjunction

instance IffIntro Seq where
  iffL1 s1 s2 = mapL getIff (withL1 (downR s1 ->⊢ s2))

  iffL2 s1 s2 = mapL getIff (withL2 (downR s1 ->⊢ s2))

  iffR s1 s2 = mapR Iff (funR (downL s1) ⊢& funR (downL s2))

instance XOrIntro Seq where
  xorL s1 s2 = mapL getXOr (subL (upR s1) ⊕⊢ subL (upR s2))

  xorR1 s1 s2 = mapR XOr (sumR1 (s1 ⊢>- upL s2))

  xorR2 s1 s2 = mapR XOr (sumR2 (s1 ⊢>- upL s2))


-- Implication

instance FunctionIntro Seq where
  funL a b = popL (val2 (\ f -> a >>> liftLR f >>> wkL' b))
  funR = lowerLR (liftR . inV0) . wkR'

instance SubtractionIntro Seq where
  subL f = popL (val2 (\ s -> liftR (s^.subA_) >>> f >>> liftL (s^.subK_)))
  subR a b = wkR' a >>> popΓL (\ a -> lowerL (liftR . inV0 . inCoexp a) (wkR b))


-- Quantification

instance UniversalIntro Seq where
  forAllL p = mapL (notNegate . runForAll) p
  forAllR p = inExp (\ (Coexp _Γ _Δ) -> liftRes (\ run -> inrK _Δ •• ForAll (inK (\ k -> run (exExp p (Coexp _Γ (inlK _Δ |> k)))))))

instance ExistentialIntro Seq where
  existsL p = popL (val2 (dnE . runExists (pushL p . inV0)))
  existsR p = mapR (Exists . liftDN) p


-- Recursion

instance NuIntro Seq where
  nuL = mapL runNu
  nuR s = wkR' s >>> existsL (mapL nu init)

instance MuIntro Seq where
  muL f k = wkL (downR f) >>> exL (mapL getMu (funL init (wkL' k)))
  muR = mapR mu


-- Polarity shifts

instance UpIntro Seq where
  upL   = mapL getUp
  upR   = mapR Up

instance DownIntro Seq where
  downL = mapL getDown
  downR = mapR Down
