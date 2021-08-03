module Sequoia.Sequent
( -- * Sequents
  Seq(getSeq)
  -- * Construction
, liftLR
, lowerLR
, seq
, seqExp
, seqCoexp
, seqFn
  -- * Elimination
, evalSeq
, runSeq
, runSeqFn
, elimSeq
  -- * Effectful sequents
, runSeqT
, SeqT(..)
) where

import           Control.Arrow as Arrow hiding ((>>>), (|||))
import           Control.Category (Category(id))
import qualified Control.Category as Cat
import           Control.Monad.Trans.Class
import           Data.Coerce
import           Data.Profunctor
import           Data.Profunctor.Traversing
import           Fresnel.Getter
import           Fresnel.Review
import           Prelude hiding (exp, id, init, negate, seq)
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
import           Sequoia.Conjunction as Conj
import           Sequoia.Contextual
import           Sequoia.Disjunction as Disj
import           Sequoia.Monad.Run
import           Sequoia.Profunctor.Coexponential
import           Sequoia.Profunctor.Context
import           Sequoia.Profunctor.Continuation as K
import           Sequoia.Profunctor.Diagonal
import           Sequoia.Profunctor.Exponential as Exponential hiding ((>>>), (↓))
import           Sequoia.Profunctor.Value

-- Sequents

newtype Seq e r _Γ _Δ = Seq { getSeq :: _Δ • r -> e ∘ _Γ -> e ==> r }
  deriving (Applicative, Functor, Monad, MonadEnv e, MonadRes r) via (Exp e r _Γ)
  deriving (Arrow, ArrowApply, ArrowChoice, Category, Choice, Codiagonal, Diagonal, Profunctor, Strong, Traversing) via (Exp e r)

infixl 3 ↓


-- Construction

liftLR :: Exp e r a b -> Seq e r (a < _Γ) (_Δ > b)
liftLR = dimap exl inr . seqExp

lowerLR :: (Exp e r a b -> _Γ -|Seq e r|- _Δ) -> a < _Γ -|Seq e r|- _Δ > b -> _Γ -|Seq e r|- _Δ
lowerLR f p = seq (\ _Δ _Γ -> _Δ ↓ f (exp (\ b a -> _Δ |> b ↓ p ↑ a <| _Γ)) ↑ _Γ)

seq :: (_Δ • r -> e ∘ _Γ -> e ==> r) -> Seq e r _Γ _Δ
seq = Seq

seqExp :: Exp e r a b -> Seq e r a b
seqExp = seq . runExp

seqCoexp :: (Coexp e r b a -> e ==> r) -> Seq e r a b
seqCoexp = seqExp . expCoexp

seqFn :: ((_Δ -> r) -> (e -> _Γ) -> (e -> r)) -> Seq e r _Γ _Δ
seqFn = coerce


-- Elimination

evalSeq :: _Γ -|Seq _Γ _Δ|- _Δ -> (_Γ -> _Δ)
evalSeq = evalExp . exp . getSeq

runSeq :: Seq e r _Γ _Δ -> (_Δ • r -> e ∘ _Γ -> e ==> r)
runSeq = coerce

runSeqFn :: Seq e r _Γ _Δ -> ((_Δ -> r) -> (e -> _Γ) -> (e -> r))
runSeqFn = coerce

elimSeq :: _Γ -|Seq e r|- _Δ -> Coexp e r _Δ _Γ -> e ==> r
elimSeq = unCoexp . flip . getSeq

(↓) :: _Δ • r -> Seq e r _Γ _Δ -> e ∘ _Γ -> e ==> r
(↓) = flip getSeq


-- Effectful sequents

runSeqT :: SeqT e r _Γ m _Δ -> (_Δ • m r -> e ∘ _Γ -> e ==> m r)
runSeqT = coerce

newtype SeqT e r _Γ m _Δ = SeqT { getSeqT :: Seq e (m r) _Γ _Δ }
  deriving (Applicative, Functor, Monad)

instance MonadTrans (SeqT r s _Γ) where
  lift m = SeqT (seq (\ k _ -> C (const (m >>= (k •)))))


-- Core rules

instance Core Seq where
  f >>> g = arr (\ _Γ -> (f Cat.>>> (id ||| lmap (>--< _Γ) g), _Γ)) Cat.>>> app

  init = dimap exl inr id


-- Structural rules

deriving via Contextually Seq instance Weaken   Seq
deriving via Contextually Seq instance Contract Seq
deriving via Contextually Seq instance Exchange Seq


-- Contextual rules

instance Contextual Seq where
  sequent = seq
  appSequent = runSeq


-- Control

instance Environment Seq where
  environment = seq (\ _Δ _Γ -> review _CK (inrL _Δ))

  withEnv r s = seq (\ _Δ _Γ -> env (\ e -> _Δ |> view _CK (_Δ ↓ s ↑ lmap (const e) _Γ) ↓ r ↑ _Γ))

instance Calculus.Control Seq where
  reset s = seqFn (\ _Δ _Γ -> _Δ . runSeqFn s id _Γ)
  shift s = seq (\ _Δ _Γ -> inlL _Δ |> idK ↓ s ↑ pure (inrL _Δ) <| _Γ)


-- Assertion

instance NotUntrueIntro Seq where
  notUntrueL a = popL (val (\ (NotUntrue r) -> liftR r >>> a))
  notUntrueR s = lowerR (liftR . pure . NotUntrue) (wkR' s)

instance TrueIntro Seq where
  trueL = mapL (fmap trueA)
  trueR = mapR (lmap true)


-- Negation

instance NotIntro Seq where
  notL = notLK . kL
  notR = notRK . kR

instance NegateIntro Seq where
  negateL = negateLK . kL
  negateR a = popR (\ k -> env (\ e -> liftR (pure (negate e k)))) >>> wkR a


-- Additive

instance TopIntro Seq where
  topR = pure (inr Top)

instance ZeroIntro Seq where
  zeroL = liftL (K absurdP)

instance WithIntro Seq where
  withL1 p = popL (pushL p . exlF)
  withL2 p = popL (pushL p . exrF)
  withR = mapR2 (lmap (lmap . inlr))

instance SumIntro Seq where
  sumL a b = popL (\ s -> env ((pushL a <∘∘> pushL b) s <==))
  sumR1 = mapR (lmap inl)
  sumR2 = mapR (lmap inr)


-- Multiplicative

instance BottomIntro Seq where
  botL = liftL (K absurdN)
  botR = wkR

instance OneIntro Seq where
  oneL = wkL
  oneR = liftR (V One)

instance ParIntro Seq where
  parL a b = popL (\ s -> env ((pushL a <∘∘> pushL b) s <==))
  parR = fmap ((>>= inr . inl) <--> inr . inr)

instance TensorIntro Seq where
  tensorL p = popL (pushL2 p . exlF <*> exrF)
  tensorR = mapR2 (lmap (lmap . inlr))


-- Logical biconditional/exclusive disjunction

instance IffIntro Seq where
  iffL1 s1 s2 = mapL (fmap getIff) (withL1 (downR s1 ->⊢ s2))

  iffL2 s1 s2 = mapL (fmap getIff) (withL2 (downR s1 ->⊢ s2))

  iffR s1 s2 = mapR (lmap Iff) (funR (downL s1) ⊢& funR (downL s2))

instance XOrIntro Seq where
  xorL s1 s2 = mapL (fmap getXOr) (subL (upR s1) ⊕⊢ subL (upR s2))

  xorR1 s1 s2 = mapR (lmap XOr) (sumR1 (s1 ⊢>- upL s2))

  xorR2 s1 s2 = mapR (lmap XOr) (sumR2 (s1 ⊢>- upL s2))


-- Implication

instance FunctionIntro Seq where
  funL a b = popL (val (\ f -> a >>> liftLR (runFunExp f) >>> wkL' b))
  funR = lowerLR (liftR . pure . funExp) . wkR'

instance SubtractionIntro Seq where
  subL f = popL (val (\ s -> liftR (subA s) >>> f >>> liftL (subK s)))
  subR a b = wkR' a >>> popL (popR . fmap (liftR . pure) . (:-<)) >>> wkL' (wkR b)


-- Quantification

instance UniversalIntro Seq where
  forAllL p = mapL (fmap (notNegate . runForAll)) p
  forAllR p = seq (\ _Δ _Γ -> cont (\ _K -> pure (inrL _Δ • ForAll (_K (\ k -> inlL _Δ |> k ↓ p ↑ _Γ)))))

instance ExistentialIntro Seq where
  existsL p = popL (val (seqExp . dnE . runExists (exp . getSeq . pushL p . pure)))
  existsR p = mapR (lmap (Exists . K . flip (•))) p


-- Recursion

instance NuIntro Seq where
  nuL = mapL (fmap runNu)
  nuR s = wkR' s >>> existsL (mapL (fmap nu) init)

instance MuIntro Seq where
  muL f k = wkL (downR f) >>> exL (mapL (fmap getMu) (funL init (wkL' k)))
  muR = mapR (lmap mu)


-- Polarity shifts

instance UpIntro Seq where
  upL   = mapL (fmap getUp)
  upR   = mapR (lmap Up)

instance DownIntro Seq where
  downL = mapL (fmap getDown)
  downR = mapR (lmap Down)
