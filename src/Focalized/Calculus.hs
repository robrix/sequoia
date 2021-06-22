{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances #-}
module Focalized.Calculus
( -- * Sequents
  runSeq
, runSeqIO
, Seq(..)
  -- * Contexts
, type (<|)
, type (|>)
, Γ(..)
, Δ
  -- * Core rules
, Core(..)
, Structural(..)
  -- * Negating
, Not(..)
, runNot
, not'
, Negate(..)
, runNegate
, negate'
, Negative(..)
  -- * Additive
, Top(..)
, Zero
, type (&)(..)
, type (⊕)(..)
, Additive(..)
  -- * Multiplicative
, Bot
, One(..)
, type (⅋)(..)
, type (⊗)(..)
, (:⊗)(..)
, type (.⊗)
, Multiplicative(..)
  -- * Implicative
, type (-->)(..)
, appFun
, fun
, type (--<)(..)
, sub
, Implicative(..)
  -- * Quantifying
, ForAll(..)
, Exists(..)
, Quantifying(..)
  -- * Recursive
, Mu(..)
, mu
, getMu
, Nu(..)
, nu
, getNu
, Recursive(..)
  -- * Polarity
, N(..)
, P(..)
, Up(..)
, Down(..)
, Shifting(..)
  -- * Utilities
, I(..)
, J(..)
, (:->)(..)
, type (.->)
, Conj(..)
, Disj(..)
, foldMapDisj
, bifoldMapDisj
, fmapDisj
, bimapDisj
, traverseDisj
, bitraverseDisj
) where

import Control.Applicative (liftA2)
import Control.Exception (Exception, catch, throw)
import Control.Monad (ap, join)
import Data.Bifoldable
import Data.Bifunctor (Bifunctor(..))
import Data.Bitraversable
import Data.Distributive
import Data.Functor.Adjunction
import Data.Functor.Identity
import Data.Functor.Rep
import Data.Profunctor hiding ((:->))
import Prelude hiding (init)

-- Sequents

runSeq :: (o -> r) -> i -> Seq r i o -> r
runSeq k c (Seq run) = run k c

runSeqIO :: (o -> IO ()) -> i -> Seq Δ i o -> IO ()
runSeqIO k i (Seq run) = absurdΔ (run (throw . Escape . k) i) `catch` getEscape

newtype Escape = Escape { getEscape :: IO () }

instance Show Escape where show _ = "Escape"
instance Exception Escape


newtype Seq r i o = Seq ((o -> r) -> (i -> r))
  deriving (Functor)

instance Applicative (Seq r i) where
  pure a = Seq $ \ k _ -> k a
  (<*>) = ap

instance Monad (Seq r i) where
  Seq a >>= f = Seq $ \ k c -> a (runSeq k c . f) c

instance Profunctor (Seq r) where
  dimap f g (Seq run) = Seq (\ k -> run (k . g) . f)


-- Contexts

type (<|) = (,)
infixr 4 <|

type (|>) = Either
infixl 4 |>

split :: (o |> a -> r) -> (o -> r, a -> r)
split f = (f . Left, f . Right)


data Γ = Γ
  deriving (Eq, Ord, Show)


data Δ

absurdΔ :: Δ -> a
absurdΔ = \case


-- Core rules

class Core p where
  (>>>) :: p i (o |> a) -> p (a <| i) o -> p i o

  init :: p (a <| i) (o |> a)

infixr 1 >>>

instance Core (Seq Δ) where
  f >>> g = f >>= either pure (pushL g)

  init = popL (pure . pure)


class Structural p where
  -- | Pop something off the input context which can later be pushed. Used with 'pushL', this provides a generalized context restructuring facility.
  --
  -- @
  -- popL . pushL = id
  -- @
  -- @
  -- pushL . popL = id
  -- @
  popL :: (a -> p i o) -> p (a <| i) o

  poppedL :: (p i o -> p i' o') -> (p (a <| i) o -> p (a <| i') o')
  poppedL f p = popL (f . pushL p)

  -- | Push something onto the input context which was previously popped off it. Used with 'popL', this provides a generalized context restructuring facility. It i undefined what will happen if you push something which was not previously popped.
  --
  -- @
  -- popL . pushL = id
  -- @
  -- @
  -- pushL . popL = id
  -- @
  pushL :: p (a <| i) o -> a -> p i o

  popL2 :: (a -> b -> p i o) -> p (a <| b <| i) o
  popL2 f = popL (popL . f)

  pushL2 :: p (a <| b <| i) o -> a -> b -> p i o
  pushL2 p = pushL . pushL p

  mapL :: (a' -> a) -> p (a <| i) o -> p (a' <| i) o
  mapL f p = popL (pushL p . f)


  -- | Pop something off the output context which can later be pushed. Used with 'pushR', this provides a generalized context restructuring facility.
  --
  -- @
  -- popR . pushR = id
  -- @
  -- @
  -- pushR . popR = id
  -- @
  popR :: ((a -> Δ) -> p i o) -> p i (o |> a)

  poppedR :: (p i o -> p i' o') -> (p i (o |> a) -> p i' (o' |> a))
  poppedR f p = popR (f . pushR p)

  -- | Push something onto the output context which was previously popped off it. Used with 'popR', this provides a generalized context restructuring facility. It i undefined what will happen if you push something which was not previously popped.
  --
  -- @
  -- popR . pushR = id
  -- @
  -- @
  -- pushR . popR = id
  -- @
  pushR :: p i (o |> a) -> ((a -> Δ) -> p i o)

  popR2 :: ((a -> Δ) -> (b -> Δ) -> p i o) -> p i (o |> b |> a)
  popR2 f = popR (popR . f)

  pushR2 :: p i (o |> b |> a) -> (a -> Δ) -> (b -> Δ) -> p i o
  pushR2 p = pushR . pushR p

  mapR :: (a -> a') -> p i (o |> a) -> p i (o |> a')
  mapR f p = popR (pushR p . (. f))


  wkL :: p i o -> p (a <| i) o
  wkL = popL . const
  wkR :: p i o -> p i (o |> a)
  wkR = popR . const
  cnL :: p (a <| a <| i) o -> p (a <| i) o
  cnL = popL . join . pushL2
  cnR :: p i (o |> a |> a) -> p i (o |> a)
  cnR = popR . join . pushR2
  exL :: p (a <| b <| c) o -> p (b <| a <| c) o
  exL = popL2 . flip . pushL2
  exR :: p i (o |> a |> b) -> p i (o |> b |> a)
  exR = popR2 . flip . pushR2

instance Structural (Seq Δ) where
  popL f = Seq $ \ k -> uncurry (flip (runSeq k) . f)
  pushL (Seq run) a = Seq $ \ k -> run k . (a,)

  popR f = Seq $ \ k c -> let (k', ka) = split k in runSeq k' c (f ka)
  pushR (Seq run) a = Seq $ \ k -> run (either k a)


-- Negating

newtype Not    a = Not    { getNot    :: Seq Δ (P a <| Γ) Δ }

runNot :: N (Not a) -> Seq Δ (P a <| Γ) Δ
runNot = getNot . getN

not' :: Seq Δ (P a <| Γ) Δ -> N (Not a)
not' = N . Not


newtype Negate a = Negate { getNegate :: Seq Δ (N a <| Γ) Δ }

runNegate :: P (Negate a) -> Seq Δ (N a <| Γ) Δ
runNegate = getNegate . getP

negate' :: Seq Δ (N a <| Γ) Δ -> P (Negate a)
negate' = P . Negate


class (Core p, Structural p) => Negative p where
  notL :: p i (o |> P a) -> p (N (Not a) <| i) o
  notL' :: p (N (Not a) <| i) o -> p i (o |> P a)
  notL' p = notR init >>> wkR p
  notR :: p (P a <| i) o -> p i (o |> N (Not a))
  notR' :: p i (o |> N (Not a)) -> p (P a <| i) o
  notR' p = wkL p >>> notL init

  negateL :: p i (o |> N a) -> p (P (Negate a) <| i) o
  negateL' :: p (P (Negate a) <| i) o -> p i (o |> N a)
  negateL' p = negateR init >>> wkR p
  negateR :: p (N a <| i) o -> p i (o |> P (Negate a))
  negateR' :: p i (o |> P (Negate a)) -> p (N a <| i) o
  negateR' p = wkL p >>> negateL init

instance Negative (Seq Δ) where
  negateL p = popL (\ negateA -> p >>> dimap (Γ <$) absurdΔ (runNegate negateA))
  negateR p = cont (\ abstract -> negate' (poppedL abstract p))

  notL p = popL (\ notA -> p >>> dimap (Γ <$) absurdΔ (runNot notA))
  notR p = cont (\ abstract -> not' (poppedL abstract p))


-- Additive

data Top = Top
  deriving (Eq, Ord, Show)


data Zero

absurdP :: P Zero -> a
absurdP = \case


newtype a & b = With { getWith :: (I :& I) a b }
  deriving (Conj I I, Bifoldable, Bifunctor, Foldable, Functor, Traversable)

infixr 6 &, :&

instance Bitraversable (&) where
  bitraverse f g = fmap With . bitraverse f g . getWith


newtype (f :& g) a b = With1 (forall r . (f a -> g b -> r) -> r)
  deriving (Functor)

instance Foldable g => Foldable ((f :& g) a) where
  foldMap f = foldMap f . exr

instance Traversable g => Traversable ((f :& g) a) where
  traverse f r = inlr (exl r) <$> traverse f (exr r)

instance (Foldable f, Foldable g) => Bifoldable (f :& g) where
  bifoldMap f g = (foldMap f &&& foldMap g) (<>)

instance (Functor f, Functor g) => Bifunctor (f :& g) where
  bimap f g = fmap f *** fmap g

instance (Traversable f, Traversable g) => Bitraversable (f :& g) where
  bitraverse f g w = inlr <$> traverse f (exl w) <*> traverse g (exr w)

instance Conj f g (f :& g) where
  inlr a b = With1 $ \ f -> f a b
  exl (With1 run) = run const
  exr (With1 run) = run (const id)


newtype a ⊕ b = Sum { getSum :: (I :⊕ I) a b }
  deriving (Disj I I, Bifoldable, Bifunctor, Eq, Foldable, Functor, Ord, Show, Traversable)

infixr 6 ⊕, :⊕

instance Bitraversable (⊕) where
  bitraverse f g = fmap Sum . bitraverse f g . getSum


data (f :⊕ g) a b
  = InL1 !(f a)
  | InR1 !(g b)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

instance (Foldable f, Foldable g) => Bifoldable (f :⊕ g) where
  bifoldMap = bifoldMapDisj

instance (Functor f, Functor g) => Bifunctor (f :⊕ g) where
  bimap = bimapDisj

instance (Traversable f, Traversable g) => Bitraversable (f :⊕ g) where
  bitraverse = bitraverseDisj

instance Disj f g (f :⊕ g) where
  inl = InL1
  inr = InR1
  exlr ifl ifr = \case
    InL1 l -> ifl l
    InR1 r -> ifr r


class (Core p, Structural p, Negative p) => Additive p where
  zeroL :: p (P Zero <| i) o

  topR :: p i (o |> N Top)

  sumL :: p (P a <| i) o -> p (P b <| i) o -> p (P (a ⊕ b) <| i) o
  sumL p1 p2 = sumLWith (notR p1 & notR p2)
  sumL1' :: p (P (a ⊕ b) <| i) o -> p (P a <| i) o
  sumL1' p = sumR1 init >>> exL (wkL p)
  sumL2' :: p (P (a ⊕ b) <| i) o -> p (P b <| i) o
  sumL2' p = sumR2 init >>> exL (wkL p)
  sumLWith :: p i (o |> N (Not a & Not b)) -> p (P (a ⊕ b) <| i) o
  sumLWith p = sumL (wkL p >>> withL1 (notL init)) (wkL p >>> withL2 (notL init))
  sumR1 :: p i (o |> P a) -> p i (o |> P (a ⊕ b))
  sumR2 :: p i (o |> P b) -> p i (o |> P (a ⊕ b))

  withL1 :: p (N a <| i) o -> p (N (a & b) <| i) o
  withL1 = withLSum . sumR1 . negateR
  withL2 :: p (N b <| i) o -> p (N (a & b) <| i) o
  withL2 = withLSum . sumR2 . negateR
  withLSum :: p i (o |> P (Negate a ⊕ Negate b)) -> p (N (a & b) <| i) o
  withLSum p = wkL p >>> sumL (negateL (withL1 init)) (negateL (withL2 init))
  (&) :: p i (o |> N a) -> p i (o |> N b) -> p i (o |> N (a & b))
  withR1' :: p i (o |> N (a & b)) -> p i (o |> N a)
  withR1' t = exR (wkR t) >>> withL1 init
  withR2' :: p i (o |> N (a & b)) -> p i (o |> N b)
  withR2' t = exR (wkR t) >>> withL2 init


instance Additive (Seq Δ) where
  zeroL = popL absurdP

  topR = pure (pure (N Top))

  sumL a b = popL (exlrP (pushL a . fmap getI) (pushL b . fmap getI))
  sumR1 = mapR (inlP . fmap I)
  sumR2 = mapR (inrP . fmap I)

  withL1 p = popL (pushL p . fmap getI . exlP)
  withL2 p = popL (pushL p . fmap getI . exrP)
  (&) = liftA2 (liftA2 (\ a b -> inlrP (I <$> a) (I <$> b)))


-- Multiplicative

data Bot

absurdN :: N Bot -> a
absurdN = \case


data One = One
  deriving (Eq, Ord, Show)


newtype a ⅋ b = Par { getPar :: (I :⅋ I) a b }
  deriving (Bifunctor, Bifoldable, Disj I I, Foldable, Functor, Traversable)

infixr 7 ⅋, :⅋

instance Bitraversable (⅋) where
  bitraverse f g = fmap Par . bitraverse f g . getPar


newtype (f :⅋ g) a b = Par1 (forall r . (f a -> r) -> (g b -> r) -> r)
  deriving (Functor)

instance Foldable g => Foldable ((f :⅋ g) a) where
  foldMap = foldMapDisj

instance Traversable g => Traversable ((f :⅋ g) a) where
  traverse = traverseDisj

instance (Foldable f, Foldable g) => Bifoldable (f :⅋ g) where
  bifoldMap = bifoldMapDisj

instance (Functor f, Functor g) => Bifunctor (f :⅋ g) where
  bimap = bimapDisj

instance (Traversable f, Traversable g) => Bitraversable (f :⅋ g) where
  bitraverse = bitraverseDisj

instance Disj f g (f :⅋ g) where
  inl l = Par1 $ \ ifl _ -> ifl l
  inr r = Par1 $ \ _ ifr -> ifr r
  exlr ifl ifr (Par1 run) = run ifl ifr


newtype a ⊗ b = Tensor { getTensor :: (I :⊗ I) a b }
  deriving (Bifoldable, Bifunctor, Conj I I, Eq, Foldable, Functor, Ord, Show, Traversable)

infixr 7 ⊗, :⊗, .⊗

instance Bitraversable (⊗) where
  bitraverse f g = fmap Tensor . bitraverse f g . getTensor


data (f :⊗ g) a b = !(f a) :⊗ !(g b)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

instance (Foldable f, Foldable g) => Bifoldable (f :⊗ g) where
  bifoldMap f g = (foldMap f &&& foldMap g) (<>)

instance (Functor f, Functor g) => Bifunctor (f :⊗ g) where
  bimap f g = fmap f *** fmap g

instance (Traversable f, Traversable g) => Bitraversable (f :⊗ g) where
  bitraverse f g (a :⊗ b) = (:⊗) <$> traverse f a <*> traverse g b

instance Conj f g (f :⊗ g) where
  inlr = (:⊗)
  exl (l :⊗ _) = l
  exr (_ :⊗ r) = r


type (f .⊗ g) = J (f :⊗ g)


class (Core p, Structural p, Negative p) => Multiplicative p where
  botL :: p (N Bot <| i) o
  botR :: p i o -> p i (o |> N Bot)
  botR' :: p i (o |> N Bot) -> p i o
  botR' = (>>> botL)

  oneL :: p i o -> p (P One <| i) o
  oneL' :: p (P One <| i) o -> p i o
  oneL' = (oneR >>>)
  oneR :: p i (o |> P One)

  parL :: p (N a <| i) o -> p (N b <| i) o -> p (N (a ⅋ b) <| i) o
  parL p1 p2 = parLTensor (negateR p1 ⊗ negateR p2)
  parLTensor :: p i (o |> P (Negate a ⊗ Negate b)) -> p (N (a ⅋ b) <| i) o
  parLTensor p = wkL p >>> tensorL (negateL (negateL (parL (wkR init) init)))
  parR :: p i (o |> N a |> N b) -> p i (o |> N (a ⅋ b))
  parR' :: p i (o |> N (a ⅋ b)) -> p i (o |> N a |> N b)
  parR' p = exR (wkR (exR (wkR p))) >>> parL (wkR init) init

  tensorL :: p (P a <| P b <| i) o -> p (P (a ⊗ b) <| i) o
  tensorL = tensorLPar . parR . notR . notR
  tensorLPar :: p i (o |> N (Not a ⅋ Not b)) -> p (P (a ⊗ b) <| i) o
  tensorLPar p = wkL p >>> parL (notL (tensorL init)) (notL (tensorL (wkL init)))
  tensorL' :: p (P (a ⊗ b) <| i) o -> p (P a <| P b <| i) o
  tensorL' p = init ⊗ wkL init >>> popL (wkL . wkL . pushL p)
  (⊗) :: p i (o |> P a) -> p i (o |> P b) -> p i (o |> P (a ⊗ b))


instance Multiplicative (Seq Δ) where
  botL = popL absurdN
  botR = fmap Left

  oneL = wkL
  oneR = pure (pure (P One))

  parL a b = popL (exlrP (pushL a . fmap getI) (pushL b . fmap getI))
  parR ab = either (>>= (pure . inlP . fmap I)) (pure . inrP . fmap I) <$> ab

  tensorL p = popL (pushL2 p . fmap getI . exlP <*> fmap getI . exrP)
  (⊗) = liftA2 (liftA2 (\ a b -> inlrP (I <$> a) (I <$> b)))


-- Implicative

newtype a --> b = Fun { getFun :: Seq Δ (P (Negate b) <| Γ) (Δ |> N (Not a)) }

infixr 5 -->

appFun :: N (a --> b) -> Seq Δ (P (Negate b) <| Γ) (Δ |> N (Not a))
appFun = getFun . getN

appFun' :: N (a --> b) -> Seq Δ (P (Negate b) <| i) (o |> N (Not a))
appFun' = dimap (Γ <$) (first absurdΔ) . appFun

fun :: Seq Δ (P (Negate b) <| Γ) (Δ |> N (Not a)) -> N (a --> b)
fun = N . Fun


data a --< b = Sub { subA :: !(P a), subK :: !(P (Negate b)) }

infixr 5 --<

sub :: P a -> P (Negate b) -> P (a --< b)
sub = fmap P . Sub


class (Core p, Structural p, Negative p) => Implicative p where
  funL :: p i (o |> P a) -> p (N b <| i) o -> p (N (a --> b) <| i) o
  funL pa pb = funLSub (subR pa pb)
  funLSub :: p i (o |> P (a --< b)) -> p (N (a --> b) <| i) o
  funLSub p = wkL p >>> subL (exL (funL init init))
  funL2 :: p (N (a --> b) <| P a <| i)  (o |> N b)
  funL2 = funL init init
  funR :: p (P a <| i) (o |> N b) -> p i (o |> N (a --> b))
  funR' :: p i (o |> N (a --> b)) -> p (P a <| i) (o |> N b)
  funR' p = wkL (exR (wkR p)) >>> funL2

  subL :: p (P a <| i) (o |> N b) -> p (P (a --< b) <| i) o
  subL = subLFun . funR
  subLFun :: p i (o |> N (a --> b)) -> p (P (a --< b) <| i) o
  subLFun p = wkL p >>> exL (subL (exL (funL init init)))
  subL' :: p (P (a --< b) <| i) o -> p (P a <| i) (o |> N b)
  subL' p = subR init init >>> wkR (exL (wkL p))
  subR :: p i (o |> P a) -> p (N b <| i) o -> p i (o |> P (a --< b))

  ($$) :: p i (o |> N (a --> b)) -> p i (o |> P a) -> p i (o |> N b)
  f $$ a = exR (wkR f) >>> exR (wkR a) `funL` init


instance Implicative (Seq Δ) where
  funL a b = popL (\ f -> a >>> notR' (exR (negateL' (appFun' f))) >>> exL (wkL b))
  funR b = cont (\ abstract -> fun (poppedL (poppedR abstract) (notR (exL (negateL b)))))

  subL b = popL (\ (P s) -> pushL b (subA s) >>> pushL (negateL init) (subK s))
  subR a b = liftA2 sub <$> a <*> negateR b


-- Quantifying

newtype ForAll f = ForAll (forall x . f x)

runForAll :: N (ForAll f) -> N (f x)
runForAll (N (ForAll f)) = N f


data Exists f = forall x . Exists (f x)

exists :: P (f x) -> P (Exists f)
exists = fmap Exists

runExists :: (forall x . P (f x) -> r) -> P (Exists f) -> r
runExists f (P (Exists r)) = f (P r)


class (Core p, Structural p, Negative p, Shifting p) => Quantifying p where
  forAllL :: p (N (f x) <| i) o -> p (N (ForAll f) <| i) o
  forAllLExists :: p i (o |> P (Exists (Negate · f))) -> p (N (ForAll f) <| i) o
  forAllLExists p = wkL p >>> existsL (mapL (fmap getC) (negateL (forAllL init)))
  -- FIXME: the correct signature should be p i (o |> (forall x . N (f x))) -> p i (o |> N (ForAll f)), but we can’t write that until (at least) quick look impredicativity lands in ghc (likely 9.2)
  -- forAllR :: (forall x . p i (o |> N (f x))) -> p i (o |> N (ForAll f))
  forAllR' :: p i (o |> N (ForAll f)) -> (forall x . p i (o |> N (f x)))
  forAllR' p = exR (wkR p) >>> forAllL init

  -- FIXME: the correct signature should be p ((forall x . P (f x)) <| i) o -> p (P (Exists f) <| i) o, but we can’t write that until (at least) quick look impredicativity lands in ghc (likely 9.2)
  existsL :: (forall x . p (P (f x) <| i) o) -> p (P (Exists f) <| i) o
  existsL' :: p (P (Exists f) <| i) o -> (forall x . p (P (f x) <| i) o)
  existsL' p = existsR init >>> exL (wkL p)
  existsLForAll :: p i (o |> N (ForAll (Not · f))) -> p (P (Exists f) <| i) o
  existsLForAll p = wkL p >>> exL (existsL (exL (forAllL (mapL (fmap getC) (notL init)))))
  existsR :: p i (o |> P (f x)) -> p i (o |> P (Exists f))
  existsRForAll :: p i (o |> N (ForAll (Up · f))) -> p i (o |> P (Exists f))
  existsRForAll = existsR . upR' . mapR (fmap getC) . forAllR'


instance Quantifying (Seq Δ) where
  forAllL p = mapL runForAll p
  -- forAllR p = mapR ForAll p

  existsL p = popL (runExists (pushL p))
  existsR p = mapR exists p


-- Recursive

newtype Mu f = Mu (ForAll ((f .-> I) .-> I))

mu :: N (ForAll ((f .-> I) .-> I)) -> N (Mu f)
mu = fmap Mu

getMu :: N (Mu f) -> N (ForAll ((f .-> I) .-> I))
getMu (N (Mu f)) = N f


newtype Nu f = Nu (Exists ((I .-> f) .⊗ I))

nu :: P (Exists ((I .-> f) .⊗ I)) -> P (Nu f)
nu = fmap Nu

getNu :: P (Nu f) -> P (Exists ((I .-> f) .⊗ I))
getNu (P (Nu f)) = P f


class (Core p, Structural p) => Recursive p where
  muL :: p (N (ForAll ((f .-> I) .-> I)) <| i) o -> p (N (Mu f) <| i) o
  muR :: p i (o |> N (ForAll ((f .-> I) .-> I))) -> p i (o |> N (Mu f))

  nuL :: p (P (Exists ((I .-> f) .⊗ I)) <| i) o -> p (P (Nu f) <| i) o
  nuR :: p i (o |> P (Exists ((I .-> f) .⊗ I))) -> p i (o |> P (Nu f))


instance Recursive (Seq Δ) where
  muL = mapL getMu
  muR = mapR mu

  nuL = mapL getNu
  nuR = mapR nu


-- Polarity

newtype N a = N { getN :: a }
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)
  deriving (Applicative, Monad, Representable) via Identity

instance Distributive N where
  collect f = N . fmap (getN . f)
  distribute = N . fmap getN

instance Adjunction N P where
  unit   =    P .    N
  counit = getP . getN
  leftAdjunct  f =    P . f .    N
  rightAdjunct f = getP . f . getN


newtype P a = P { getP :: a }
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)
  deriving (Applicative, Monad, Representable) via Identity

instance Distributive P where
  collect f = P . fmap (getP . f)
  distribute = P . fmap getP

instance Adjunction P N where
  unit   =    N .    P
  counit = getN . getP
  leftAdjunct  f =    N . f .    P
  rightAdjunct f = getN . f . getP


up :: P a -> N (Up a)
up = N . Up . getP

runUp :: N (Up a) -> P a
runUp = P . getUp . getN

newtype Up   a = Up   { getUp   :: a }
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)
  deriving (Applicative, Monad, Representable) via Identity

instance Distributive Up where
  collect f = Up . fmap (getUp . f)
  distribute = Up . fmap getUp

instance Adjunction Up Down where
  unit   =    Down .    Up
  counit = getDown . getUp
  leftAdjunct  f =    Down . f .    Up
  rightAdjunct f = getDown . f . getUp


down :: N a -> P (Down a)
down = P . Down . getN

runDown :: P (Down a) -> N a
runDown = N . getDown . getP

newtype Down a = Down { getDown :: a }
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)
  deriving (Applicative, Monad, Representable) via Identity

instance Distributive Down where
  collect f = Down . fmap (getDown . f)
  distribute = Down . fmap getDown

instance Adjunction Down Up where
  unit   =    Up .    Down
  counit = getUp . getDown
  leftAdjunct  f =    Up . f .    Down
  rightAdjunct f = getUp . f . getDown


class (Core p, Structural p) => Shifting p where
  upL   :: p (P a <| i) o -> p (N (Up   a) <| i) o
  upL'   :: p (N (Up   a) <| i) o -> p (P a <| i) o
  upL' p = upR init >>> exL (wkL p)
  upR   :: p i (o |> P a) -> p i (o |> N (Up   a))
  upR'   :: p i (o |> N (Up   a)) -> p i (o |> P a)
  upR' p = exR (wkR p) >>> upL init

  downL :: p (N a <| i) o -> p (P (Down a) <| i) o
  downL'   :: p (P (Down   a) <| i) o -> p (N a <| i) o
  downL' p = downR init >>> exL (wkL p)
  downR :: p i (o |> N a) -> p i (o |> P (Down a))
  downR'   :: p i (o |> P (Down   a)) -> p i (o |> N a)
  downR' p = exR (wkR p) >>> downL init


instance Shifting (Seq Δ) where
  upL   = mapL runUp
  upR   = mapR up

  downL = mapL runDown
  downR = mapR down


-- Utilities

cont :: ((Seq r i o -> Seq r Γ Δ) -> a) -> Seq Δ i (o |> a)
cont f = Seq $ \ k -> k . Right . f . flip dimap (k . Left) . const


newtype I a = I { getI :: a }
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)


newtype J p a = J { getJ :: p a a }

instance Bifoldable p => Foldable (J p) where
  foldMap f = bifoldMap f f . getJ

instance Bifunctor p => Functor (J p) where
  fmap f = J . bimap f f . getJ

instance Bitraversable p => Traversable (J p) where
  traverse f = fmap J . bitraverse f f . getJ


newtype (f :-> g) a b = Fn (f a -> g b)

infixr 5 :->, .->

type (f .-> g) = J (f :-> g)


class Conj f g c | c -> f g where
  inlr :: f a -> g b -> a `c` b
  exl :: (a `c` b) -> f a
  exr :: (a `c` b) -> g b

instance Conj I I (,) where
  inlr (I a) (I b) = (a, b)
  exl = I . fst
  exr = I . snd

(***) :: (Conj f g r, Conj f' g' r') => (f a -> f' a') -> (g b -> g' b') -> (a `r` b) -> (a' `r'` b')
f *** g = inlr <$> f . exl <*> g . exr

(&&&) :: Conj f g r => (f a -> c) -> (g b -> d) -> (c -> d -> e) -> (a `r` b) -> e
(f &&& g) h = h <$> f . exl <*> g . exr

inlrP :: (Conj f g c, Applicative p) => p (f a) -> p (g b) -> p (a `c` b)
inlrP = liftA2 inlr

exlP :: (Conj f g c, Functor p) => p (a `c` b) -> p (f a)
exlP = fmap exl

exrP :: (Conj f g c, Functor p) => p (a `c` b) -> p (g b)
exrP = fmap exr


class Disj f g d | d -> f g where
  inl :: f a -> a `d` b
  inr :: g b -> a `d` b
  exlr :: (f a -> r) -> (g b -> r) -> ((a `d` b) -> r)

instance Disj I I Either where
  inl = Left  . getI
  inr = Right . getI
  exlr f g = either (f . I) (g . I)

inlP :: (Disj f g d, Functor p) => p (f a) -> p (a `d` b)
inlP = fmap inl

inrP :: (Disj f g d, Functor p) => p (g b) -> p (a `d` b)
inrP = fmap inr

exlrP :: (Adjunction p p', Disj f g d) => (p (f a) -> r) -> (p (g b) -> r) -> (p (a `d` b) -> r)
exlrP f g = rightAdjunct (exlr (leftAdjunct f) (leftAdjunct g))

foldMapDisj :: (Foldable g, Disj f g p, Monoid m) => (b -> m) -> (a `p` b) -> m
foldMapDisj f = exlr (const mempty) (foldMap f)

bifoldMapDisj :: (Foldable f, Foldable g, Disj f g p, Monoid m) => (a -> m) -> (b -> m) -> (a `p` b) -> m
bifoldMapDisj f g = exlr (foldMap f) (foldMap g)

fmapDisj :: (Functor g, Disj f g p) => (b -> b') -> (a `p` b) -> (a `p` b')
fmapDisj f = exlr inl (inr . fmap f)

bimapDisj :: (Functor f, Functor g, Disj f g p) => (a -> a') -> (b -> b') -> (a `p` b) -> (a' `p` b')
bimapDisj f g = exlr (inl . fmap f) (inr . fmap g)

traverseDisj :: (Traversable g, Disj f g p, Applicative m) => (b -> m b') -> (a `p` b) -> m (a `p` b')
traverseDisj f = exlr (pure . inl) (fmap inr . traverse f)

bitraverseDisj :: (Traversable f, Traversable g, Disj f g p, Applicative m) => (a -> m a') -> (b -> m b') -> (a `p` b) -> m (a' `p` b')
bitraverseDisj f g = exlr (fmap inl . traverse f) (fmap inr . traverse g)


newtype (f · g) a = C { getC :: f (g a) }
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

infixr 7 ·

instance (Applicative f, Applicative g) => Applicative (f · g) where
  pure = C . pure . pure
  f <*> a = C ((<*>) <$> getC f <*> getC a)
