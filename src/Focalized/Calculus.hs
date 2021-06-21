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
  -- * Polarity
, N(..)
, P(..)
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
) where

import Control.Applicative (liftA2)
import Control.Exception (Exception, catch, throw)
import Control.Monad (ap, join)
import Data.Bifoldable
import Data.Bifunctor (Bifunctor(..))
import Data.Bitraversable
import Data.Functor.Identity
import Data.Profunctor
import Data.Traversable (foldMapDefault)
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


-- Polarity

class (Functor f, Functor u) => Adjunction f u | f -> u, u -> f where
  {-# MINIMAL (unit | leftAdjunct), (counit | rightAdjunct) #-}
  unit :: a -> u (f a)
  unit = leftAdjunct id
  counit :: f (u a) -> a
  counit = rightAdjunct id

  leftAdjunct :: (f a -> b) -> (a -> u b)
  leftAdjunct f = fmap f . unit
  rightAdjunct :: (a -> u b) -> (f a -> b)
  rightAdjunct f = counit . fmap f


newtype N a = N { getN :: a }
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)
  deriving (Applicative, Monad) via Identity

instance Adjunction N P where
  unit   =    P .    N
  counit = getP . getN
  leftAdjunct  f =    P . f .    N
  rightAdjunct f = getP . f . getN


newtype P a = P { getP :: a }
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)
  deriving (Applicative, Monad) via Identity

instance Adjunction P N where
  unit   =    N .    P
  counit = getN . getP
  leftAdjunct  f =    N . f .    P
  rightAdjunct f = getN . f . getP


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


newtype a & b = With (forall r . (a -> b -> r) -> r)
  deriving (Functor)

infixr 6 &

instance Foldable ((&) a) where
  foldMap = foldMapDefault

instance Traversable ((&) a) where
  traverse f (With run) = run $ \ a b -> let mk b = With (\ f -> f a b) in mk <$> f b

instance Bifoldable (&) where
  bifoldMap = bifoldMapDefault

instance Bifunctor (&) where
  bimap = bimapDefault

instance Bitraversable (&) where
  bitraverse f g w = inlr <$> f (exl w) <*> g (exr w)

instance Conj (&) where
  inlr a b = With $ \ f -> f a b
  exl (With run) = run const
  exr (With run) = run (const id)


data a ⊕ b
  = InL !a
  | InR !b
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

infixr 6 ⊕

instance Bifoldable (⊕) where
  bifoldMap = bifoldMapDefault

instance Bifunctor (⊕) where
  bimap = bimapDefault

instance Bitraversable (⊕) where
  bitraverse f g = \case
    InL a -> InL <$> f a
    InR b -> InR <$> g b

instance Disj (⊕) where
  inl = InL
  inr = InR
  exlr ifl ifr = \case
    InL l -> ifl l
    InR r -> ifr r


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
  sumLWith p = wkL p >>> exL (sumL (exL (withL1 (notL init))) (exL (withL2 (notL init))))
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

  zapSum :: p i (o |> N (Not a & Not b)) -> p (P (a ⊕ b) <| i) o
  zapSum p = sumL (wkL p >>> withL1 (notL init)) (wkL p >>> withL2 (notL init))

  zapWith :: p i (o |> P (Negate a ⊕ Negate b)) -> p (N (a & b) <| i) o
  zapWith p = wkL p >>> sumL (negateL (withL1 init)) (negateL (withL2 init))

instance Additive (Seq Δ) where
  zeroL = popL absurdP

  topR = pure (pure (N Top))

  sumL a b = popL (exlrP (pushL a) (pushL b))
  sumR1 = fmap (fmap inlP)
  sumR2 = fmap (fmap inrP)

  withL1 p = popL (pushL p . exlP)
  withL2 p = popL (pushL p . exrP)
  (&) = liftA2 (liftA2 inlrP)


-- Multiplicative

data Bot

absurdN :: N Bot -> a
absurdN = \case


data One = One
  deriving (Eq, Ord, Show)


newtype a ⅋ b = Par (forall r . (a -> r) -> (b -> r) -> r)
  deriving (Functor)

infixr 7 ⅋

instance Foldable ((⅋) a) where
  foldMap = foldMapDefault

instance Traversable ((⅋) a) where
  traverse f (Par run) = run (pure . inl) (fmap inr . f)

instance Bifoldable (⅋) where
  bifoldMap = bifoldMapDefault

instance Bifunctor (⅋) where
  bimap = bimapDefault

instance Bitraversable (⅋) where
  bitraverse f g (Par run) = run (fmap inl . f) (fmap inr . g)

instance Disj (⅋) where
  inl l = Par $ \ ifl _ -> ifl l
  inr r = Par $ \ _ ifr -> ifr r
  exlr ifl ifr (Par run) = run ifl ifr


data a ⊗ b = !a :⊗ !b
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

infixr 7 ⊗

instance Bifoldable (⊗) where
  bifoldMap = bifoldMapDefault

instance Bifunctor (⊗) where
  bimap = bimapDefault

instance Bitraversable (⊗) where
  bitraverse f g (a :⊗ b) = (:⊗) <$> f a <*> g b

instance Conj (⊗) where
  inlr = (:⊗)
  exl (l :⊗ _) = l
  exr (_ :⊗ r) = r


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

  zapTensor :: p i (o |> N (Not a ⅋ Not b)) -> p (P (a ⊗ b) <| i) o
  zapTensor p = tensorL (wkL (wkL p) >>> parL (notL init) (notL (wkL init)))

  zapPar :: p i (o |> P (Negate a ⊗ Negate b)) -> p (N (a ⅋ b) <| i) o
  zapPar p = wkL p >>> tensorL (popL2 (parL `on0` pushL (negateL init) `on1` pushL (negateL init)))


instance Multiplicative (Seq Δ) where
  botL = popL absurdN
  botR = fmap Left

  oneL = wkL
  oneR = pure (pure (P One))

  parL a b = popL (exlrP (pushL a) (pushL b))
  parR ab = either (>>= (pure . inlP)) (pure . inrP) <$> ab

  tensorL p = popL (pushL2 p . exlP <*> exrP)
  (⊗) = liftA2 (liftA2 inlrP)


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

newtype ForAll f = ForAll { forAll :: forall x . f x }

data Exists f = forall x . Exists (f x)


class (Core p, Structural p, Negative p) => Quantifying p where
  forAllL :: p (f x <| i) o -> p (ForAll f <| i) o
  forAllR :: (forall x . p i (o |> f x)) -> p i (o |> ForAll f)

  existsL :: (forall x . p (f x <| i) o) -> p (Exists f <| i) o
  existsR :: p i (o |> f x) -> p i (o |> Exists f)


-- Utilities

on0 :: (a -> b -> c) -> (a' -> a) -> (a' -> b -> c)
on0 = (.)

on1 :: (a -> b -> c) -> (b' -> b) -> (a -> b' -> c)
on1 = fmap flip . (.) . flip

infixl 4 `on0`, `on1`


cont :: ((Seq Δ i o -> Seq Δ Γ Δ) -> a) -> Seq Δ i (o |> a)
cont f = Seq $ \ k -> k . Right . f . flip dimap (k . Left) . const


class Conj c where
  inlr :: a -> b -> a `c` b
  exl :: (a `c` b) -> a
  exr :: (a `c` b) -> b

instance Conj (,) where
  inlr = (,)
  exl = fst
  exr = snd

inlrP :: (Conj c, Applicative p) => p a -> p b -> p (a `c` b)
inlrP = liftA2 inlr

exlP :: (Conj c, Functor p) => p (a `c` b) -> p a
exlP = fmap exl

exrP :: (Conj c, Functor p) => p (a `c` b) -> p b
exrP = fmap exr


class Disj d where
  inl :: a -> a `d` b
  inr :: b -> a `d` b
  exlr :: (a -> r) -> (b -> r) -> ((a `d` b) -> r)

instance Disj Either where
  inl = Left
  inr = Right
  exlr = either

inlP :: (Disj d, Functor p) => p a -> p (a `d` b)
inlP = fmap inl

inrP :: (Disj d, Functor p) => p b -> p (a `d` b)
inrP = fmap inr

exlrP :: (Adjunction p p', Disj d) => (p a -> r) -> (p b -> r) -> (p (a `d` b) -> r)
exlrP f g = rightAdjunct (exlr (leftAdjunct f) (leftAdjunct g))
