-- | Pretty-printing.
module Sequoia.Print.Printer
( -- * Printers
  Printer(..)
  -- * Construction
, printer
, withSubject
, contrapure
  -- * Elimination
, print
, appPrint
  -- * Computation
, (<#>)
, (<&>)
, (<&)
, liftP2
, liftC2
  -- * Combinators
, pairWith
, tuple
  -- * Documents
, Doc(..)
  -- * Exponentials
, type (-->)(..)
, appF
, (#)
, xfmap
, xap
, xbind
  -- * Coexponentials
, type (>--)(..)
, (>--)
, coK
, coconst
) where

import Control.Monad (ap)
import Data.Functor.Contravariant
import Data.Monoid (Endo(..))
import Data.Profunctor
import Prelude hiding (print)
import Sequoia.Disjunction
import Sequoia.Print.Class

-- Printers

newtype Printer a = Printer { runPrint :: forall r . (Doc -> r) -> (a -> r) }

instance Semigroup (Printer a) where
  p1 <> p2 = printer (\ k a -> appPrint p1 a (\ a' -> appPrint p2 a (lmap (mappend a') k)))

instance Monoid (Printer a) where
  mempty = printer (const . ($ mempty))

instance Print (Printer a) where
  char c = printer (const . ($ char c))
  string s = printer (const . ($ string s))

instance Contravariant Printer where
  contramap f (Printer r) = Printer (lmap f . r)


-- Construction

printer :: (forall r . (Doc -> r) -> (a -> r)) -> Printer a
printer = Printer

withSubject :: (a -> Printer a) -> Printer a
withSubject f = printer (\ k a -> appPrint (f a) a k)

contrapure :: (b -> a) -> Printer (a >-- b)
contrapure f = printer (\ k (pa :>-- b) -> appPrint pa (f b) k)


-- Elimination

print :: Printer a -> a -> Doc
print p = runPrint p id

appPrint :: Printer a -> a -> (Doc -> r) -> r
appPrint p a k = runPrint p k a


-- Computation

(<#>) :: (b >-- a) -> Printer a -> Printer b
f <#> a = printer (\ k b -> appPrint a (coconst f) (\ a -> appPrint (coK f) b (k . mappend a)))

infixl 4 <#>

(<&>) :: Printer (a >-- b) -> Printer a -> Printer b
pf <&> pa = printer (\ k b -> appPrint pf (pa >-- b) k)

infixl 4 <&>

(<&) :: Printer a -> Printer b -> Printer a
a <& b = contramap coconst a <&> b

infixl 4 <&

liftP2 :: ((b >-- c) -> a) -> Printer a -> Printer b -> Printer c
liftP2 f a b = contramap f a <&> b

liftC2 :: (c -> Either a b) -> Printer a -> Printer b -> Printer c
liftC2 f pa pb = printer (\ k c -> either (runPrint pa k) (runPrint pb k) (f c))


-- Combinators

pairWith :: (Doc -> Doc -> Doc) -> Printer (a >-- b >-- (a, b))
pairWith f = printer (\ k (pa :>-- pb :>-- (a, b)) -> appPrint pa a (appPrint pb b . (k .) . f))

tuple :: Printer a -> Printer b -> Printer (a, b)
tuple a b = pairWith combine <&> a <&> b
  where
  combine da db = parens (da <> comma <+> db)


-- Documents

newtype Doc = Doc { getDoc :: ShowS }
  deriving (Monoid, Semigroup) via Endo String

instance Print Doc where
  char c = Doc (c:)
  string s = Doc (s<>)


-- Exponentials

newtype a --> b = F { runF :: forall r . (b -> r) -> (a -> r) }

instance Profunctor (-->) where
  dimap f g (F r) = F (dimap (lmap g) (lmap f) r)

instance Choice (-->) where
  left'  (F r) = F (\ k -> r (inlL k) <--> inrL k)
  right' (F r) = F (\ k -> inlL k <--> r (inrL k))

instance Cochoice (-->) where
  unleft  (F f) = F (\ k -> inlL (let f' = f (k <--> inrL f') in f'))
  unright (F f) = F (\ k -> inrL (let f' = f (inlL f' <--> k) in f'))

instance Strong (-->) where
  first'  (F r) = F (\ k (a, c) -> r (lmap (,c) k) a)
  second' (F r) = F (\ k (c, a) -> r (lmap (c,) k) a)

instance Functor ((-->) a) where
  fmap = rmap

instance Applicative ((-->) a) where
  pure a = F (const . ($ a))
  (<*>) = ap

instance Monad ((-->) a) where
  F r >>= f = F (\ k i -> r (\ a -> runF (f a) k i) i)


appF :: (a --> b) -> a -> (b -> r) -> r
appF f a b = runF f b a

(#) :: (a --> b) -> (a -> b)
f # a = runF f id a

infixl 9 #


xfmap :: Functor f => (a --> b) -> (f a --> f b)
xfmap f = F (\ k fa -> k ((f #) <$> fa))

xap :: Applicative f => f (a --> b) -> (f a --> f b)
xap f = F (\ k fa -> k ((#) <$> f <*> fa))

xbind :: Monad m => (a --> m b) -> (m a --> m b)
xbind f = F (\ k ma -> k (ma >>= (f #)))


-- Coexponentials

data a >-- b = Printer a :>-- b
  deriving (Functor)

infixr 0 >--, :>--

instance Profunctor (>--) where
  dimap f g (a :>-- b) = contramap f a >-- g b


(>--) :: Printer a -> b -> a >-- b
(>--) = (:>--)


coK :: (a >-- b) -> Printer a
coK (k :>-- _) = k

coconst :: (a >-- b) -> b
coconst (_ :>-- a) = a
