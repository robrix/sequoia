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
  -- * Computation
, (<&>)
, (<&)
, (&>)
, liftP2
, liftC2
, (<:>)
, fanoutWith
  -- * Combinators
, tuple
, list
, char1
, string1
  -- * Exponentials
, Exp(..)
, appF
, (#)
, contramapExp
  -- * Coexponentials
, Coexp(..)
, (>--)
, cocurry
) where

import Control.Monad (ap)
import Data.Functor.Contravariant
import Data.List (uncons)
import Data.List.NonEmpty (nonEmpty, toList)
import Data.Profunctor
import Prelude hiding (print)
import Sequoia.Disjunction
import Sequoia.Print.Class
import Sequoia.Print.Doc

-- Printers

newtype Printer r a = Printer { runPrint :: (Doc -> r) -> (a -> r) }

instance Semigroup (Printer r a) where
  p1 <> p2 = printer (\ k a -> runPrint p1 (\ a' -> runPrint p2 (lmap (mappend a') k) a) a)

instance Monoid (Printer r a) where
  mempty = printer (const . ($ mempty))

instance Document (Printer r a) where
  char c = printer (const . ($ char c))
  string s = printer (const . ($ string s))

instance Contravariant (Printer r) where
  contramap f (Printer r) = Printer (lmap f . r)


-- Construction

printer :: ((Doc -> r) -> (a -> r)) -> Printer r a
printer = Printer

withSubject :: (a -> Printer r a) -> Printer r a
withSubject f = printer (\ k a -> runPrint (f a) k a)

contrapure :: (b -> a) -> Printer r (Coexp r a b)
contrapure f = printer (\ _ (a :>-- b) -> a (f b))


-- Elimination

print :: Printer Doc a -> a -> Doc
print p = runPrint p id

appPrint :: Printer r a -> a -> (Doc -> r) -> r
appPrint p a k = runPrint p k a


-- Computation

(<&>) :: Printer r (Coexp r a b) -> Printer r a -> Printer r b
pf <&> pa = printer (\ k b -> runPrint pf k (runPrint pa k >-- b))

infixl 3 <&>

(<&) :: Printer r a -> Printer r a -> Printer r a
p1 <& p2 = printer (\ k a -> runPrint p1 (\ d1 -> runPrint p2 (k . mappend d1) a) a)

infixl 3 <&

(&>) :: Printer r a -> Printer r a -> Printer r a
p1 &> p2 = printer (\ k a -> runPrint p1 (\ d1 -> runPrint p2 (k . mappend d1) a) a)

infixl 3 &>

(<#>) :: (c -> Either a b) -> Printer r a -> Printer r (Coexp r b c)
f <#> a = contramapExp (cocurry f) a

infixl 3 <#>

liftP2 :: (Coexp r b c -> a) -> Printer r a -> Printer r b -> Printer r c
liftP2 f a b = contramap f a <&> b

liftC2 :: (c -> Either a b) -> Printer r a -> Printer r b -> Printer r c
liftC2 f pa pb = printer (\ k c -> either (runPrint pa k) (runPrint pb k) (f c))


(<:>) :: Printer r a -> Printer r a -> Printer r a
(<:>) = fanoutWith (<>)

infixl 4 <:>

fanoutWith :: (Doc -> Doc -> Doc) -> Printer r a -> Printer r a -> Printer r a
fanoutWith f l r = printer (\ k a -> appPrint l a (appPrint r a . (k .) . f))


-- Combinators

tuple :: Printer r a -> Printer r b -> Printer r (a, b)
tuple a b = fanoutWith combine (contramap fst a) (contramap snd b)
  where
  combine da db = parens (da <> comma <+> db)

list :: Printer r a -> Printer r [a]
list pa = brackets go
  where
  go = maybeToEither . uncons <#> mempty <&> (contramap fst pa <:> contramap snd tail)
  tail = fmap toList . maybeToEither . nonEmpty <#> mempty <&> comma <:> space <:> go

maybeToEither :: Maybe a -> Either () a
maybeToEither = maybe (Left ()) Right

char1 :: Printer r Char
char1 = printer (. char)

string1 :: Printer r String
string1 = printer (. string)


-- Exponentials

newtype Exp r a b = F { runF :: (b -> r) -> (a -> r) }

instance Profunctor (Exp r) where
  dimap f g (F r) = F (dimap (lmap g) (lmap f) r)

instance Choice (Exp r) where
  left'  (F r) = F (\ k -> r (inlL k) <--> inrL k)
  right' (F r) = F (\ k -> inlL k <--> r (inrL k))

instance Cochoice (Exp r) where
  unleft  (F f) = F (\ k -> inlL (let f' = f (k <--> inrL f') in f'))
  unright (F f) = F (\ k -> inrL (let f' = f (inlL f' <--> k) in f'))

instance Strong (Exp r) where
  first'  (F r) = F (\ k (a, c) -> r (lmap (,c) k) a)
  second' (F r) = F (\ k (c, a) -> r (lmap (c,) k) a)

instance Functor (Exp r a) where
  fmap = rmap

instance Applicative (Exp r a) where
  pure a = F (const . ($ a))
  (<*>) = ap

instance Monad (Exp r a) where
  F r >>= f = F (\ k i -> r (\ a -> runF (f a) k i) i)


appF :: Exp r a b -> a -> (b -> r) -> r
appF f a b = runF f b a

(#) :: Exp b a b -> (a -> b)
f # a = runF f id a

infixl 9 #


contramapExp :: Exp r a' a -> (Printer r a -> Printer r a')
contramapExp f pa = printer (\ k a' -> appF f a' (runPrint pa k))


-- Coexponentials

data Coexp r b a = (:>--) { coK :: b -> r, coconst :: a }
  deriving (Functor)

infixr 0 >--, :>--

instance Profunctor (Coexp r) where
  dimap f g (a :>-- b) = lmap f a >-- g b


(>--) :: (b -> r) -> a -> Coexp r b a
(>--) = (:>--)

cocurry :: (c -> Either a b) -> Exp r (Coexp r b c) a
cocurry f = F $ \ k (b :>-- c) -> either k b (f c)
