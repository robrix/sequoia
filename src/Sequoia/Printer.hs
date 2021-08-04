-- | Pretty-printing.
module Sequoia.Printer
( Doc(..)
, printer
, print
, Printer(..)
, prec
, atom
, withPrec
, Prec(..)
, PrecPrinter(..)
) where

import Data.Functor.Contravariant
import Data.Monoid (Endo(..))
import Data.Profunctor
import Prelude hiding (print)
import Sequoia.Print.Class
import Sequoia.Profunctor.Continuation

newtype Doc = Doc { getDoc :: ShowS }
  deriving (Monoid, Semigroup) via Endo String

instance Print Doc where
  char c = Doc (c:)
  string s = Doc (s<>)


printer :: (a -> Printer a) -> Printer a
printer f = Printer (\ k -> K (\ a -> runPrint (f a) k • a))

print :: Printer a -> a -> Doc
print p = (runPrint p idK •)

newtype Printer a = Printer { runPrint :: forall r . Doc • r -> a • r }

instance Semigroup (Printer a) where
  p1 <> p2 = Printer (\ k -> K (\ a -> runPrint p1 (K (\ a' -> runPrint p2 (lmap (mappend a') k) • a)) • a))

instance Monoid (Printer a) where
  mempty = Printer (constK . (• mempty))

instance Print (Printer a) where
  char c = Printer (constK . (• char c))
  string s = Printer (constK . (• string s))

instance Contravariant Printer where
  contramap f (Printer r) = Printer (lmap f . r)


prec :: Print (p a) => Prec -> p a -> PrecPrinter p a
prec i pr = PrecPrinter $ \ i' -> parensIf (i' > i) pr

atom :: p a -> PrecPrinter p a
atom = PrecPrinter . const

withPrec :: Prec -> PrecPrinter p a -> p a
withPrec = flip runPrecPrinter

newtype Prec = Prec { getPrec :: Int }
  deriving (Eq, Ord, Show)

newtype PrecPrinter p a = PrecPrinter { runPrecPrinter :: Prec -> p a }
  deriving (Functor)

instance Contravariant p => Contravariant (PrecPrinter p) where
  contramap f (PrecPrinter r) = PrecPrinter (contramap f . r)
