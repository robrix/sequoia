-- | Pretty-printing.
module Sequoia.Print.Printer
( Doc(..)
, printer
, print
, Printer(..)
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
