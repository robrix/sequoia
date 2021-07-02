-- | Pretty-printing.
module Focalized.Printer
( Printer(..)
, prec
, atom
, withPrec
, Prec(..)
, PrecPrinter(..)
, Print(..)
) where

import Data.Functor.Contravariant

newtype Printer a = Printer { runPrinter :: a -> ShowS }

instance Contravariant Printer where
  contramap f (Printer r) = Printer (r . f)


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


parensIf :: Print p => Bool -> p -> p
parensIf True  = parens
parensIf False = id

class Monoid p => Print p where
  char :: Char -> p
  string :: String -> p
  string = foldMap char

  lparen, rparen :: p
  lparen = char '('
  rparen = char ')'

  surround :: p -> p -> p -> p
  surround l r x = l <> x <> r

  parens :: p -> p
  parens = surround lparen rparen
