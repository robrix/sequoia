{-# LANGUAGE QuantifiedConstraints #-}
-- | Pretty-printing.
module Sequoia.Printer
( Doc(..)
, printer
, Printer(..)
, prec
, atom
, withPrec
, Prec(..)
, PrecPrinter(..)
, Print(..)
) where

import Data.Functor.Contravariant
import Data.Monoid (Endo(..))
import Prelude hiding (print)

newtype Doc = Doc { getDoc :: ShowS }
  deriving (Monoid, Semigroup) via Endo String


printer :: (forall x . a -> Printer x) -> Printer a
printer f = Printer (print . f <*> id)

newtype Printer a = Printer { print :: a -> Doc }
  deriving (Monoid, Semigroup)

instance Contravariant Printer where
  contramap f (Printer r) = Printer (r . f)

instance Print Printer where
  char = Printer . const . Doc . (:)


prec :: Print p => Prec -> p a -> PrecPrinter p a
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

parensIf :: Print p => Bool -> p a -> p a
parensIf True  = parens
parensIf False = id

class (Contravariant p, forall a . Monoid (p a)) => Print p where
  {-# MINIMAL char | string #-}
  char :: Char -> p a
  char c = string [c]
  string :: String -> p a
  string = foldMap char

  lparen, rparen :: p a
  lparen = char '('
  rparen = char ')'

  space :: p a
  space = char ' '

  comma :: p a
  comma = char ','

  (<+>) :: p a -> p a -> p a
  (<+>) = surround space

  infixl 4 <+>

  surround :: p a -> p a -> p a -> p a
  surround x l r = enclose l r x

  enclose :: p a -> p a -> p a -> p a
  enclose l r x = l <> x <> r

  parens :: p a -> p a
  parens = enclose lparen rparen
