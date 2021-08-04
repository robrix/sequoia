module Sequoia.Print.Class
( -- * Pretty-printing
  Print(..)
  -- * Combinators
, parensIf
) where

import Control.Applicative (liftA2)

-- Pretty-printing

class Monoid p => Print p where
  {-# MINIMAL char | string #-}
  char :: Char -> p
  char c = string [c]
  string :: String -> p
  string = foldMap char

  lparen, rparen :: p
  lparen = char '('
  rparen = char ')'

  space :: p
  space = char ' '

  comma :: p
  comma = char ','

  (<+>) :: p -> p -> p
  (<+>) = surround space

  infixr 6 <+>

  surround :: p -> p -> p -> p
  surround x l r = enclose l r x

  enclose :: p -> p -> p -> p
  enclose l r x = l <> x <> r

  parens :: p -> p
  parens = enclose lparen rparen

instance Print b => Print (a -> b) where
  char   = pure . char
  string = pure . string

  lparen = pure lparen
  rparen = pure rparen
  space = pure space
  comma = pure comma

  (<+>) = liftA2 (<+>)

  surround x l r = enclose <$> x <*> l <*> r
  enclose l r x = enclose <$> l <*> r <*> x

  parens f = parens <$> f


-- Combinators

parensIf :: Print p => Bool -> p -> p
parensIf True  = parens
parensIf False = id
