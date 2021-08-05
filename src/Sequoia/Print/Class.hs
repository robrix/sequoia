module Sequoia.Print.Class
( -- * Pretty-printing
  Document(..)
  -- * Combinators
, parensIf
, concatWith
, (<+>)
  -- * Characters
, lparen
, rparen
, lbracket
, rbracket
, lbrace
, rbrace
, langle
, rangle
, squote
, dquote
, space
, comma
) where

import Data.Maybe (fromMaybe)

-- Pretty-printing

class Monoid p => Document p where
  {-# MINIMAL char | string #-}
  char :: Char -> p
  char c = string [c]
  string :: String -> p
  string = foldMap char

  surround :: p -> p -> p -> p
  surround x l r = enclose l r x

  enclose :: p -> p -> p -> p
  enclose l r x = l <> x <> r

  parens :: p -> p
  parens = enclose lparen rparen

  brackets :: p -> p
  brackets = enclose lbracket rbracket

  braces :: p -> p
  braces = enclose lbrace rbrace

  angles :: p -> p
  angles = enclose langle rangle

instance Document b => Document (a -> b) where
  char   = pure . char
  string = pure . string

  surround x l r = enclose <$> x <*> l <*> r
  enclose l r x = enclose <$> l <*> r <*> x

  parens f = parens <$> f
  brackets f = brackets <$> f
  braces f = braces <$> f
  angles f = angles <$> f


-- Combinators

parensIf :: Document p => Bool -> p -> p
parensIf True  = parens
parensIf False = id

concatWith :: (Monoid p, Foldable t) => (p -> p -> p) -> t p -> p
concatWith (<>) = fromMaybe mempty . foldr (\ a -> Just . maybe a (a <>)) Nothing


(<+>) :: Document p => p -> p -> p
(<+>) = surround space

infixr 6 <+>


-- Characters

lparen, rparen :: Document p => p
lparen = char '('
rparen = char ')'

lbracket, rbracket :: Document p => p
lbracket = char '['
rbracket = char ']'

lbrace, rbrace :: Document p => p
lbrace = char '{'
rbrace = char '}'

langle, rangle :: Document p => p
langle = char '<'
rangle = char '>'

squote, dquote :: Document p => p
squote = char '\''
dquote = char '"'

space :: Document p => p
space = char ' '

comma :: Document p => p
comma = char ','
