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
, semi
, comma
, colon
, dot
, slash
, backslash
, equals
, pipe
) where

import Data.Maybe (fromMaybe)

-- Pretty-printing

class Monoid p => Document p where
  {-# MINIMAL char | string #-}
  char :: Char -> p
  char c = string [c]
  string :: String -> p
  string = foldMap char

  enclosing :: p -> p -> p -> p
  enclosing = enclose

  parens :: p -> p
  parens = enclosing lparen rparen

  brackets :: p -> p
  brackets = enclosing lbracket rbracket

  braces :: p -> p
  braces = enclosing lbrace rbrace

  angles :: p -> p
  angles = enclosing langle rangle

  squotes :: p -> p
  squotes = enclosing squote squote

  dquotes :: p -> p
  dquotes = enclosing dquote dquote

instance Document b => Document (a -> b) where
  char   = pure . char
  string = pure . string

  enclosing l r x = enclosing <$> l <*> r <*> x

  parens f = parens <$> f
  brackets f = brackets <$> f
  braces f = braces <$> f
  angles f = angles <$> f
  squotes f = squotes <$> f
  dquotes f = dquotes <$> f


-- Combinators

parensIf :: Document p => Bool -> p -> p
parensIf True  = parens
parensIf False = id

concatWith :: (Monoid p, Foldable t) => (p -> p -> p) -> t p -> p
concatWith (<>) = fromMaybe mempty . foldr (\ a -> Just . maybe a (a <>)) Nothing


enclose :: Semigroup p => p -> p -> p -> p
enclose l r x = l <> x <> r

surround :: Semigroup p => p -> p -> p -> p
surround x l r = enclose l r x


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

semi, comma, colon, dot, slash, backslash, equals, pipe :: Document p => p
semi = char ';'
comma = char ','
colon = char ':'
dot = char '.'
slash = char '/'
backslash = char '\\'
equals = char '='
pipe = char '|'
