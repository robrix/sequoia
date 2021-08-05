module Sequoia.Print.Class
( -- * Pretty-printing
  Document(..)
  -- * Combinators
, parensIf
, concatWith
, hsep
, vsep
, fillSep
, sep
, hcat
, vcat
, fillCat
, cat
, punctuate
, enclose
, encloseSep
, list
, tupled
, surround
, (<+>)
, (</>)
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
, line
, line'
, softline
, softline'
, semi
, comma
, colon
, dot
, slash
, backslash
, equals
, pipe
  -- * Responsive documents
, ResponsiveDocument(..)
  -- * Combinators
, width
, fill
, fillBreak
) where

import Control.Applicative (liftA2)
import Data.Maybe (fromMaybe)
import Data.Semigroup

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

  hardline :: p
  hardline = char '\n'


  group :: p -> p
  group = id

  flatAlt :: p -> p -> p
  flatAlt = const

  nest :: Int -> p -> p
  nest _ = id


instance Document b => Document (a -> b) where
  char   = pure . char
  string = pure . string

  enclosing l r x = enclosing <$> l <*> r <*> x

  parens = fmap parens
  brackets = fmap brackets
  braces = fmap braces
  angles = fmap angles
  squotes = fmap squotes
  dquotes = fmap dquotes

  hardline = pure hardline

  group = fmap group
  flatAlt = liftA2 flatAlt
  nest i = fmap (nest i)


-- Combinators

parensIf :: Document p => Bool -> p -> p
parensIf True  = parens
parensIf False = id

concatWith :: (Monoid p, Foldable t) => (p -> p -> p) -> t p -> p
concatWith (<>) = fromMaybe mempty . foldr (\ a -> Just . maybe a (a <>)) Nothing


hsep :: Document p => [p] -> p
hsep = concatWith (<+>)

vsep :: Document p => [p] -> p
vsep = concatWith (</>)

fillSep :: Document p => [p] -> p
fillSep = concatWith (surround softline)

sep :: Document p => [p] -> p
sep = group . vsep


hcat :: Document p => [p] -> p
hcat = mconcat

vcat :: Document p => [p] -> p
vcat = concatWith (surround line')

fillCat :: Document p => [p] -> p
fillCat = concatWith (surround softline')

cat :: Document p => [p] -> p
cat = group . vcat


punctuate :: Document p => p -> [p] -> [p]
punctuate s = go
  where
  go []     = []
  go [x]    = [x]
  go (x:xs) = x <> s : go xs


enclose :: Semigroup p => p -> p -> p -> p
enclose l r x = l <> x <> r


encloseSep :: Document p => p -> p -> p -> [p] -> p
encloseSep l r s ps = enclose l r (group (concatWith (surround (line' <> s)) ps))


list :: Document p => [p] -> p
list
  = group
  . brackets
  . encloseSep
    (flatAlt space mempty)
    (flatAlt space mempty)
    (comma <> space)

tupled :: Document p => [p] -> p
tupled
  = group
  . parens
  . encloseSep
    (flatAlt space mempty)
    (flatAlt space mempty)
    (comma <> space)


surround :: Semigroup p => p -> p -> p -> p
surround x l r = enclose l r x


(<+>) :: Document p => p -> p -> p
(<+>) = surround space

infixr 6 <+>

(</>) :: Document p => p -> p -> p
(</>) = surround line

infixr 6 </>


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

space, line, line', softline, softline' :: Document p => p
space = char ' '
line = flatAlt hardline space
line' = flatAlt hardline mempty
softline = flatAlt space hardline
softline' = flatAlt mempty hardline

semi, comma, colon, dot, slash, backslash, equals, pipe :: Document p => p
semi = char ';'
comma = char ','
colon = char ':'
dot = char '.'
slash = char '/'
backslash = char '\\'
equals = char '='
pipe = char '|'


-- Responsive documents

class Document p => ResponsiveDocument p where
  column :: (Int -> p) -> p

instance ResponsiveDocument b => ResponsiveDocument (a -> b) where
  column f a = column (`f` a)


-- Combinators

width :: ResponsiveDocument p => p -> (Int -> p) -> p
width p f = column $ \ start -> p <> column (\ end -> f (end - start))


fill :: ResponsiveDocument p => Int -> p -> p
fill n p = width p $ \ w -> stimes (n - w) space

fillBreak :: ResponsiveDocument p => Int -> p -> p
fillBreak f x = width x go
  where
  go w
    | w > f = nest f line'
    | otherwise = stimes (f - w) space
