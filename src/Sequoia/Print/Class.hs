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
, space'
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
, align
, hang
, indent
, width
, fill
, fillBreak
) where

import Control.Applicative (liftA2)
import Data.Foldable (fold)
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


hsep :: (Document p, Foldable t) => t p -> p
hsep = concatWith (<+>)

vsep :: (Document p, Foldable t) => t p -> p
vsep = concatWith (</>)

fillSep :: (Document p, Foldable t) => t p -> p
fillSep = concatWith (surround softline)

sep :: (Document p, Foldable t) => t p -> p
sep = group . vsep


hcat :: (Document p, Foldable t) => t p -> p
hcat = fold

vcat :: (Document p, Foldable t) => t p -> p
vcat = concatWith (surround line')

fillCat :: (Document p, Foldable t) => t p -> p
fillCat = concatWith (surround softline')

cat :: (Document p, Foldable t) => t p -> p
cat = group . vcat


punctuate :: (Document p, Foldable t) => p -> t p -> [p]
punctuate s = fromMaybe [] . foldr (\ a -> maybe (Just [a]) (Just . (a <> s :))) Nothing


enclose :: Semigroup p => p -> p -> p -> p
enclose l r x = l <> x <> r


encloseSep :: (Document p, Foldable t) => p -> p -> p -> t p -> p
encloseSep l r s = enclose l r . group . concatWith (surround (line' <> s))


list :: (Document p, Foldable t) => t p -> p
list = group . brackets . encloseSep space' space' (comma <> space)

tupled :: (Document p, Foldable t) => t p -> p
tupled = group . parens . encloseSep space' space' (comma <> space)


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

space, space', line, line', softline, softline' :: Document p => p
space = char ' '
space' = flatAlt space mempty
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
  nesting :: (Int -> p) -> p

instance ResponsiveDocument b => ResponsiveDocument (a -> b) where
  column f a = column (`f` a)
  nesting f a = nesting (`f` a)


-- Combinators

align :: ResponsiveDocument p => p -> p
align d = column (\ k -> nesting (\ i -> nest (k - i) d))

hang :: ResponsiveDocument p => Int -> p -> p
hang = fmap align . nest

indent :: ResponsiveDocument p => Int -> p -> p
indent i d = hang i (stimes i space <> d)


width :: ResponsiveDocument p => p -> (Int -> p) -> p
width p f = column $ \ start -> p <> column (\ end -> f (end - start))


fill :: ResponsiveDocument p => Int -> p -> p
fill n p = width p $ \ w -> stimes (n - w) space

fillBreak :: ResponsiveDocument p => Int -> p -> p
fillBreak f x = width x $ \case
  w | w > f     -> nest f line'
    | otherwise -> stimes (f - w) space
