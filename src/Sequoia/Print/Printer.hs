{-# LANGUAGE FunctionalDependencies #-}
-- | Pretty-printing.
module Sequoia.Print.Printer
( -- * Printers
  Printer(..)
  -- * Construction
, printer
, withSubject
  -- * Elimination
, getPrint
, print
, appPrint
, runPrint
  -- * Computation
, fanoutWith
  -- * Combinators
, tuple
, list
, char1
, string1
) where

import Data.List (uncons)
import Data.List.NonEmpty (nonEmpty, toList)
import Data.Profunctor
import Prelude hiding (exp, print)
import Sequoia.Print.Class hiding (list)
import Sequoia.Profunctor.Applicative
import Sequoia.Profunctor.Exp

-- Printers

newtype Printer r a b = Printer (a ~~Exp r~> b)
  deriving (Applicative, Choice, Cochoice, Functor, Monad, Profunctor, Strong)

instance Semigroup b => Semigroup (Printer r a b) where
  p1 <> p2 = printer (\ k a -> appPrint p1 a (appPrint p2 a . ((`lmap` k) . (<>))))

instance Monoid b => Monoid (Printer r a b) where
  mempty = printer (const . ($ mempty))

instance Document b =>  Document (Printer r a b) where
  char c = printer (const . ($ char c))
  string s = printer (const . ($ string s))

instance Coapply (Coexp r) (Printer r) where
  pf <&> pa = printer (\ k b -> getPrint pf k (getPrint pa k >- b))

instance Coapplicative (Coexp r) (Printer r) where
  copure = printer . const . runCoexp

instance ProfunctorCPS (Exp r) (Printer r) where
  dimapCPS f g p = printer (getExp f . getPrint p . getExp g)
  lmapCPS f p = printer (getExp f . getPrint p)
  rmapCPS f p = printer (getPrint p . getExp f)


-- Construction

printer :: ((b -> r) -> (a -> r)) -> Printer r a b
printer = Printer . Exp

withSubject :: (a -> Printer r a b) -> Printer r a b
withSubject f = printer (\ k -> runPrint k <*> f)


-- Elimination

getPrint :: Printer r a b -> ((b -> r) -> (a -> r))
getPrint (Printer r) = getExp r

print :: Printer b a b -> a -> b
print p = getPrint p id

runPrint :: (b -> r) -> a -> Printer r a b -> r
runPrint k a p = getPrint p k a

appPrint :: Printer r a b -> a -> (b -> r) -> r
appPrint p a k = getPrint p k a


-- Computation

fanoutWith :: (b -> b -> b) -> Printer r a b -> Printer r a b -> Printer r a b
fanoutWith f l r = printer (\ k a -> appPrint l a (appPrint r a . (k .) . f))


-- Combinators

tuple :: Document c => Printer r a c -> Printer r b c -> Printer r (a, b) c
tuple a b = fanoutWith combine (lmap fst a) (lmap snd b)
  where
  combine da db = parens (da <> comma <+> db)

list :: Document b => Printer r a b -> Printer r [a] b
list pa = brackets go
  where
  go = maybeToEither . uncons <#> mempty <&> lmap fst pa <> lmap snd tail
  tail = fmap toList . maybeToEither . nonEmpty <#> mempty <&> comma <> space <> go

maybeToEither :: Maybe a -> Either () a
maybeToEither = maybe (Left ()) Right

char1 :: Document b => Printer r Char b
char1 = printer (. char)

string1 :: Document b => Printer r String b
string1 = printer (. string)
