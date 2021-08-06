{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE QuantifiedConstraints #-}
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


-- Combinators

tuple :: (forall a b . Document b => Document (p a b), Document c, Coapplicative co p) => p a c -> p b c -> p (a, b) c
tuple a b = parens (lmap fst a <> comma <+> lmap snd b)

list :: (forall a b . Document b => Document (p a b), Document b, ProfunctorCPS (Exp r) p, Coapplicative (Coexp r) p) => p a b -> p [a] b
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
