{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
module Sequoia.Profunctor.Product
( (:*:)(..)
, (***)
) where

import qualified Control.Arrow as A ((***))
import qualified Control.Category as Cat
import           Data.Functor.Product
import           Data.Profunctor
import           Data.Profunctor.Rep
import           Data.Profunctor.Sieve

newtype (p :*: q) a b = Product { runProduct :: (p a b, q a b) }

infixr 6 :*:

instance (Cat.Category p, Cat.Category q) => Cat.Category (p :*: q) where
  id = Product (Cat.id, Cat.id)
  Product (fp, fq) . Product (gp, gq) = Product (fp Cat.. gp, fq Cat.. gq)

instance (Profunctor p, Profunctor q) => Profunctor (p :*: q) where
  dimap f g = Product . (dimap f g A.*** dimap f g) . runProduct

instance (Strong p, Strong q) => Strong (p :*: q) where
  first'  = Product . (first'  A.*** first')  . runProduct
  second' = Product . (second' A.*** second') . runProduct

instance (Costrong p, Costrong q) => Costrong (p :*: q) where
  unfirst  = Product . (unfirst  A.*** unfirst)  . runProduct
  unsecond = Product . (unsecond A.*** unsecond) . runProduct

instance (Choice p, Choice q) => Choice (p :*: q) where
  left'  = Product . (left'  A.*** left')  . runProduct
  right' = Product . (right' A.*** right') . runProduct

instance (Cochoice p, Cochoice q) => Cochoice (p :*: q) where
  unleft  = Product . (unleft  A.*** unleft)  . runProduct
  unright = Product . (unright A.*** unright) . runProduct

instance (Closed p, Closed q) => Closed (p :*: q) where
  closed = Product . (closed A.*** closed) . runProduct

instance (Sieve p f, Sieve q g) => Sieve (p :*: q) (Product f g) where
  sieve (Product (p, q)) a = Pair (sieve p a) (sieve q a)

instance (Representable p, Representable q) => Representable (p :*: q) where
  type Rep (p :*: q) = Product (Rep p) (Rep q)
  tabulate f' = let f d = let Pair a b = f' d in (a, b) in Product
    ( tabulate (fst . f)
    , tabulate (snd . f) )


(***) :: (Strong p, Cat.Category p) => a1 `p` b1 -> a2 `p` b2 -> (a1, a2) `p` (b1, b2)
f *** g = first' f Cat.>>> second' g

infixr 3 ***
