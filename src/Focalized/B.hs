module Focalized.B
( B(..)
, viewl
, viewr
) where

import Control.Applicative (Alternative(..))
import Data.Foldable (toList)

data B a
  = Nil
  | Leaf a
  | B a :<>: B a
  deriving (Eq, Foldable, Functor, Ord, Traversable)

infixr 5 :<>:

instance Show a => Show (B a) where
  showsPrec _ = showList . toList

instance Semigroup (B a) where
  Nil <> b   = b
  a   <> Nil = a
  a   <> b   = a :<>: b

instance Monoid (B a) where
  mempty = Nil

instance Applicative B where
  pure = Leaf

  Nil        <*> _ = Nil
  Leaf f     <*> a = f <$> a
  fl :<>: fr <*> a = (fl <*> a) <> (fr <*> a)

instance Alternative B where
  empty = Nil
  (<|>) = (<>)

instance Monad B where
  Nil        >>= _ = Nil
  Leaf a     >>= f = f a
  al :<>: ar >>= f = (al >>= f) <> (ar >>= f)


viewl :: Alternative m => B a -> m (a, B a)
viewl = \case
  Nil               -> empty
  Leaf a            -> pure (a, Nil)
  Nil :<>: r        -> viewl r
  Leaf a :<>: r     -> pure (a, r)
  (l :<>: m) :<>: r -> viewl (l :<>: (m :<>: r))

viewr :: Alternative m => B a -> m (B a, a)
viewr = \case
  Nil               -> empty
  Leaf a            -> pure (Nil, a)
  l :<>: Nil        -> viewr l
  l :<>: Leaf a     -> pure (l, a)
  l :<>: (m :<>: r) -> viewr ((l :<>: m) :<>: r)
