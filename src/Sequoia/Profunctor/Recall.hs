module Sequoia.Profunctor.Recall
( Recall(..)
) where

newtype Recall e a b = Recall { runRecall :: e -> b }
  deriving (Applicative, Functor, Monad)
