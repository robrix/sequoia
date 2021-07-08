-- | 'Representable' functors from 'Corepresentable' 'Profunctor's.
module Sequoia.Functor.CorepRep
( CorepRep(..)
) where

newtype CorepRep p s a = CorepRep { getCorepRep :: p s a }
