{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}
module Focalized.HOAS ( module Focalized.HOAS ) where

import Control.Applicative (Alternative(..), liftA2, optional, (<**>))
import Control.Monad (ap, guard, void, (<=<))
import Data.Char
import Data.Distributive
import Data.Foldable (asum, traverse_)

newtype Name = Name { getName :: String }
  deriving (Eq, Ord, Show)

newtype Level = Level { getLevel :: Int }
  deriving (Enum, Eq, Num, Ord, Show)

newtype Index = Index { getIndex :: Int }
  deriving (Enum, Eq, Num, Ord, Show)

levelToIndex :: Level -> Level -> Index
levelToIndex (Level d) (Level level) = Index $ d - level - 1

indexToLevel :: Level -> Index -> Level
indexToLevel (Level d) (Index index) = Level $ d - index - 1


class App rep where
  app :: rep -> rep -> rep

class Var a rep | rep -> a where
  var :: Name -> a -> rep

class App rep => HO rep where
  lamHO :: Name -> (rep -> rep) -> rep

class App rep => FO rep where
  lamFO :: Name -> rep -> rep

type f ~> g = forall x . f x -> g x

lam :: (Applicative i, Applicative m, HO rep) => Name -> (forall j . Applicative j => (i ~> j) -> j rep -> m (j rep)) -> m (i rep)
lam n b = fmap (lamHO n) . getC <$> b liftCOut (liftCIn id)

($$) :: (Applicative m, App rep) => m rep -> m rep -> m rep
($$) = liftA2 app


data FOD a
  = VarFO Name a
  | LamFO Name (FOD a)
  | AppFO (FOD a) (FOD a)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

interpretFO :: (Var Index rep, FO rep) => FOD rep -> rep
interpretFO = \case
  VarFO _ s -> s
  LamFO n b -> lamFO n (interpretFO b)
  AppFO f a -> app (interpretFO f) (interpretFO a)

instance App (FOD a) where
  app = AppFO

instance Var a (FOD a) where
  var = VarFO

instance FO (FOD a) where
  lamFO = LamFO


newtype Quote a = Quote (Level -> a)

quote :: Level -> Quote a -> a
quote d (Quote run) = run d

varQ :: Name -> Level -> Quote (FOD Index)
varQ n a = Quote (VarFO n . (`levelToIndex` a))

instance App r => App (Quote r) where
  app f a = Quote (\ d -> app (quote d f) (quote d a))

instance HO (Quote (FOD Index)) where
  lamHO n b = Quote (\ d -> lamFO n (quote (succ d) (b (varQ n d))))


newtype Eval r = Eval ([r] -> r)

eval :: [r] -> Eval r -> r
eval env (Eval run) = run env

instance Var Index (Eval r) where
  var _ i = Eval (!! getIndex i)

instance App r => App (Eval r) where
  app (Eval f) (Eval a) = Eval $ \ env -> app (f env) (a env)

instance HO r => FO (Eval r) where
  lamFO n b = Eval $ \ env -> lamHO n (\ v -> eval (v:env) b)


data HOD a
  = VarHO Name a
  | LamHO Name (HOD a -> HOD a)
  | AppHO (HOD a) (HOD a)

interpretHO :: HO rep => HOD rep -> rep
interpretHO = \case
  VarHO _ s -> s
  LamHO n b -> lamHO n (interpretHO . b . VarHO n)
  AppHO f a -> app (interpretHO f) (interpretHO a)

instance App (HOD a) where
  app = AppHO

instance HO (HOD a) where
  lamHO = LamHO

instance Show (HOD PrecPrint) where
  showsPrec p = showsPrec p . interpretHO @PrecPrint


-- Pretty-printing

newtype Prec = Prec { getPrec :: Int }
  deriving (Eq, Num, Ord, Show)

newtype Counter = Counter { getCounter :: Int }
  deriving (Eq, Num, Ord, Show)

newtype Print = Print { getPrint :: Counter -> ShowS }

instance Show Print where
  showsPrec _ p = getPrint p 0

instance Semigroup Print where
  Print a <> Print b = Print (\ v -> a v . b v)

instance Monoid Print where
  mempty = Print (const id)

str :: String -> Print
str = Print . const . showString

parensIf :: Bool -> Print -> Print
parensIf True  p = str "(" <> p <> str ")"
parensIf False p = p

scope :: Name -> (Print -> Print) -> Print
scope _ b = Print $ \ v i -> getPrint (b (str (toAlpha v))) v i

alphabet :: String
alphabet = ['a'..'z']

toAlpha :: Counter -> String
toAlpha (Counter i) = alphabet !! r : if q > 0 then show q else ""
  where
  n = length alphabet
  (q, r) = i `divMod` n


-- Precedence-respecting printing

newtype PrecPrint = PrecPrint { getPrecPrint :: Prec -> Print }

instance Semigroup PrecPrint where
  PrecPrint a <> PrecPrint b = PrecPrint (a <> b)

instance Monoid PrecPrint where
  mempty = PrecPrint mempty

prec :: Prec -> Print -> PrecPrint
prec i b = PrecPrint $ \ i' -> parensIf (i' > i) b

atom :: Print -> PrecPrint
atom = PrecPrint . const

withPrec :: Prec -> PrecPrint -> Print
withPrec = flip getPrecPrint

instance App PrecPrint where
  app f a = prec 10 (withPrec 10 f <> str " " <> withPrec 11 a)

instance HO PrecPrint where
  lamHO n b = prec 0 (scope n (\ v -> str "λ " <> v <> str " . " <> withPrec 0 (b (atom v))))

instance Show PrecPrint where
  showsPrec i p = getPrint (getPrecPrint p (Prec i)) 0


newtype I a = I { getI :: a }
  deriving (Eq, Ord, Foldable, Functor, Show, Traversable)

instance Applicative I where
  pure = I
  liftA2 f a b = I (f (getI a) (getI b))

instance Monad I where
  I a >>= f = f a

instance Distributive I where
  collect f = I . fmap (getI . f)
  distribute = I . fmap getI


newtype K a b = K { getK :: a }
  deriving (Eq, Ord, Foldable, Functor, Show, Traversable)

instance Monoid a => Applicative (K a) where
  pure _ = K mempty
  K a <*> K b = K (a <> b)


newtype (f :.: g) a = C { getC :: f (g a) }
  deriving (Foldable, Functor, Traversable)

instance (Applicative f, Applicative g) => Applicative (f :.: g) where
  pure = C . pure . pure

  liftA2 f a b = C (liftA2 (liftA2 f) (getC a) (getC b))

instance (Alternative f, Applicative g) => Alternative (f :.: g) where
  empty = C empty
  C l <|> C r = C (l <|> r)


strengthenOut :: Functor f => (f :.: I) a -> f a
strengthenOut = fmap getI . getC

liftCIn :: Applicative f => g a -> (f :.: g) a
liftCIn = C . pure

mapCIn :: Applicative f => (g a -> h b) -> (f :.: g) a -> (f :.: h) b
mapCIn f = C . fmap f . getC

liftCOut :: (Functor f, Applicative g) => f a -> (f :.: g) a
liftCOut = C . fmap pure


parse :: Parser a -> String -> Maybe a
parse p = fmap snd . runParser (whole p)

newtype Parser a = Parser { runParser :: String -> Maybe (String, a) }
  deriving (Functor)

instance Applicative Parser where
  pure a = Parser (\ s -> Just (s, a))
  (<*>) = ap

instance Alternative Parser where
  empty = Parser (const Nothing)
  Parser l <|> Parser r = Parser (\ s -> l s <|> r s)

instance Monad Parser where
  Parser a >>= f = Parser (\ s -> do
    (s', a') <- a s
    runParser (f a') s')

class Alternative p => CharParsing p where
  satisfy :: (Char -> Bool) -> p Char
  eof :: p ()

instance CharParsing Parser where
  satisfy p = Parser (\case
    []   -> Nothing
    c:cs -> (cs, c) <$ guard (p c))

  eof = Parser (fmap ("",) . guard . null)

instance (CharParsing f, Applicative g) => CharParsing (f :.: g) where
  satisfy p = liftCOut (satisfy p)
  eof = liftCOut eof

char :: CharParsing p => Char -> p Char
char = satisfy . (==)

string :: CharParsing p => String -> p String
string s = s <$ traverse_ char s

parens :: CharParsing p => p a -> p a
parens p = char '(' *> p <* char ')'

ws :: CharParsing p => p ()
ws = void (some (satisfy isSpace))

token :: CharParsing p => p a -> p a
token p = p <* optional ws

chainl1 :: Alternative m => m a -> m (a -> a -> a) -> m a
chainl1 p op = scan where
  scan = p <**> rst
  rst = (\f y g x -> g (f x y)) <$> op <*> p <*> rst <|> pure id

whole :: CharParsing p => p a -> p a
whole p = optional ws *> p <* eof


pprog :: HO rep => Parser rep
pprog = getI <$> pexp []

pexp, plam, papp, patom :: (Monad p, CharParsing p, Applicative i, HO rep) => [p (i rep)] -> p (i rep)

pexp env = plam env <|> papp env

plam env = do
  n <- token (char 'λ') *> pname <* token (char '.')
  lam n (\ wk v -> pexp ((v <$ string (getName n)) : map (fmap wk) env))

papp env = patom env `chainl1` (($$) <$ optional ws)

patom env = asum env <|> parens (pexp env)

pname :: CharParsing p => p Name
pname = Name <$> token ((:) <$> satisfy isAlpha <*> many (satisfy isAlphaNum))


-- Types

data Type = Base | Type :-> Type
  deriving (Eq, Ord, Show)

infixr 3 :->


data Typed a = a ::: Type
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

infix 2 :::

getType :: Typed a -> Type
getType (_ ::: _T) = _T

curryTyped :: (Typed a -> b) -> (Type -> a -> b)
curryTyped f _T a = f $ a ::: _T

uncurryTyped :: (Type -> a -> b) -> (Typed a -> b)
uncurryTyped f (a ::: _T) = f _T a


newtype Check a = Check { check :: Type -> Maybe a }
  deriving (Functor)

newtype Synth a = Synth { synth :: Maybe (Typed a) }
  deriving (Functor)


checkTyped :: Typed (Check a) -> Maybe a
checkTyped (m ::: _T) = check m _T

switch :: Synth a -> Check a
switch s = Check $ \ _T -> do
  a ::: _T' <- synth s
  a <$ guard (_T == _T')


data (f :+: g) a = InL (f a) | InR (g a)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

infixr 5 :+:

exlr :: (f a -> b) -> (g a -> b) -> (f :+: g) a -> b
exlr f g = \case
  InL a -> f a
  InR b -> g b

prjL :: Alternative m => (f :+: g) a -> m (f a)
prjL = pure `exlr` const empty

prjR :: Alternative m => (f :+: g) a -> m (g a)
prjR = const empty `exlr` pure


mkSyn :: Maybe (Typed a) -> (Synth :+: Check) a
mkSyn = InL . Synth

syn :: (Synth :+: Check) a -> Maybe (Typed a)
syn = synth <=< prjL


mkChk :: (Type -> Maybe a) -> (Synth :+: Check) a
mkChk = InR . Check

chk :: Typed ((Synth :+: Check) a) -> Maybe a
chk = checkTyped <=< traverse prjR


newtype Elab c a = Elab ([c] -> (Synth :+: Check) a)
  deriving (Functor)

elab :: [c] -> Elab c a -> (Synth :+: Check) a
elab ctx (Elab run) = run ctx

instance (App a, Applicative i) => App (Elab (i a) (i a)) where
  app f a = Elab $ \ ctx -> mkSyn $ do
    f' ::: _A :-> _B <- syn (elab ctx f)
    a' <- chk (elab ctx a ::: _A)
    pure $ f' $$ a' ::: _B
