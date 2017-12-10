%include lhs2TeX.fmt

%format <|> = "\mathbin{<\!\!|\!\!>}"
%format <*> = "\mathbin{<\!\!*\!\!>}"
%format <*  = "\mathbin{<\!\!*}"
%format *>  = "\mathbin{*\!\!>}"
%format <$> = "\mathbin{<\!\!\$\!\!>}"

\begin{code}
{-# LANGUAGE TupleSections        #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE InstanceSigs         #-}

module Parser where

import Data.Maybe
import Text.Read
import Control.Applicative hiding (some, many)
import Control.Monad (ap)
\end{code}

%<*parser>
\begin{code}
newtype Parser a = Parser { runParser
  ::  String           -- input string
  ->  [(String, a)] }  -- pairs of leftovers and values
\end{code}
%</parser>

%<*parse>
\begin{code}
parse :: Parser a -> String -> Maybe a
parse p s = case filter (null . fst) (runParser p s) of
    [(_, a)]  -> Just a
    _         -> Nothing
\end{code}
%</parse>

%<*anychar>
\begin{code}
anyChar :: Parser Char
anyChar = Parser $ \ s -> case s of
  []       -> []
  (c : s)  -> [(s, c)]
\end{code}
%</anychar>

%<*guard>
\begin{code}
guard :: (a -> Bool) -> Parser a -> Parser a
guard f p = Parser $ filter (f . snd) . runParser p
\end{code}
%</guard>
%<*digit>
\begin{code}
digit :: Parser Char
digit = guard (`elem` "0123456789") anyChar
\end{code}
%</digit>
%<*guard2>
\begin{code}
guardM :: (a -> Maybe b) -> Parser a -> Parser b
guardM f p = Parser  $ catMaybes . fmap (traverse f) . runParser p
\end{code}
%</guard2>
%<*digit2>
\begin{code}
digit :: Parser Int
digit = guardM (readMaybe . (:[])) anyChar
\end{code}
%</digit2>

\begin{code}
instance Functor Parser where
\end{code}
%<*fmap>
\begin{code}
fmap :: (a -> b) -> Parser a -> Parser b
\end{code}
%</fmap>
\begin{code}
  fmap f p = Parser $ fmap (fmap f) . runParser p

instance Applicative Parser where
\end{code}
%<*applicative>
\begin{code}
pure   :: a -> Parser a
(<*>)  :: Parser (a -> b) -> Parser a -> Parser b
\end{code}
%</applicative>
\begin{code}

  pure a = Parser $ \ s -> [(s,a)]
  (<*>)  = ap

instance Monad Parser where
\end{code}
%<*monad>
\begin{code}
(>>=) :: Parser a -> (a -> Parser b) -> Parser b
\end{code}
%</monad>
\begin{code}
  return  = pure
  p >>= f = Parser $ \ s -> runParser p s >>= \ (s', a) -> runParser (f a) s'

instance Alternative Parser where

\end{code}
%<*alternative>
\begin{code}
empty  :: Parser a
(<|>)  :: Parser a -> Parser a -> Parser a
\end{code}
%</alternative>
\begin{code}
  empty = Parser (const [])
  p <|> q = Parser $ \ s -> runParser p s ++ runParser q s
\end{code}
%<*some>
\begin{code}
some :: Parser a -> Parser [a]
some p = (:) <$> p <*> many p
\end{code}
%</some>
%<*many>
\begin{code}
many :: Parser a -> Parser [a]
many p = some p <|> pure []
\end{code}
%</many>
%<*some2>
\begin{code}
some :: Parser a -> Parser [a]
some p = (:) <$> p <*> (some p <|> pure [])
\end{code}
%</some2>
%<*Expr>
\begin{code}
data Expr = Lit Int | Add Expr Expr
\end{code}
%</Expr>
\begin{code}
  deriving (Show)

char :: Char -> Parser Char
char c = guard (c ==) anyChar

int :: Parser Int
int = convert <$> some digit where
  convert ds = sum $ zipWith (\ d e -> d * 10 ^ e) (reverse ds) [0..]
\end{code}

%<*expr>
\begin{code}
expr :: Parser Expr
expr  = Lit <$> int <|> Add <$> expr <* char '+' <*> expr
\end{code}
%</expr>
%<*base>
\begin{code}
base :: Parser Expr
base  = Lit <$> int <|>  char '(' *> expr' <* char ')'
\end{code}
%</base>
%<*expr2>
\begin{code}
expr :: Parser Expr
expr = base <|> Add <$> base <* char '+' <*> expr'
\end{code}
%</expr2>

%<*hchainl>
\begin{code}
hchainl :: Parser a -> Parser (a -> b -> a) -> Parser b -> Parser a
hchainl seed con arg  = seed >>= rest where

  rest :: a -> Parser a
  rest a =  do { f <- con; b <- arg; rest (f a b) } <|> pure a
\end{code}
%</hchainl>

%<*example>
\begin{code}
expr    = term   `chainl1` addop
term    = factor `chainl1` mulop
factor  = parens expr <|> integer

mulop   =   do{ symbol "*"; pure (*)   }
        <|> do{ symbol "/"; pure (div) }

addop   =   do{ symbol "+"; pure (+) }
        <|> do{ symbol "-"; pure (-) }
\end{code}
%</example>
