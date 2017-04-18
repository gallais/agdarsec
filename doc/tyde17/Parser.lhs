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
  ->  [(String, a)] }  -- possible values + leftover
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
guardM f p = Parser  $ catMaybes . fmap (traverse f)
                     . runParser p
\end{code}
%</guard2>
%<*digit2>
\begin{code}
digit' :: Parser Int
digit' = guardM (readMaybe . (:[])) anyChar
\end{code}
%</digit2>

\begin{code}
instance Functor Parser where
  fmap f p = Parser $ fmap (fmap f) . runParser p

instance Applicative Parser where
  pure a = Parser $ \ s -> [(s,a)]
  (<*>)  = ap

instance Monad Parser where
  return  = pure
  p >>= f = Parser $ \ s -> runParser p s >>= \ (s', a) -> runParser (f a) s'

instance Alternative Parser where
  empty :: Parser a
  empty = Parser (const [])

  (<|>) :: Parser a -> Parser a -> Parser a
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
%<*Expr>
\begin{code}
data Expr = Literal Int | Plus Expr Expr
\end{code}
%</Expr>
\begin{code}
  deriving (Show)

char :: Char -> Parser Char
char c = guard (c ==) anyChar

int :: Parser Int
int = convert <$> some digit' where
  convert ds = sum $ zipWith (\ d e -> d * 10 ^ e) (reverse ds) [0..]
\end{code}

%<*expr>
\begin{code}
expr :: Parser Expr
expr  =    Literal <$> int
      <|>  Plus <$> expr <* char '+' <*> expr
\end{code}
%</expr>
%<*base>
\begin{code}
base :: Parser Expr
base  =    Literal <$> int
      <|>  char '(' *> expr' <* char ')'
\end{code}
%</base>
%<*expr2>
\begin{code}
expr' :: Parser Expr
expr' = base <|> Plus <$> base <* char '+' <*> expr'
\end{code}
%</expr2>
