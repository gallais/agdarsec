{-# LANGUAGE TupleSections        #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE InstanceSigs         #-}

module Parser where

import Data.Maybe
import Data.Bifunctor (first)
import Text.Read
import Control.Applicative hiding (some, many)
import Control.Monad (ap)

newtype Parser a = Parser { runParser
  :: String        -- input string
  -> [(a, String)] -- possible values + leftover
  }

parse :: Parser a -> String -> Maybe a
parse p s = case filter (null . snd) (runParser p s) of
    [(a,[])] -> Just a
    _        -> Nothing

anyChar :: Parser Char
anyChar = Parser $ \ s -> case s of
  []      -> []
  (c : s) -> [(c, s)]

guard :: (a -> Bool) -> Parser a -> Parser a
guard f p = Parser $ filter (f . fst) . runParser p

guard' :: (a -> Maybe b) -> Parser a -> Parser b
guard' f p = Parser $ catMaybes
                    . fmap (\ (a,s) -> fmap (,s) (f a))
                    . runParser p

digit :: Parser Char
digit = guard (`elem` "0123456789") anyChar

digit' :: Parser Int
digit' = guard' (readMaybe . (:[])) anyChar

instance Functor Parser where
  fmap f p = Parser $ fmap (first f) . runParser p

instance Applicative Parser where
  pure a = Parser $ \ s -> [(a,s)]
  (<*>)  = ap

instance Monad Parser where
  return  = pure
  p >>= f = Parser $ \ s -> runParser p s >>= \ (a, s') -> runParser (f a) s'

instance Alternative Parser where
  empty :: Parser a
  empty = Parser (const [])

  (<|>) :: Parser a -> Parser a -> Parser a
  p <|> q = Parser $ \ s -> runParser p s ++ runParser q s

some :: Parser a -> Parser [a]
some p = (:) <$> p <*> many p

many :: Parser a -> Parser [a]
many p = some p <|> pure []


data Expr = Literal Int | Plus Expr Expr
  deriving (Show)

char :: Char -> Parser Char
char c = guard (c ==) anyChar

int :: Parser Int
int = convert <$> some digit' where
  convert ds = sum $ zipWith (\ d e -> d * 10 ^ e) (reverse ds) [0..]

expr :: Parser Expr
expr = Literal <$> int <|> Plus <$> expr <* char '+' <*> expr

expr' :: Parser Expr
expr' = base <|> Plus <$> base <* char '+' <*> expr'
    where base = Literal <$> int <|> char '(' *> expr' <* char ')'

