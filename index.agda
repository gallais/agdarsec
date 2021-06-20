{-# OPTIONS --guardedness #-}

module index where

-- The core design decisions behind agdarsec are detailed in
-- https://gallais.github.io/pdf/agdarsec18.pdf

-- We have a simplified frontend with ready made default choices:

import Text.Parser

-- Otherwise you probably want to start with the main types:

import Text.Parser.Types

-- You can see the parser combinators themselves in:

import Text.Parser.Combinators
import Text.Parser.Combinators.Numbers
import Text.Parser.Combinators.Char

-- We have some ready-to-use monads for parsing in:

import Text.Parser.Monad

-- We have a small lexer library

import Text.Lexer

-- We have some fully worked-out in:

import Expr
import STLC
import Parentheses
import RegExp
import NList
import SExp

-- And even a parser returning a large type

import Large

-- The key ideas behind the implementation details are largely contained in

import Induction.Nat.Strong
import Text.Parser.Success
