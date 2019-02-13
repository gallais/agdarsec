{-# OPTIONS --without-K --safe #-}

module Text.Parser.Types where

open import Data.Unit using (⊤)
open import Data.Nat

--------------------------------------------------------------------------------
-- PARAMETERS

-- A parser is parametrised by some types, type constructors and one function.

record Parameters : Set₁ where
   field
-- Token-related parameters:
-- * Tok: tokens
-- * Toks: sized input (~ Vec Tok)
     Tok         : Set
     Toks        : ℕ → Set
-- The monad stack used
     M           : Set → Set
-- The action allowing us to track consumed tokens
     recordToken : Tok → M ⊤

--------------------------------------------------------------------------------
-- SUCCESS

-- A successful partial parse of an A is a value A together leftovers
-- which are proven to be smaller than the input

infix 1 _^_,_
record Success (Toks : ℕ → Set) (A : Set) (n : ℕ) : Set where
  constructor _^_,_
  field
    value     : A
    {size}    : ℕ
    .small    : size < n
    leftovers : Toks size

--------------------------------------------------------------------------------
-- PARSER

-- A parser is the ability to, given an input, return a computation for
-- a success.

record Parser (P : Parameters) (A : Set) (n : ℕ) : Set where
  constructor mkParser
  open Parameters P
  field runParser : ∀ {m} → .(m ≤ n) → Toks m → M (Success Toks A m)
open Parser public
