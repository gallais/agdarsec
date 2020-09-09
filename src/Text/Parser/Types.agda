{-# OPTIONS --without-K --safe #-}

module Text.Parser.Types where

open import Level using (Level; suc; Lift)
open import Data.Unit.Base using (⊤)
open import Data.Nat.Base using (ℕ; _<_; _≤_)

private
  variable
    l : Level

--------------------------------------------------------------------------------
-- PARAMETERS

-- A parser is parametrised by some types, type constructors and one function.

record Parameters (l : Level) : Set (suc l) where
   field
-- Token-related parameters:
-- * Tok: tokens
-- * Toks: sized input (~ Vec Tok)
     Tok         : Set l
     Toks        : ℕ → Set l
-- The monad stack used
     M           : Set l → Set l
-- The action allowing us to track consumed tokens
     recordToken : Tok → M (Lift l ⊤)

--------------------------------------------------------------------------------
-- SUCCESS

-- A successful partial parse of an A is a value A together leftovers
-- which are proven to be smaller than the input

infix 1 _^_,_
record Success (Toks : ℕ → Set l) (A : Set l) (n : ℕ) : Set l where
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

record Parser (P : Parameters l) (A : Set l) (n : ℕ) : Set l where
  constructor mkParser
  open Parameters P
  field runParser : ∀ {m} → .(m ≤ n) → Toks m → M (Success Toks A m)
open Parser public
