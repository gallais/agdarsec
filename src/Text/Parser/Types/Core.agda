{-# OPTIONS --without-K --safe #-}

module Text.Parser.Types.Core where

open import Level using (Level; Setω)
open import Level.Bounded using (Set≤; theSet; Lift; ⊤)
open import Data.Nat.Base using (ℕ; _<_)

--------------------------------------------------------------------------------
-- PARAMETERS

-- A parser is parametrised by some types, type constructors and one function.

record Parameters (l : Level) : Setω where
   field
-- Token-related parameters:
-- * Tok: tokens
     Tok    : Set≤ l
-- * Toks: sized input (~ Vec Tok)
     Toks    : ℕ → Set≤ l
-- The monad stack used
     M : Set l → Set l
-- The action allowing us to track consumed tokens
     recordToken : theSet Tok → M (Lift ⊤)

--------------------------------------------------------------------------------
-- SUCCESS

-- A successful partial parse of an A is a value A together leftovers
-- which are proven to be smaller than the input

infix 1 _^_,_
record Success {l} (Toks : ℕ → Set≤ l) (A : Set≤ l) (n : ℕ) : Set l where
  constructor _^_,_
  field
    value     : Lift A
    {size}    : ℕ
    .small    : size < n
    leftovers : Lift (Toks size)
