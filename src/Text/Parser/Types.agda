{-# OPTIONS --without-K --safe #-}

module Text.Parser.Types where

open import Level using (suc; _⊔_)
open import Level.Bounded using (Level≤; BSet; level; Lift)
open import Data.Unit.Base using (⊤)
open import Data.Nat.Base using (ℕ; _<_; _≤_)
open import Function.Base using (_∘′_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

--------------------------------------------------------------------------------
-- PARAMETERS

-- A parser is parametrised by some types, type constructors and one function.

record Parameters l (lTok lToks : Level≤ l)
       : Set (suc (l ⊔ level lTok ⊔ level lToks))
       where
   field
-- Token-related parameters:
-- * Tok: tokens
-- * Toks: sized input (~ Vec Tok)
     Tok         : Set (level lTok)
     Toks        : ℕ → Set (level lToks)
-- The monad stack used
     M           : Set l → Set l
-- The action allowing us to track consumed tokens
     recordToken : Tok → M (Lift l ⊤)

--------------------------------------------------------------------------------
-- SUCCESS

-- A successful partial parse of an A is a value A together leftovers
-- which are proven to be smaller than the input

infix 1 _^_,_
record Success {l} (lToks : Level≤ l) (Toks : ℕ → BSet lToks)
                   (la : Level≤ l) (A : BSet la) (n : ℕ) : Set l where
  constructor _^_,_
  field
    value     : Lift l A
    {size}    : ℕ
    .small    : size < n
    leftovers : Lift l (Toks size)

--------------------------------------------------------------------------------
-- PARSER

-- A parser is the ability to, given an input, return a computation for
-- a success.

record Parser {l lTok lToks} (P : Parameters l lTok lToks)
              {la : Level≤ l} (A : BSet la) (n : ℕ) : Set l where
  constructor mkParser
  open Parameters P
  field runParser : ∀ {m} → .(m ≤ n) → Lift l (Toks m) → M (Success lToks Toks la A m)
open Parser public
