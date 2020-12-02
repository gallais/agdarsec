{-# OPTIONS --without-K --safe #-}

open import Text.Parser.Types.Core using (Parameters)

module Text.Parser.Types {l} (P : Parameters l) where

open import Level.Bounded
open import Data.Nat.Base using (ℕ; _<_; _≤_)
open import Function.Base using (_∘′_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open Text.Parser.Types.Core using (Success)

--------------------------------------------------------------------------------
-- PARSER

-- A parser is the ability to, given an input, return a computation for
-- a success.

record Parser (A : Set≤ l) (n : ℕ) : Set l where
  constructor mkParser
  open Parameters P
  field runParser : ∀ {m} → .(m ≤ n) → Lift (Toks m) → M (Success Toks A m)
open Parser public
