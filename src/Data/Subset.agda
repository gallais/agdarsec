{-# OPTIONS --without-K --safe #-}

module Data.Subset where

record Subset (A B : Set) : Set where
  field into : A → B
open Subset public

open import Data.List
open import Data.Char
open import Data.String

instance

  Subset-list : ∀ {A} → Subset A (List A)
  Subset-list .into a = a ∷ []

  Subset-chars : Subset Char String
  Subset-chars .into c = fromList (c ∷ [])

  Subset-refl : ∀ {A} → Subset A A
  Subset-refl .into x = x
