{-# OPTIONS --without-K --safe #-}

module Data.Subset where

open import Level using (Level; _⊔_)

record Subset {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  field into : A → B
open Subset public

open import Data.List.Base using (List; []; _∷_)
open import Data.Char.Base using (Char)
open import Data.String.Base using (String; fromList)

instance

  Subset-list : ∀ {a} {A : Set a} → Subset A (List A)
  Subset-list .into a = a ∷ []

  Subset-chars : Subset Char String
  Subset-chars .into c = fromList (c ∷ [])

  Subset-refl : ∀ {a} {A : Set a} → Subset A A
  Subset-refl .into x = x
