{-# OPTIONS --without-K --safe #-}

module Data.Subset where

open import Level using (Level)

private
  variable
    l : Level

record Subset {l} (A B : Set l) : Set l where
  field into : A → B
open Subset public

open import Data.List.Base using (List; []; _∷_)
open import Data.Char.Base using (Char)
open import Data.String.Base using (String; fromList)

instance

  Subset-list : {A : Set l} → Subset A (List A)
  Subset-list .into a = a ∷ []

  Subset-chars : Subset Char String
  Subset-chars .into c = fromList (c ∷ [])

  Subset-refl : {A : Set l} → Subset A A
  Subset-refl .into x = x
