{-# OPTIONS --without-K --safe #-}

module Data.List.Sized.Interface where

open import Level.Bounded
open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Data.Product using (_,_)
open import Function.Base using (case_of_)
open import Relation.Unary

module _ {l} (A : Set≤ l) (As : ℕ → Set≤ l) where

 View : ℕ → Set l
 View zero    = Lift ⊤
 View (suc n) = Lift (A × As n)

 record Sized : Set l where
   field view : ∀ {n} → Lift (As n) → View n

open import Data.Vec.Base using ([]; _∷_)

instance

  vec : ∀ {l} {A : Set≤ l} → Sized A (Vec A)
  Sized.view vec xs = case lower xs of λ where
    []       → lift _
    (x ∷ xs) → lift (x , xs)
