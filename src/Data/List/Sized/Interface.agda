{-# OPTIONS --without-K --safe #-}

module Data.List.Sized.Interface where

open import Level
open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Data.Unit
open import Data.Product
open import Relation.Unary

module _ {a as : Level} (A : Set a) (As : ℕ → Set as) where

 View : ℕ → Set (a ⊔ as)
 View zero    = Lift _ ⊤
 View (suc n) = A × As n

 record Sized : Set (a ⊔ as) where
   field view : ∀[ As ⇒ View ]

open import Data.Vec

instance

  vec : ∀ {ℓ} {A : Set ℓ} → Sized A (Vec A)
  Sized.view     vec []       = lift tt
  Sized.view     vec (x ∷ xs) = x , xs

open import Data.Vec.Recursive

instance

  sized-nary : ∀ {ℓ} {A : Set ℓ} → Sized A (A ^_)
  Sized.view sized-nary {0}    xs = Level.lift tt
  Sized.view sized-nary {1}    x  = x , Level.lift tt
  Sized.view sized-nary {2+ n} xs = xs
