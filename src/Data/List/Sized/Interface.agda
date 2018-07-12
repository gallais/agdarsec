module Data.List.Sized.Interface where

open import Level
open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Data.Unit
open import Data.Product
open import Relation.Unary.Indexed

module _ {a : Level} (A : Set a) (As : ℕ → Set a) where

 View : ℕ → Set a
 View zero    = Lift ⊤
 View (suc n) = A × As n

 record Sized : Set a where
   field view : [ As ⟶ View ]

open import Data.Vec

instance

  vec : ∀ {ℓ} {A : Set ℓ} → Sized A (Vec A)
  Sized.view     vec []       = lift tt
  Sized.view     vec (x ∷ xs) = x , xs

open import Data.Product.N-ary

instance

  sized-nary : ∀ {ℓ} {A : Set ℓ} → Sized A (A ^_)
  Sized.view sized-nary {0}    xs = Level.lift tt
  Sized.view sized-nary {1}    x  = x , Level.lift tt
  Sized.view sized-nary {2+ n} xs = xs
