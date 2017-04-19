module Data.List.Sized.Interface where

open import Level
open import Data.Nat
open import Data.Unit
open import Data.Product

module _ {ℓ : Level} where

 View : ℕ → Set ℓ → (ℕ → Set ℓ) → Set ℓ
 View zero     A As = Lift ⊤
 View (suc n)  A As = A × As n

 record Sized (A : Set ℓ) (V : ℕ → Set ℓ) : Set ℓ where
   field view : {n : ℕ} → V n → View n A V

open import Data.Vec

instance

  vec : ∀ {ℓ} {A : Set ℓ} → Sized A (Vec A)
  Sized.view vec []       = lift tt
  Sized.view vec (x ∷ xs) = x , xs
