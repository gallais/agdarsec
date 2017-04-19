module Relation.Unary.Indexed where

open import Level
open import Data.Sum
open import Data.Product

module _ {ℓ ℓ′ ℓ^I : Level} {I : Set ℓ^I} where

 infixr 1 _⟶_
 _⟶_ : (I → Set ℓ) → (I → Set ℓ′) → (I → Set (ℓ′ ⊔ ℓ))
 (A ⟶ B) n = A n → B n

 infixr 2 _⊕_
 _⊕_ : (I → Set ℓ) → (I → Set ℓ′) → (I → Set (ℓ′ ⊔ ℓ))
 (A ⊕ B) n = A n ⊎ B n

 infixr 3 _⊗_
 _⊗_ : (I → Set ℓ) → (I → Set ℓ′) → (I → Set (ℓ′ ⊔ ℓ))
 (A ⊗ B) n = A n × B n


module _ {ℓ ℓ^I : Level} {I : Set ℓ^I} where
 infix 5 [_]
 [_] : (A : I → Set ℓ) → Set (ℓ^I ⊔ ℓ)
 [ A ] = ∀ {n} → A n
