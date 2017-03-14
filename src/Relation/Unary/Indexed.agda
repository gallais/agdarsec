module Relation.Unary.Indexed where

open import Data.Sum
open import Data.Product

module _ {I : Set} where

 infixr 1 _⟶_
 _⟶_ : (A B : I → Set) → (I → Set)
 (A ⟶ B) n = A n → B n

 infixr 2 _⊕_
 _⊕_ : (A B : I → Set) → (I → Set)
 (A ⊕ B) n = A n ⊎ B n

 infixr 3 _⊗_
 _⊗_ : (A B : I → Set) → (I → Set)
 (A ⊗ B) n = A n × B n

 infix 5 [_]
 [_] : (A : I → Set) → Set
 [ A ] = ∀ {n} → A n
