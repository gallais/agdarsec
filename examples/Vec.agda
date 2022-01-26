module Vec where

open import Text.Parser
open import Data.Vec hiding (replicate)
open import Data.Maybe
open import Data.Nat
open import Data.Product

n-times : {A : Set} → ∀[ Parser A ⇒ Parser (∃[ n ] Vec A (suc n)) ]
n-times p = decimalℕ &>>= λ n → box (replicate (suc n) p)

n-times? : {A : Set} → ∀[ Parser A ⇒ Parser (∃[ n ] Maybe (Vec A (suc n))) ]
n-times? p = decimalℕ &?>>= λ n → box (replicate (suc n) p)

space-ℕ : ∀[ Parser ℕ ]
space-ℕ = space &> box decimalℕ

_ : "0 0" ∈ n-times space-ℕ
_ = 0 , 0 ∷ [] !

_ : "1 0 1" ∈ n-times space-ℕ
_ = 1 , 0 ∷ 1 ∷ [] !

_ : "1 0 1" ∈ n-times? space-ℕ
_ = 1 , just (0 ∷ 1 ∷ []) !

_ : "1" ∈ n-times? space-ℕ
_ = 1 , nothing !

_ : "1 1" ∉ n-times? space-ℕ
_ = _

_ : "1 1" ∈ (n-times? space-ℕ <& box space-ℕ)
_ = 1 , nothing !
