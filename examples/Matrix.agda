module Matrix where

open import Data.Maybe.Base as Maybe
open import Data.Nat.Base
open import Data.Product as Product
open import Data.Sum.Base
open import Data.Vec.Base as Vec using (Vec; _∷_; [])
open import Function.Base
open import Relation.Nullary

open import Text.Parser

Matrix : Set → ℕ → ℕ → Set
Matrix a m n = Vec (Vec a n) m

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

indices : ∀[ Parser ((Σ[ m ∈ ℕ ] Σ[ n ∈ ℕ ] (m ≡ 0 ⊎ n ≡ 0))
                   ⊎ (Σ[ m ∈ ℕ ] Σ[ n ∈ ℕ ] (NonZero m × NonZero n))) ]
indices = f <$> (decimalℕ <& box space <&> box decimalℕ) where

  f : ℕ × ℕ → (Σ[ m ∈ ℕ ] Σ[ n ∈ ℕ ] (m ≡ 0 ⊎ n ≡ 0))
            ⊎ (Σ[ m ∈ ℕ ] Σ[ n ∈ ℕ ] (NonZero m × NonZero n))
  f (zero , n) = inj₁ (zero , n , inj₁ refl)
  f (m , zero) = inj₁ (m , zero , inj₂ refl)
  f (suc m , suc n) = inj₂ (suc m , suc n , _)

matrix : ∀[ Parser (Σ[ m ∈ ℕ ] Σ[ n ∈ ℕ ] Matrix ℕ m n) ]
matrix = <[ ((λ (m , n , p) → [ (λ _ → 0 , n , []) , (λ _ → m , 0 , Vec.replicate []) ] p))
          , (λ (m , n , p , q) → box $ (m ,_) ∘ (n ,_) <$> replicate m {{p}} (replicate n {{q}} (space &> box decimalℕ)))
          ]> indices

_ : "2 2 1 2 3 4" ∈ matrix
_ = 2 , 2
  , (1 ∷ 2 ∷ [])
  ∷ (3 ∷ 4 ∷ [])
  ∷ [] !

_ : "1 3 1 2 3" ∈ matrix
_ = 1 , 3
  , (1 ∷ 2 ∷ 3 ∷ [])
  ∷ [] !

_ : "3 1 1 2 3" ∈ matrix
_ = 3 , 1
  , (1 ∷ [])
  ∷ (2 ∷ [])
  ∷ (3 ∷ [])
  ∷ [] !

_ : "0 3" ∈ matrix
_ = 0 , 3 , [] !

_ : "3 0" ∈ matrix
_ = 3 , 0 , [] ∷ [] ∷ [] ∷ [] !
