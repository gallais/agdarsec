module Data.Text.Sized where

open import Data.Empty
open import Data.Unit
open import Data.Nat.Base
open import Data.Char.Base
open import Data.String.Base hiding (length)
open import Data.List.Base hiding (uncons)
open import Data.Maybe.Base
open import Data.Pair
open import Data.Product
open import Data.Text
open import Data.List.Sized.Interface
open import Relation.Binary.PropositionalEquality
open import Function

open ≡-Reasoning

record Text (n : ℕ) : Set where
  field  value  : String
         .proof : length (toList value) ≡ n

⊥-irrelim : ∀ {ℓ} {A : Set ℓ} → .⊥ → A
⊥-irrelim ()

instance

  text : Sized Char Text
  Sized.view text {zero}  _  = _
  Sized.view text {suc n} t with uncons (Text.value t) | uncons-list (Text.value t)
  ... | just (c , s)  | eq = c , record { value = s
                                        ; proof = pr } where

    .pr : length (toList s) ≡ n
    pr = cong pred $ begin
          length (c ∷ toList s)           ≡⟨ cong length (sym eq) ⟩
          length (toList (Text.value t))  ≡⟨ Text.proof t ⟩
          suc n
         ∎

  ... | nothing       | eq = ⊥-irrelim (case pr of λ ()) where

    .pr : 0 ≡ suc n
    pr = begin
           0                               ≡⟨ cong length (sym eq) ⟩
           length (toList (Text.value t))  ≡⟨ Text.proof t ⟩
           suc n
         ∎
