module Data.Text.Sized where

open import Level using (Level)
open import Level.Bounded using ([_]; lower; lift)
open import Data.Empty.Irrelevant
open import Data.Unit
open import Data.Nat.Base
import Data.Nat.Properties as ℕₚ
open import Data.Char.Base
open import Data.String.Base using (String; length; uncons)
open import Data.String.Unsafe
open import Data.Maybe.Base
open import Data.Product
open import Data.List.Sized.Interface
open import Function.Base using (_$_; _∘′_; case_of_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)

private
  variable l : Level

record Text (n : ℕ) : Set where
  constructor mkTest
  field
    value  : String
    .proof : length value ≡ n
open Text

record Split (n : ℕ) (str : String) : Set where
  constructor mkSplit
  field
    head   : Char
    tail   : String
    .size  : length tail ≡ n
    .proof : uncons str ≡ just (head , tail)

length-uncons : ∀ str {mcs} → uncons str ≡ mcs →
                length str ≡ maybe′ (suc ∘′ length ∘′ proj₂) zero mcs
length-uncons str eq with uncons str | length-tail str
length-uncons str refl | nothing | p = p
length-uncons str refl | just _  | p = p

split : ∀ str {n} → .(_ : length str ≡ suc n) → Split n str
split str {n} lgth with uncons str in eq
... | just (c , s) = mkSplit c s (prf lgth) eq where

  .prf : length str ≡  suc n → length s ≡ n
  prf lgth = ℕₚ.suc-injective $ begin
    suc (length s) ≡˘⟨ length-uncons str eq ⟩
    length str     ≡⟨ lgth ⟩
    suc n          ∎ where open Eq.≡-Reasoning

... | nothing      = ⊥-elim (case prf lgth of λ ()) where

  .prf : length str ≡ suc n → 0 ≡ suc n
  prf lgth = begin
    0          ≡˘⟨ length-uncons str eq ⟩
    length str ≡⟨ lgth ⟩
    suc n      ∎ where open Eq.≡-Reasoning

instance

  text : Sized {l} [ Char ] (λ n → [ Text n ])
  Sized.view text {zero}  t = _
  Sized.view text {suc n} (Level.lift (mkTest val prf)) =
    let (mkSplit hd tl prf _) = split val prf in
    lift (hd , mkTest tl prf)
