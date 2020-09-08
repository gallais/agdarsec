{-# OPTIONS --without-K --safe #-}

module Text.Parser.Success where

open import Level using (Level)
open import Data.Nat.Base using (ℕ; zero; suc; _≤_; _<_)
open import Data.Nat.Properties using (≤-trans; <⇒≤; ≤-refl)
open import Data.Maybe.Base as Maybe using (Maybe; nothing; just)
open import Data.Product using (_×_; _,_)
open import Data.List.Sized.Interface using (Sized)
open import Function.Base using (_∘′_)
open import Relation.Unary using (IUniversal; _⇒_)

open import Text.Parser.Types
open Success

variable
  l : Level
  A B Tok : Set l
  Toks : ℕ → Set l
  m n : ℕ

map : (A → B) → ∀[ Success Toks A ⇒ Success Toks B ]
map f (a ^ m≤n , s) = f a ^ m≤n , s

guardM : (A → Maybe B) → ∀[ Success Toks A ⇒ Maybe ∘′ Success Toks B ]
guardM f (a ^ m≤n , s) = Maybe.map (_^ m≤n , s) (f a)

≤-lift : .(le : m ≤ n) → Success Toks A m → Success Toks A n
≤-lift m≤n (a ^ p<m , s) = a ^ ≤-trans p<m m≤n , s

<-lift : .(le : m < n) → Success Toks A m → Success Toks A n
<-lift m<n = ≤-lift (<⇒≤ m<n)

and : (p : Success Toks A n) → Success Toks B (size p) →
      Success Toks (A × B) n
and (a ^ m<n , v) q = <-lift m<n (map (a ,_) q)

module _ {{𝕊 : Sized Tok Toks}} where

  view : ∀[ Toks ⇒ Maybe ∘′ Success Toks Tok ]
  view {zero}   ts = nothing
  view {suc n}  ts = just (let (t , ts) = Sized.view 𝕊 ts in t ^ ≤-refl , ts)
