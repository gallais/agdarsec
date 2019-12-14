{-# OPTIONS --without-K --safe #-}

module Text.Parser.Success where

open import Data.Nat.Base hiding (_^_)
open import Data.Nat.Properties
open import Data.Char.Base hiding (_<_)
open import Data.Maybe.Base as Maybe hiding (map)
open import Data.Product hiding (map)
open import Data.List.Sized.Interface
open import Function
open import Relation.Unary

open import Text.Parser.Types
open Success

module _ {A B : Set} {Toks : ℕ → Set} where

  map : (A → B) → ∀[ Success Toks A ⇒ Success Toks B ]
  map f (a ^ m≤n , s) = f a ^ m≤n , s

  guardM : (A → Maybe B) → ∀[ Success Toks A ⇒ Maybe ∘′ Success Toks B ]
  guardM f (a ^ m≤n , s) = Maybe.map (_^ m≤n , s) (f a)

module _ {A : Set} {Toks : ℕ → Set} where

  ≤-lift : {m n : ℕ} → .(le : m ≤ n) → Success Toks A m → Success Toks A n
  ≤-lift m≤n (a ^ p<m , s) = a ^ ≤-trans p<m m≤n , s

  <-lift : {m n : ℕ} → .(le : m < n) → Success Toks A m → Success Toks A n
  <-lift m<n = ≤-lift (<⇒≤ m<n)

module _ {A B : Set} {Toks : ℕ → Set} where

  and : {n : ℕ} (p : Success Toks A n) → Success Toks B (size p) →
        Success Toks (A × B) n
  and (a ^ m<n , v) q = <-lift m<n (map (a ,_) q)

module _ {Tok : Set} {Toks : ℕ → Set} {{𝕊 : Sized Tok Toks}} where

  view : ∀[ Toks ⇒ Maybe ∘ Success Toks Tok ]
  view {zero}   ts = nothing
  view {suc n}  ts = just (let (t , ts) = Sized.view 𝕊 ts in t ^ ≤-refl , ts)
