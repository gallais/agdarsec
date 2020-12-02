{-# OPTIONS --without-K --safe #-}

open import Text.Parser.Types.Core using (Parameters)

module Text.Parser.Success {l} (P : Parameters l) where

open import Level.Bounded as Level≤ using (Set≤; _×_; theSet; lift; lower)
open import Data.Nat.Base using (ℕ; zero; suc; _≤_; _<_)
open import Data.Nat.Properties using (≤-trans; <⇒≤; ≤-refl)
open import Data.Maybe.Base as Maybe using (Maybe; nothing; just)
open import Data.Product using (_,_)
open import Data.List.Sized.Interface using (Sized)
open import Function.Base using (_∘′_; _$_)
open import Relation.Unary using (IUniversal; _⇒_)

open Text.Parser.Types.Core
open import Text.Parser.Types P
open Parameters P
open Success

module _ {A B : Set≤ l} where

  map : (theSet A → theSet B) → ∀[ Success Toks A ⇒ Success Toks B ]
  map f (a ^ m≤n , s) = Level≤.map f a ^ m≤n , s

  guardM : (theSet A → Maybe (theSet B)) →
           ∀[ Success Toks A ⇒ Maybe ∘′ Success Toks B ]
  guardM f (a ^ m≤n , s) = Maybe.map ((_^ m≤n , s) ∘′ lift) (f (lower a))

module _ {A : Set≤ l} {m n : ℕ} where

  ≤-lift : .(le : m ≤ n) → Success Toks A m → Success Toks A n
  ≤-lift m≤n (a ^ p<m , s) = a ^ ≤-trans p<m m≤n , s

  <-lift : .(le : m < n) → Success Toks A m → Success Toks A n
  <-lift m<n = ≤-lift (<⇒≤ m<n)

module _ {A B : Set≤ l} where

  and : ∀ {n} (p : Success Toks A n) → Success Toks B (size p) →
        Success Toks (A × B) n
  and (a ^ m<n , v) q = <-lift m<n (map (lower a ,_) q)

module _ {{𝕊 : Sized Tok Toks}} where

  view : ∀ {n} → theSet (Toks n) → Maybe (Success Toks Tok n)
  view {zero}   ts = nothing
  view {suc n}  ts = just $ let (t , ts) = lower (Sized.view 𝕊 (lift ts))
                            in lift t ^ ≤-refl , lift ts
