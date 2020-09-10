{-# OPTIONS --without-K --safe #-}

module Text.Parser.Success where

open import Level using (Level)
open import Level.Bounded as Level≤ using (Level≤; _⊔_; BSet; lift; lower)
open import Data.Nat.Base using (ℕ; zero; suc; _≤_; _<_)
open import Data.Nat.Properties using (≤-trans; <⇒≤; ≤-refl)
open import Data.Maybe.Base as Maybe using (Maybe; nothing; just)
open import Data.Product using (_×_; _,_)
open import Data.List.Sized.Interface using (Sized)
open import Function.Base using (_∘′_)
open import Relation.Unary using (IUniversal; _⇒_)

open import Text.Parser.Types
open Success


module _ {l} {la lb lToks : Level≤ l} {Toks : ℕ → BSet lToks} {A : BSet la} {B : BSet lb} where

  map : (A → B) → ∀[ Success lToks Toks la A ⇒ Success lToks Toks lb B ]
  map f (a ^ m≤n , s) = Level≤.map f a ^ m≤n , s

  guardM : (A → Maybe B) → ∀[ Success lToks Toks la A ⇒ Maybe ∘′ Success lToks Toks lb B ]
  guardM f (a ^ m≤n , s) = Maybe.map ((_^ m≤n , s) ∘′ lift) (f (lower a))

module _ {l} {la lToks : Level≤ l} {Toks : ℕ → BSet lToks} {A : BSet la} {m n : ℕ} where

  ≤-lift : .(le : m ≤ n) → Success lToks Toks la A m → Success lToks Toks la A n
  ≤-lift m≤n (a ^ p<m , s) = a ^ ≤-trans p<m m≤n , s

  <-lift : .(le : m < n) → Success lToks Toks la A m → Success lToks Toks la A n
  <-lift m<n = ≤-lift (<⇒≤ m<n)

module _ {l} {la lb lToks : Level≤ l} {Toks : ℕ → BSet lToks} {A : BSet la} {B : BSet lb} where

  and : ∀ {n} (p : Success lToks Toks la A n) → Success lToks Toks lb B (size p) →
        Success lToks Toks (la ⊔ lb) (A × B) n
  and (a ^ m<n , v) q = <-lift m<n (map (lower a ,_) q)

module _ {l} {lTok lToks : Level≤ l} {Tok : BSet lTok} {Toks : ℕ → BSet lToks}
         {{𝕊 : Sized Tok Toks}} where

  view : ∀[ Toks ⇒ Maybe ∘′ Success lToks Toks lTok Tok ]
  view {zero}   ts = nothing
  view {suc n}  ts = just (let (t , ts) = Sized.view 𝕊 ts in lift t ^ ≤-refl , lift ts)
