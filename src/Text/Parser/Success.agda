module Text.Parser.Success where

open import Data.Nat.Base hiding (_^_)
open import Data.Nat.LTE
open import Data.Char.Base
open import Data.Maybe.Base as Maybe hiding (map)
open import Data.Product hiding (map ; ,_)
open import Data.List.Sized.Interface
open import Function
open import Relation.Unary.Indexed

infix 1 _^_,_
record Success (Tok : Set) (Toks : ℕ → Set) (A : Set) (n : ℕ) : Set where
  constructor _^_,_
  field
    value     : A
    {size}    : ℕ
    .small    : size < n
    leftovers : Toks size
open Success

module _ {Tok A B : Set} {Toks : ℕ → Set} where

  map : (A → B) → [ Success Tok Toks A ⟶ Success Tok Toks B ]
  map f (a ^ m≤n , s) = f a ^ m≤n , s

  guardM : (A → Maybe B) → [ Success Tok Toks A ⟶ Maybe ⊚ Success Tok Toks B ]
  guardM f (a ^ m≤n , s) = Maybe.map (_^ m≤n , s) (f a)

module _ {Tok A : Set} {Toks : ℕ → Set} where

  ≤-lift : {m n : ℕ} → .(m ≤ n) → Success Tok Toks A m → Success Tok Toks A n
  ≤-lift m≤n (a ^ p<m , s) = a ^ ≤-trans p<m m≤n , s

  <-lift : {m n : ℕ} → .(m < n) → Success Tok Toks A m → Success Tok Toks A n
  <-lift m<n = ≤-lift (<⇒≤ m<n)

module _ {Tok A B : Set} {Toks : ℕ → Set} where

  and : {n : ℕ} (p : Success Tok Toks A n) → Success Tok Toks B (size p) →
        Success Tok Toks (A × B) n
  and p q = <-lift (small p) (map (value p ,_) q)

module _ {Tok : Set} {Toks : ℕ → Set} {{𝕊 : Sized Tok Toks}} where

  view : [ Toks ⟶ Maybe ∘ Success Tok Toks Tok ]
  view {zero}   ts = nothing
  view {suc n}  ts = just (let (t , ts) = Sized.view 𝕊 ts in t ^ ≤-refl , ts)
