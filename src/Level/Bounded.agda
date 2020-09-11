{-# OPTIONS --without-K --safe --overlapping-instances #-}

module Level.Bounded where

open import Level using (Level; Setω)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong₂)

_≤l_ : (a l : Level) → Set
a ≤l l = l Level.⊔ a ≡ l

record Level≤ (l : Level) : Set where
  field level : Level
        bound : level ≤l l
open Level≤ public

BSet : ∀ {l} (a : Level≤ l) → Set (Level.suc (level a))
BSet a = Set (level a)

record Set≤ (l : Level) : Setω where
  field level≤ : Level≤ l
        theSet : BSet level≤
open Set≤ public

zero : ∀ {l} → Level≤ l
level zero = Level.zero
bound zero = refl

infixl 6 _⊔_
_⊔_ : ∀ {l₁ l₂} (a : Level≤ l₁) (b : Level≤ l₂) → Level≤ (l₁ Level.⊔ l₂)
a ⊔ b = record
  { level = level a Level.⊔ level b
  ; bound = cong₂ Level._⊔_ (Level≤.bound a) (Level≤.bound b)
  }

[_] : Set → ∀ {l} → Set≤ l
level≤ [ A ] = zero
theSet [ A ] = A

import Data.Unit.Base as Unit

⊤ : ∀ {l} → Set≤ l
⊤ = [ Unit.⊤ ]

infixr 0 _⟶_
_⟶_ : ∀ {l} (A B : Set≤ l) → Set≤ l
level≤ (A ⟶ B) = level≤ A ⊔ level≤ B
theSet (A ⟶ B) = theSet A → theSet B

import Data.Product as Product

infixr 2 _×_
_×_ : ∀ {l} (A B : Set≤ l) → Set≤ l
level≤ (A × B) = level≤ A ⊔ level≤ B
theSet (A × B) = theSet A Product.× theSet B

import Data.Sum.Base as Sum

infixr 1 _⊎_
_⊎_ : ∀ {l} (A B : Set≤ l) → Set≤ l
level≤ (A ⊎ B) = level≤ A ⊔ level≤ B
theSet (A ⊎ B) = theSet A Sum.⊎ theSet B

import Data.Maybe.Base as Maybe

Maybe : ∀ {l} → Set≤ l → Set≤ l
level≤ (Maybe A) = level≤ A
theSet (Maybe A) = Maybe.Maybe (theSet A)

import Data.List.Base as List

List : ∀ {l} → Set≤ l → Set≤ l
level≤ (List A) = level≤ A
theSet (List A) = List.List (theSet A)

open import Data.Nat.Base using (ℕ)
import Data.Vec.Base as Vec

Vec : ∀ {l} → Set≤ l → ℕ → Set≤ l
level≤ (Vec A n) = level≤ A
theSet (Vec A n) = Vec.Vec (theSet A) n

import Data.List.NonEmpty as List⁺

List⁺ : ∀ {l} → Set≤ l → Set≤ l
level≤ (List⁺ A) = level≤ A
theSet (List⁺ A) = List⁺.List⁺ (theSet A)

Lift : ∀ {l} → Set≤ l → Set l
Lift {l} A = cast (bound (level≤ A)) (theSet A) module Lift where

  cast : ∀ {b} → l Level.⊔ (level (level≤ A)) ≡ b →
         Set (level (level≤ A)) → Set b
  cast refl = Level.Lift l

lift : ∀ {l} {A : Set≤ l} → theSet A → Lift A
lift {l} {A} = cast (bound (level≤ A)) where

  cast : ∀ {b} (eq : l Level.⊔ (level (level≤ A)) ≡ b) →
         theSet A → Lift.cast A eq (theSet A)
  cast refl = Level.lift

lower : ∀ {l} {A : Set≤ l} → Lift A → theSet A
lower {l} {A} = cast (bound (level≤ A)) where

  cast : ∀ {b} (eq : l Level.⊔ (level (level≤ A)) ≡ b) →
         Lift.cast A eq (theSet A) → theSet A
  cast refl = Level.lower

map : ∀ {l} {A B : Set≤ l} → (theSet A → theSet B) → Lift A → Lift B
map f a = lift (f (lower a))
