{-# OPTIONS --without-K --safe #-}

module Level.Bounded where

open import Level using (Level; Setω)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong₂)

------------------------------------------------------------------------
-- Bounded levels

_≤l_ : (a l : Level) → Set
a ≤l l = l Level.⊔ a ≡ l

record Level≤ (l : Level) : Set where
  constructor MkLevel≤
  field level     : Level
        {{bound}} : level ≤l l
open Level≤ public

instance
  z≤l : ∀ {l} → Level.zero ≤l l
  z≤l = refl

zero : ∀ {l} → Level≤ l
level zero = Level.zero

infixl 6 _⊔_
_⊔_ : ∀ {l₁ l₂} (a : Level≤ l₁) (b : Level≤ l₂) → Level≤ (l₁ Level.⊔ l₂)
a ⊔ b = record
  { level = level a Level.⊔ level b
  ; bound = cong₂ Level._⊔_ (Level≤.bound a) (Level≤.bound b)
  }

------------------------------------------------------------------------
-- Bounded sets

record Set≤ (l : Level) : Setω where
  field level≤ : Level≤ l
        theSet : Set (level level≤)
open Set≤ public

------------------------------------------------------------------------
-- Type constructors

[_] : Set → ∀ {l} → Set≤ l
level≤ [ A ] = zero
theSet [ A ] = A

import Data.Unit.Base as Unit

⊤ : ∀ {l} → Set≤ l
⊤ = [ Unit.⊤ ]

import Data.Empty as Empty

⊥ : ∀ {l} → Set≤ l
⊥ = [ Empty.⊥ ]

infixr 0 _⟶_
_⟶_ : ∀ {l} (A B : Set≤ l) → Set≤ l
level≤ (A ⟶ B) = level≤ A ⊔ level≤ B
theSet (A ⟶ B) = theSet A → theSet B

import Data.Product as Product

infixr 2 _×_
_×_ : ∀ {l} (A B : Set≤ l) → Set≤ l
level≤ (A × B) = level≤ A ⊔ level≤ B
theSet (A × B) = theSet A Product.× theSet B

-- This type is less than optimal. However we cannot give `B` the type
-- theSet A → Set≤ l
-- because otherwise we would have no guarantee that the level of `B`
-- does not depend on the value of type `theSet A` it is passed.
-- The current definition allows us to write e.g. the following (using `Vec`
-- defined below):
-- List : ∀ {l} → Set≤ l → Set≤ l
-- List A = Σ [ ℕ ] (λ n → theSet (Vec A n))
-- which is not too far off from what we would ideally like to write:
-- List A = Σ [ ℕ ] (Vec A)

Σ : ∀ {l} (A : Set≤ l) {b : Level} {{b≤l : b ≤l l}} (B : theSet A → Set b) → Set≤ l
level≤ (Σ A {b} {{b≤l}} B) = level≤ A ⊔ MkLevel≤ b {{b≤l}}
theSet (Σ A B) = Product.Σ (theSet A) B

import Data.Sum.Base as Sum

infixr 1 _⊎_
_⊎_ : ∀ {l} (A B : Set≤ l) → Set≤ l
level≤ (A ⊎ B) = level≤ A ⊔ level≤ B
theSet (A ⊎ B) = theSet A Sum.⊎ theSet B

infixr 0 _$$_
_$$_ : (∀ {l} → Set l → Set l) → ∀ {l} → Set≤ l → Set≤ l
level≤ (T $$ A) = level≤ A
theSet (T $$ A) = T (theSet A)

import Data.Maybe.Base as Maybe

Maybe : ∀ {l} → Set≤ l → Set≤ l
Maybe = Maybe.Maybe $$_

import Data.List.Base as List

List : ∀ {l} → Set≤ l → Set≤ l
List = List.List $$_

open import Data.Nat.Base using (ℕ)
import Data.Vec.Base as Vec

Vec : ∀ {l} → Set≤ l → ℕ → Set≤ l
Vec A n = (λ A → Vec.Vec A n) $$ A

import Data.List.NonEmpty as List⁺

List⁺ : ∀ {l} → Set≤ l → Set≤ l
List⁺ = List⁺.List⁺ $$_

------------------------------------------------------------------------
-- Going back and forth between `Set≤ l`  and `Set l`

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
