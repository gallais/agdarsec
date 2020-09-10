{-# OPTIONS --without-K --safe #-}

module Level.Bounded where

open import Level using (Level; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong₂)

record _≤l_ (a l : Level) : Set where
  field proof : l Level.⊔ a ≡ l
open _≤l_ public

record Level≤ (l : Level) : Set where
  field level     : Level
        {{bound}} : level ≤l l
open Level≤ public

infixl 6 _⊔_
_⊔_ : ∀ {l₁ l₂} (a : Level≤ l₁) (b : Level≤ l₂) → Level≤ (l₁ Level.⊔ l₂)
a ⊔ b = record
  { level = level a Level.⊔ level b
  ; bound = record { proof = cong₂ Level._⊔_ (proof (bound a)) (proof (bound b)) }
  }

BSet : ∀ {l} (a : Level≤ l) → Set (suc (level a))
BSet a = Set (level a)

Lift : ∀ l {a} {{la : a ≤l l}} → Set a → Set l
Lift l {a} {{la}} = cast (proof la) module Lift where

  cast : ∀ {b} → l Level.⊔ a ≡ b → Set a → Set b
  cast refl = Level.Lift l

lift : ∀ {l a} {{la : a ≤l l}} {A : Set a} → A → Lift l A
lift {l} {a} {{la}} {A} = uncast (proof la) where

  uncast : ∀ {b} (eq : l Level.⊔ a ≡ b) → A → Lift.cast l eq A
  uncast refl = Level.lift

lower : ∀ {l a} {{la : a ≤l l}} {A : Set a} → Lift l A → A
lower {l} {a} {{la}} {A} = uncast (proof la) where

  uncast : ∀ {b} (eq : l Level.⊔ a ≡ b) → Lift.cast l eq A → A
  uncast refl = Level.lower

map : ∀ {l a b} {{la : a ≤l l}} {{lb : b ≤l l}} {A : Set a} {B : Set b} →
      (A → B) → Lift l A → Lift l B
map f a = lift (f (lower a))


-- Sometimes we want things to be solved automatically.
-- Problem is: we can't declare too many of this or we will have overlapping
-- solutions...

instance
  z≤n : ∀ {a} → zero ≤l a
  z≤n .proof = refl
