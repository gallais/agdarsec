module Level.Bounded where

open import Level using (Level; zero; suc; _⊔_)
open import Agda.Builtin.Equality using (_≡_; refl)

record _≤l_ (a l : Level) : Set where
  field proof : l ⊔ a ≡ l
open _≤l_ public

instance
  z≤n : ∀ {a} → zero ≤l a
  z≤n .proof = refl

record Level≤ (l : Level) : Set where
  field level     : Level
        {{bound}} : level ≤l l
open Level≤ public

BSet : ∀ {l} (a : Level≤ l) → Set (suc (level a))
BSet a = Set (level a)

Lift : ∀ l {a} {{la : a ≤l l}} → Set a → Set l
Lift l {a} {{la}} = cast (proof la) module Lift where

  cast : ∀ {b} → l ⊔ a ≡ b → Set a → Set b
  cast refl = Level.Lift l

lift : ∀ {l a} {{la : a ≤l l}} {A : Set a} → A → Lift l A
lift {l} {a} {{la}} {A} = uncast (proof la) where

  uncast : ∀ {b} (eq : l ⊔ a ≡ b) → A → Lift.cast l eq A
  uncast refl = Level.lift

lower : ∀ {l a} {{la : a ≤l l}} {A : Set a} → Lift l A → A
lower {l} {a} {{la}} {A} = uncast (proof la) where

  uncast : ∀ {b} (eq : l ⊔ a ≡ b) → Lift.cast l eq A → A
  uncast refl = Level.lower

map : ∀ {l a b} {{la : a ≤l l}} {{lb : b ≤l l}} {A : Set a} {B : Set b} →
      (A → B) → Lift l A → Lift l B
map f a = lift (f (lower a))
