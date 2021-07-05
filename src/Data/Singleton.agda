{-# OPTIONS --without-K --safe #-}

module Data.Singleton where

open import Level using (Level)
open import Data.Empty.Polymorphic using (⊥)
open import Data.Maybe.Base using (Maybe; nothing; just)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)

private
  variable
    a b : Level
    A : Set a
    B : Set b

infix 0 _!
data Singleton {A : Set a} : A → Set a where
  _! : (a : A) → Singleton a

fromJust : Maybe {a} A → Set a
fromJust (just a) = Singleton a
fromJust nothing  = ⊥

fromInj₁ : {A : Set a} → A ⊎ B → Set a
fromInj₁ (inj₁ a) = Singleton a
fromInj₁ (inj₂ _) = ⊥

fromInj₂ : {B : Set b} → A ⊎ B → Set b
fromInj₂ (inj₁ _) = ⊥
fromInj₂ (inj₂ b) = Singleton b
