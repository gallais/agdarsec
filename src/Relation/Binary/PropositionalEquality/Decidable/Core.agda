{-# OPTIONS --without-K --safe #-}

module Relation.Binary.PropositionalEquality.Decidable.Core where

open import Relation.Binary
open import Relation.Binary.PropositionalEquality.Core

record DecidableEquality {a} (A : Set a) : Set a where
  field decide : Decidable {A = A} _≡_
open DecidableEquality public

open import Data.Unit as U using (⊤)
open import Data.Nat as ℕ using (ℕ)

instance

  decide-unit : DecidableEquality ⊤
  decide-unit .decide = U._≟_

  decide-nat : DecidableEquality ℕ
  decide-nat .decide = ℕ._≟_
