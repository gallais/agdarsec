module Relation.Binary.PropositionalEquality.Decidable where

open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality.Core

record DecidableEquality {a} (A : Set a) : Set a where
  field decide : Decidable {A = A} _≡_
open DecidableEquality public

open import Data.Unit as U using (⊤)
open import Data.Nat as ℕ using (ℕ)
open import Data.Char as C using (Char)
open import Data.String as S using (String)

instance

  decide-unit : DecidableEquality ⊤
  decide-unit .decide = U._≟_

  decide-nat : DecidableEquality ℕ
  decide-nat .decide = ℕ._≟_

  decide-char : DecidableEquality Char
  decide-char .decide = C._≟_

  decide-string : DecidableEquality String
  decide-string .decide = S._≟_
