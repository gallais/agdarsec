module Data.Nat.LTE where

open import Data.Nat.Base
import Data.Nat.Properties as Prop
open import Relation.Binary

≤-refl : Reflexive _≤_
≤-refl = Prop.≤′⇒≤ ≤′-refl

≤-trans : Transitive _≤_
≤-trans z≤n _ = z≤n
≤-trans (s≤s p) (s≤s q) = s≤s (≤-trans p q)

<⇒≤ : ∀ {m n} → m < n → m ≤ n
<⇒≤ = ≤-trans (Prop.n≤1+n _)
