module Induction.Nat.Strong where

open import Data.Nat.Base
open import Data.Nat.LTE
open import Data.Nat.Properties
open import Relation.Unary.Indexed
open import Function

infix 4 □_
record □_ (A : ℕ → Set) (n : ℕ) : Set where
  constructor mkBox
  field call : ∀ {m} → .(m < n) → A m
open □_ public

module _ {A B : ℕ → Set} where

 map : [ A ⟶ B ] → [ □ A ⟶ □ B ]
 call (map f A) m<n = f (call A m<n)

module _ {A : ℕ → Set} where

 extract : [ □ A ] → [ A ]
 extract a = call a ≤-refl

 duplicate : [ □ A ⟶ □ □ A ]
 call (call (duplicate A) m<n) p<m = call A (<-trans p<m m<n)

 ≤-lower : {m n : ℕ} → .(m ≤ n) → (□ A) n → (□ A) m
 call (≤-lower m≤n A) p<m = call A (≤-trans p<m m≤n)

 <-lower : {m n : ℕ} → .(m < n) → (□ A) n → (□ A) m
 call (<-lower m<n A) p<m = call A (<-trans p<m m<n)

 fix□ : [ □ A ⟶ A ] → [ □ A ]
 call (fix□ f {zero})  ()
 call (fix□ f {suc n}) m<sn = f (≤-lower (≤-pred m<sn) (fix□ f))

module _ {A B : ℕ → Set} where

 map2 : {C : ℕ → Set} → [ A ⟶ B ⟶ C ] → [ □ A ⟶ □ B ⟶ □ C ]
 call (map2 f A B) m<n = f (call A m<n) (call B m<n)

 app : [ □ (A ⟶ B) ⟶ (□ A ⟶ □ B) ]
 call (app F A) m<n = call F m<n (call A m<n)

fix : ∀ A → [ □ A ⟶ A ] → [ A ]
fix A = extract ∘ fix□

module _ {A : ℕ → Set} where

 <-close : (∀ {m n} → .(m < n) → A n → A m) → [ A ⟶ □ A ]
 call (<-close down a) m<n = down m<n a

 ≤-close : (∀ {m n} → .(m ≤ n) → A n → A m) → [ A ⟶ □ A ]
 ≤-close down = <-close (λ .m<n → down (<⇒≤ m<n))

 loeb : [ □ (□ A ⟶ A) ⟶ □ A ]
 loeb = fix (□ (□ A ⟶ A) ⟶ □ A) $ λ rec f → mkBox λ m<n →
        call f m<n (call rec m<n (call (duplicate f) m<n))
