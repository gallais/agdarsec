\begin{code}
module Induction.Nat.Strong where

open import Data.Nat.Base
open import Data.Nat.LTE
open import Data.Nat.Properties
open import Relation.Unary.Indexed
open import Function

infix 4 □_
\end{code}
%<*box>
\begin{code}
record □_ (A : ℕ → Set) (n : ℕ) : Set where
  constructor mkBox
  field call : ∀ {m} → .(m < n) → A m
\end{code}
%</box>
\begin{code}
open □_ public

module _ {A B : ℕ → Set} where
\end{code}
%<*map>
\begin{code}
 map : [ A ⟶ B ] → [ □ A ⟶ □ B ]
 call (map f A) m<n = f (call A m<n)
\end{code}
%</map>
\begin{code}
module _ {A : ℕ → Set} where

\end{code}
%</app>
%<*extract>
\begin{code}
 extract : [ □ A ] → [ A ]
 extract a = call a ≤-refl
\end{code}
%</extract>
%<*duplicate>
\begin{code}
 duplicate : [ □ A ⟶ □ □ A ]
 call (call (duplicate A) m<n) p<m = call A (<-trans p<m m<n)
\end{code}
%</duplicate>
\begin{code}
 lower : {m n : ℕ} → .(m ≤ n) → (□ A) n → (□ A) m
 call (lower m≤n A) p<m = call A (≤-trans p<m m≤n)
\end{code}
%<*fixbox>
\begin{code}
 fix□ : [ □ A ⟶ A ] → [ □ A ]
\end{code}
%</fixbox>
\begin{code}
 call (fix□ f {zero})  ()
 call (fix□ f {suc n}) m<sn =
  f $ mkBox $ λ p<m →
  call (fix□ f {n}) (≤-trans p<m (<⇒≤pred m<sn))

module _ {A B : ℕ → Set} where

 map2 : {C : ℕ → Set} → [ A ⟶ B ⟶ C ] → [ □ A ⟶ □ B ⟶ □ C ]
 call (map2 f A B) m<n = f (call A m<n) (call B m<n)

\end{code}
%<*app>
\begin{code}
 app : [ □ (A ⟶ B) ⟶ (□ A ⟶ □ B) ]
 call (app F A) m<n = call F m<n (call A m<n)
\end{code}
%</app>
%<*fix>
\begin{code}
fix : ∀ A → [ □ A ⟶ A ] → [ A ]
\end{code}
%</fix>
\begin{code}
fix A = extract ∘ fix□

module _ {A : ℕ → Set} where

 loeb : [ □ (□ A ⟶ A) ⟶ □ A ]
 loeb = fix (□ (□ A ⟶ A) ⟶ □ A) $ λ rec f → mkBox λ m<n →
        call f m<n (call rec m<n (call (duplicate f) m<n))
\end{code}
