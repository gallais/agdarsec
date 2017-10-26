\begin{code}
module Relation.Unary.Indexed where

open import Data.Sum
open import Data.Product

module _ {I : Set} where

 infixr 1 _⟶_
 infixr 2 _⊕_
 infixr 3 _⊗_
 infix 5 [_]
\end{code}
%<*arrow>
\begin{code}
 _⟶_ : (I → Set) → (I → Set) → (I → Set)
 (A ⟶ B) n = A n → B n
\end{code}
%</arrow>
%<*sum>
\begin{code}
 _⊕_ : (I → Set) → (I → Set) → (I → Set)
 (A ⊕ B) n = A n ⊎ B n
\end{code}
%</sum>
%<*product>
\begin{code}
 _⊗_ : (I → Set) → (I → Set) → (I → Set)
 (A ⊗ B) n = A n × B n
\end{code}
%</product>
%<*constant>
\begin{code}
 κ : Set → (I → Set)
 κ A n = A
\end{code}
%</constant>
%<*forall>
\begin{code}
 [_] : (I → Set) → Set
 [ A ] = ∀ {n} → A n
\end{code}
%</forall>
