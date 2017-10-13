\begin{code}
module Text.Parser.Success where

open import Data.Vec hiding ([_] ; map)
open import Data.Nat.Base
open import Data.Nat.LTE
open import Data.Char.Base
open import Data.List.Sized as Sized hiding (map)
open import Relation.Unary.Indexed

infix 1 _^_,_
\end{code}
%<*success>
\begin{code}
record Success (A : Set) (n : ℕ) : Set where
  constructor _^_,_
  field  value      : A
         {size}     : ℕ
         .small     : size < n
         leftovers  : Vec Char size
\end{code}
%</success>
\begin{code}
open Success

module _ {A B : Set} where

  map : (A → B) → [ Success A ⟶ Success B ]
  map f (a ^ m≤n , s) = f a ^ m≤n , s

module _ {A : Set} where

  lift : {m n : ℕ} → .(m ≤ n) → Success A m → Success A n
  lift m≤n (a ^ p<m , s) = a ^ ≤-trans p<m m≤n , s
\end{code}
