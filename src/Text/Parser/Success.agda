module Text.Parser.Success where

open import Data.Nat.Base
open import Data.Nat.LTE
open import Data.Char.Base
open import Data.List.Sized as Sized hiding (map)
open import Relation.Unary.Indexed

infix 1 _^_,_
record Success (Tok : Set) (A : Set) (n : ℕ) : Set where
  constructor _^_,_
  field
    value     : A
    {size}    : ℕ
    .small    : size < n
    leftovers : ∣List Tok ∣≡ size
open Success

module _ {Tok A B : Set} where

  map : (A → B) → [ Success Tok A ⟶ Success Tok B ]
  map f (a ^ m≤n , s) = f a ^ m≤n , s

module _ {Tok A : Set} where

  lift : {m n : ℕ} → .(m ≤ n) → Success Tok A m → Success Tok A n
  lift m≤n (a ^ p<m , s) = a ^ ≤-trans p<m m≤n , s
