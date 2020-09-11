-- Challenge taken from stackoverflow:
-- http://stackoverflow.com/questions/12380239/agda-parsing-nested-lists

module NList {l} where

open import Level.Bounded using (Set≤; List; _$$_)

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.DifferenceList as DList using (DiffList; [_]; _++_)
open import Data.List.Base using ([]; _∷_)
open import Data.List.Sized.Interface using ()

open import Function.Base using (_$′_)

open import Base
open import Text.Parser.Combinators.Numbers

NList : Set≤ l → ℕ → Set≤ l
NList A zero    = A
NList A (suc n) = List (NList A n)

P : Parameters l
P = chars


module _ {A : Set≤ l} where

  NList′ : ∀[ Parser P A ] →
           (n : ℕ)      → ∀[ Parser P (NList A n) ]
  NList′ p zero    = p
  NList′ p (suc n) =
    let rec : Parser P (DiffList $$ NList A n) _
        rec = chainl1 ([_] <$> NList′ p n) (box $′ _++_ <$ char ',')
    in parens $′ box $′ DList.toList <$> rec

-- tests

_ : "((1,2,3),(4,5,6))" ∈ NList′ decimalℕ 2
_ = (1 ∷ 2 ∷ 3 ∷ []) ∷ (4 ∷ 5 ∷ 6 ∷ []) ∷ [] !

_ : "((1,2,3),(4,5,6),(7,8,9,10))" ∈ NList′ decimalℕ 2
_ = (1 ∷ 2 ∷ 3 ∷ []) ∷ (4 ∷ 5 ∷ 6 ∷ []) ∷ (7 ∷ 8 ∷ 9 ∷ 10 ∷ []) ∷ [] !

_ : "((1),(2))" ∈ NList′ decimalℕ 2
_ = (1 ∷ []) ∷ (2 ∷ []) ∷ [] !

_ : "((1,2))" ∈ NList′ decimalℕ 2
_ = (1 ∷ 2 ∷ []) ∷ [] !

_ : "(((1,2),(3,4)),((5,6),(7,8)))" ∈ NList′ decimalℕ 3
_ = ((1 ∷ 2 ∷ []) ∷ (3 ∷ 4 ∷ []) ∷ []) ∷
    ((5 ∷ 6 ∷ []) ∷ (7 ∷ 8 ∷ []) ∷ []) ∷ [] !
