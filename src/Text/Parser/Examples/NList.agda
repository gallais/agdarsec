-- Challenge taken from stackoverflow:
-- http://stackoverflow.com/questions/12380239/agda-parsing-nested-lists

module Text.Parser.Examples.NList where

open import Data.Nat.Base
open import Data.Char.Base
open import Data.List.Base hiding ([_])
open import Data.List.Sized.Interface
open import Data.Maybe
import Data.DifferenceList as DList
open import Function

open import Text.Parser.Examples.Base
open import Text.Parser.Numbers

NList : Set → ℕ → Set
NList A zero    = A
NList A (suc n) = List (NList A n)

module _ {Chars : ℕ → Set} {{𝕊 : Sized Char Chars}} where

 NList′ : {A : Set} → [ Parser Char Chars Maybe A ] →
          (n : ℕ)   → [ Parser Char Chars Maybe (NList A n) ]
 NList′ A zero    = A
 NList′ A (suc n) = parens $ box $ DList.toList <$>
                    chainl1 (DList.[_] <$> NList′ A n) (box $ DList._++_ <$ char ',')

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
