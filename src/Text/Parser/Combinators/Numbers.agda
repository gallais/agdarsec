module Text.Parser.Combinators.Numbers where

open import Data.Nat.Base as ℕ
open import Data.Integer.Base as ℤ hiding (sign)
open import Data.Char
import Data.Char.Unsafe as C using (_≟_)
open import Data.List.Base as List
open import Data.List.NonEmpty as NonEmpty
open import Data.List.Sized.Interface
open import Data.Maybe
open import Data.Product
open import Function
open import Category.Monad
open import Relation.Binary
open import Relation.Binary.PropositionalEquality.Decidable

open import Data.Subset
open import Relation.Unary

open import Text.Parser.Types
open import Text.Parser.Combinators

instance eqChar = C._≟_

module _ {P : Parameters} (open Parameters P)
         {{𝕄 : RawMonadPlus M}}
         {{𝕊 : Sized Tok Toks}}
         {{𝔻 : DecidableEquality Tok}}
         {{ℂ : Subset Char Tok}} where

 private module ℂ = Subset ℂ

 decimalDigit : ∀[ Parser P ℕ ]
 decimalDigit = alts $ List.map (uncurry $ λ v c → v <$ exact (ℂ.into c))
              $ (0 , '0') ∷ (1 , '1') ∷ (2 , '2') ∷ (3 , '3') ∷ (4 , '4')
              ∷ (5 , '5') ∷ (6 , '6') ∷ (7 , '7') ∷ (8 , '8') ∷ (9 , '9') ∷ []

 decimalℕ : ∀[ Parser P ℕ ]
 decimalℕ = convert <$> list⁺ decimalDigit where
  convert = NonEmpty.foldl (λ ih v → ih ℕ.* 10 ℕ.+ v) id

 decimalℤ : ∀[ Parser P ℤ ]
 decimalℤ = uncurry convert <$> (sign <?&> decimalℕ) where
   sign    = anyOf (List.map ℂ.into $ '-' ∷ '−' ∷ [])
   convert = λ s → maybe′ (const (-_)) id s ∘′ +_
