module Text.Parser.Numbers where

open import Data.Nat.Base as ℕ
open import Data.Integer.Base as ℤ
open import Data.Char
open import Data.List.Base as List hiding ([_])
open import Data.List.NonEmpty as NonEmpty hiding ([_])
open import Data.List.Sized.Interface
open import Data.Maybe
open import Data.Product
open import Function
open import Category.Monad

open import Relation.Unary.Indexed
open import Text.Parser.Combinators

instance eqChar = Data.Char._≟_

module _ {M : Set → Set} {{𝕄 : RawMonadPlus M}}
         {Chars : ℕ → Set} {{𝕊 : Sized Char Chars}} where

 decimalDigit : [ Parser Char Chars M ℕ ]
 decimalDigit = alts $ List.map (uncurry $ λ v c → v <$ exact {Tok = Char} c)
              $ (0 , '0') ∷ (1 , '1') ∷ (2 , '2') ∷ (3 , '3') ∷ (4 , '4')
              ∷ (5 , '5') ∷ (6 , '6') ∷ (7 , '7') ∷ (8 , '8') ∷ (9 , '9') ∷ []

 decimalℕ : [ Parser Char Chars M ℕ ]
 decimalℕ = convert <$> list⁺ decimalDigit where
  convert = NonEmpty.foldl (λ ih v → ih ℕ.* 10 ℕ.+ v) id

 decimalℤ : [ Parser Char Chars M ℤ ]
 decimalℤ = uncurry convert <$> (anyOf ('-' ∷ '−' ∷ []) <?&> decimalℕ) where
   convert = λ s → maybe′ (const (-_)) id s ∘′ +_

