module Text.Parser.Examples.Identifier where

open import Data.Nat.Base
open import Data.Char.Base
open import Data.List as List hiding ([_])
open import Data.List.NonEmpty as NonEmpty hiding ([_])
open import Data.List.Sized.Interface
open import Data.Maybe
open import Data.String as String
open import Function

open import Text.Parser.Examples.Base

record Identifier : Set where
  constructor mkIdentifier
  field getIdentifier : List⁺ Char

module _ {Chars : ℕ → Set} {{𝕊 : Sized Char Chars}} where

 identifier : [ Parser Char Chars Maybe Identifier ]
 identifier = mkIdentifier <$> list⁺ alpha

-- tests

_ : "hi" ∈ identifier
_ = mkIdentifier ('h' ∷ 'i' ∷ []) !
