module Text.Parser.Examples.Identifier where

open import Data.Char.Base
open import Data.List as List hiding ([_])
open import Data.List.NonEmpty as NonEmpty hiding ([_])
open import Data.Maybe
open import Data.String as String
open import Function

open import Text.Parser.Examples.Base

alpha : [ Parser Char Maybe Char ]
alpha = anyOf $ String.toList "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ"

record Identifier : Set where
  constructor mkIdentifier
  field getIdentifier : List⁺ Char

identifier : [ Parser Char Maybe Identifier ]
identifier = mkIdentifier <$> list⁺ alpha

-- tests

_ : "Hi" ∈ identifier
_ = mkIdentifier ('H' ∷ 'i' ∷ []) !
