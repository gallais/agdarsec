module Identifier where

import Level
open import Data.Empty
open import Data.Nat.Base
open import Data.Char.Base
open import Data.Maybe as Maybe
open import Data.List as List hiding ([_])
open import Data.List.NonEmpty as NonEmpty hiding ([_])
open import Data.List.Sized.Interface using (Sized)
open import Data.List.Sized
open import Data.String as String
open import Category.Monad
open import Function

open import Base

record Identifier : Set where
  constructor mkIdentifier
  field getIdentifier : List⁺ Char

identifier : [ Parser Chars+Maybe Identifier ]
identifier = mkIdentifier <$> list⁺ alpha

-- tests

_ : "hi" ∈ identifier
_ =  mkIdentifier ('h' ∷ 'i' ∷ []) !
