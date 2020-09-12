module Identifier where

import Level
open import Level.Bounded using ([_])

open import Data.Char.Base using (Char)
open import Data.List as List using ([]; _∷_)
open import Data.List.NonEmpty as List⁺ using (List⁺; _∷_)
open import Data.List.Sized.Interface using ()

open import Base Level.zero

record Identifier : Set where
  constructor mkIdentifier
  field getIdentifier : List⁺ Char

identifier : ∀[ Parser chars [ Identifier ] ]
identifier = mkIdentifier <$> list⁺ alpha

-- tests

_ : "hi" ∈ identifier
_ =  mkIdentifier ('h' ∷ 'i' ∷ []) !
