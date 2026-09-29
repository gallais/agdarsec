{-# OPTIONS --guardedness #-}

module JSON where

open import Data.List.Base using ([_])
open import Data.JSON
open import Data.Product using (_,_)
open import Data.Sum using (inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Text.Parser
open import Text.Parser.JSON using (value)

_ : runParser value "{\"key\": \"value\"}" ≡ inj₂ (object ([ "key" , string "value" ]))
_ = refl
