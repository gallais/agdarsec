-- Parser based on RFC 8259: https://tools.ietf.org/html/rfc8259

{-# OPTIONS --guardedness #-}

module Text.Parser.JSON where

open import Data.Bool.Base
open import Data.Char.Base
open import Data.String.Base using (String)
open import Data.List using (List; []; _∷_)
open import Data.List.NonEmpty as List⁺ using (List⁺)
open import Data.Maybe
open import Data.Product
open import Data.Unit.Base using (⊤)
open import Function.Base
open import Induction.Nat.Strong
open import Text.Parser
open import Data.JSON using (JSON)

-- We assume that when we call a subparser all of the whitespace before
-- the potential token has been consumed already. So we should systematically
-- consume spaces after the tokens we have happily recognised.

-- Structural characters

structuralChar : Char → ∀[ Parser ⊤ ]
structuralChar c = _ <$ (char c  <&? box spaces)
                                           
beginArray     = structuralChar '['
beginObject    = structuralChar '{'
endArray       = structuralChar ']'
endObject      = structuralChar '}'
nameSeparator  = structuralChar ':'
valueSeparator = structuralChar ','

-- Subparser for members, provided a subparser for smaller JSON objects
-- According to the RFC:
-- member = string name-separator value

member : ∀[ □ Parser JSON ⇒ Parser (String × JSON) ]
member rec = stringLiteral <&? box spaces
           <&> box (nameSeparator &> rec)

-- Subparser for JSON objects, provided a subparser for smaller JSON objects
-- According to the RFC:
-- object = begin-object [ member *( value-separator member ) ] end-object

object : ∀[ □ Parser JSON ⇒ Parser (List (String × JSON)) ]
object rec =
  maybe′ (uncurry λ a mas → a ∷ maybe′ List⁺.toList [] mas) []
  <$> (beginObject
      &?> box (member rec <&?> box (list⁺ (valueSeparator &> box (member rec))))
        <& box endObject)

-- Subparser for JSON arrays, provided a subparser for smaller JSON objects
-- According to the RFC:
-- array = begin-array [ value *( value-separator value ) ] end-array

array : ∀[ □ Parser JSON ⇒ Parser (List JSON) ]
array rec =
  maybe′ (uncurry λ a mas → a ∷ maybe′ List⁺.toList [] mas) []
  <$> (beginArray
      &?> lift2l (λ p q → p <&?> box q) rec (list⁺ (valueSeparator &> rec))
        <& box endArray)

-- Parsing JSON values
value : ∀[ Parser JSON ]
value = (spaces ?&>_) $ fix (Parser JSON) $ λ rec →
  alts $ (JSON.null       <$  text "null"   <&? box spaces)
       ∷ (JSON.bool true  <$  text "true"   <&? box spaces)
       ∷ (JSON.bool false <$  text "false"  <&? box spaces)
       ∷ (JSON.number     <$> decimalFloat  <&? box spaces)
       ∷ (JSON.string     <$> stringLiteral <&? box spaces)
       ∷ (JSON.array      <$> array rec)
       ∷ (JSON.object     <$> object rec)
       ∷ []
