-- Parser based on RFC 8259: https://tools.ietf.org/html/rfc8259

{-# OPTIONS --without-K --safe #-}

open import Text.Parser.Types.Core using (Parameters)

module Text.Parser.JSON {l} {P : Parameters l} where

open import Category.Monad using (RawMonadPlus)

open import Data.Bool.Base using (Bool; true; false)
open import Data.Char.Base using (Char)
open import Data.Float.Base using (Float)
open import Data.List.Base using (List; []; _∷_)
import Data.List.NonEmpty as List⁺
open import Data.List.Sized.Interface
open import Data.Maybe.Base using (maybe′)
open import Data.Product using (_×_; uncurry)
open import Data.String.Base using (String)
open import Data.Subset using (Subset; into)
open import Data.Unit.Base using (⊤)

open import Induction.Nat.Strong as Box using (□_; fix)

open import Function.Base using (_$_; _∘′_)

open import Relation.Unary
open import Relation.Binary.PropositionalEquality.Decidable using (DecidableEquality)

open import Level.Bounded using (theSet; [_])
open import Text.Parser.Types P
open import Text.Parser.Combinators {P = P}
open import Text.Parser.Combinators.Char {P = P}
open import Text.Parser.Combinators.Numbers {P = P}
open Parameters P


module JSON where

  -- I wish I could use a sized type here but unfortunately they're not
  -- considered safe anymore.
  data JSON : Set where
    null   : JSON
    bool   : Bool → JSON
    number : Float → JSON
    string : String → JSON
    array  : List JSON → JSON
    object : List (String × JSON) → JSON

open JSON using (JSON)

module _ {{𝕄 : RawMonadPlus M}}
         {{𝕊 : Sized Tok Toks}}
         {{𝔻 : DecidableEquality (theSet Tok)}}
         {{ℂ : Subset Char (theSet Tok)}}
         {{ℂ⁻ : Subset (theSet Tok) Char}}
         where


-- We assume that when we call a subparser all of the whitespace before
-- the potential token has been consumed already. So we should systematically
-- consume spaces after the tokens we have happily recognised.

-- Structural characters

  structuralChar : Char → ∀[ Parser [ ⊤ ] ]
  structuralChar c = _ <$ (char c <&? box spaces)

  beginArray     = structuralChar '['
  beginObject    = structuralChar '{'
  endArray       = structuralChar ']'
  endObject      = structuralChar '}'
  nameSeparator  = structuralChar ':'
  valueSeparator = structuralChar ','

-- Subparser for members, provided a subparser for smaller JSON objects
-- According to the RFC:
-- member = string name-separator value

  member : ∀[ □ Parser [ JSON ] ⇒ Parser [ String × JSON ] ]
  member rec = stringLiteral <&? box spaces
             <&> box (nameSeparator &> rec)

-- Subparser for JSON objects, provided a subparser for smaller JSON objects
-- According to the RFC:
-- object = begin-object [ member *( value-separator member ) ] end-object

  object : ∀[ □ Parser [ JSON ] ⇒ Parser [ List (String × JSON) ] ]
  object rec =
    maybe′ (uncurry λ a mas → a ∷ maybe′ List⁺.toList [] mas) []
    <$> (beginObject
         &?> box (member rec <&?> box (list⁺ (valueSeparator &> box (member rec))))
         <& box endObject)

-- Subparser for JSON arrays, provided a subparser for smaller JSON objects
-- According to the RFC:
-- array = begin-array [ value *( value-separator value ) ] end-array

  array : ∀[ □ Parser [ JSON ] ⇒ Parser [ List JSON ] ]
  array rec =
    maybe′ (uncurry λ a mas → a ∷ maybe′ List⁺.toList [] mas) []
    <$> (beginArray
         &?> lift2l (λ p q → p <&?> box q) rec (list⁺ (valueSeparator &> rec))
         <& box endArray)

-- Parsing JSON values
  value : ∀[ Parser [ JSON ] ]
  value = (spaces ?&>_) $ fix (Parser [ JSON ]) $ λ rec →
    alts $ (JSON.null       <$  text "null"   <&? box spaces)
         ∷ (JSON.bool true  <$  text "true"   <&? box spaces)
         ∷ (JSON.bool false <$  text "false"  <&? box spaces)
         ∷ (JSON.number     <$> decimalFloat  <&? box spaces)
         ∷ (JSON.string     <$> stringLiteral <&? box spaces)
         ∷ (JSON.array      <$> array rec)
         ∷ (JSON.object     <$> object rec)
         ∷ []
