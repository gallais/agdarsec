-- Implemented according to https://www.rfc-editor.org/info/rfc8259/#section-7

{-# OPTIONS --without-K --safe #-}

module Data.JSON.Show.Escape where

open import Data.Bool.Base using (Bool; if_then_else_)
open import Data.Char using (Char; fromℕ; toℕ; _≟_)
open import Data.List using (List; []; _∷_; [_]; concatMap; find)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (_≤?_)
open import Data.Nat.Show using (charsInBase)
open import Data.Product using (_×_; _,_)
open import Data.String using (String; toList; fromList; padLeft)
open import Function using (_$_; case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary.Decidable using (does) renaming (_×-dec_ to _×?_; _⊎-dec_ to _⊎?_)

escapedReplacements : List (Char × Char)
escapedReplacements = ('"' , '"') ∷ ('\\' , '\\') ∷ ('/' , '/') ∷ ('\b' , 'b') ∷ ('\f' , 'f') ∷ ('\n' , 'n') ∷ ('\r' , 'r') ∷ ('\t' , 't') ∷ []

replaceEscaped : Char → List Char
replaceEscaped c = '\\' ∷ (case (find (λ {(x , _) → x ≟ c}) escapedReplacements) of λ
  {(just (_ , y)) → [ y ]
  ; nothing → 'u' ∷ toList (padLeft '0' 4 $ fromList $ charsInBase 16 (toℕ c))
  })

-- Test.
private
  _ : replaceEscaped '\t' ≡ toList "\\t"; _ = refl
  _ : replaceEscaped '\x1b' ≡ toList "\\u001b"; _ = refl

isUnescaped : Char → Bool
isUnescaped c = let i = toℕ c in does (
  (0x20 ≤? i) ×? (i ≤? 0x21)
  ⊎?
  (0x23 ≤? i) ×? (i ≤? 0x5B)
  ⊎?
  (0x5D ≤? i) ×? (i ≤? 0x10FFFF))

escape : String → String
escape s = fromList $ concatMap (λ c →
  if isUnescaped c then [ c ]
  else replaceEscaped c)
  (toList s)

-- Test.
private
  _ : escape "a\t\x1b bc\x0" ≡ "a\\t\\u001b bc\\u0000"; _ = refl
