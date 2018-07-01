module Text.Parser.Char where

open import Data.Nat.Base
open import Data.Sum
open import Data.Bool.Base
open import Data.Char
open import Data.String as String
open import Data.List.Base as List hiding ([_])
open import Data.List.NonEmpty as NonEmpty hiding ([_])
open import Category.Monad
open import Function

open import Relation.Unary.Indexed
open import Induction.Nat.Strong
open import Data.List.Sized.Interface
open import Data.Subset
open import Relation.Binary.PropositionalEquality.Decidable

open import Text.Parser.Types
open import Text.Parser.Combinators
open import Text.Parser.Instruments
open import Text.Parser.Numbers

module _ {P : Parameters} (open Parameters P)
         {{𝕊 : Sized Tok Toks}}
         {{𝕄 : RawMonadPlus M}}
         {{𝔻 : DecidableEquality Tok}}
         {{ℂ : Subset Char Tok}}
         {{𝕀 : Instrumented P}} where

 module ℂ = Subset ℂ

 char : Char → [ Parser P Tok ]
 char = exact ∘ ℂ.into

 space : [ Parser P Tok ]
 space = anyOf $ List.map ℂ.into $ ' ' ∷ '\t' ∷ '\n' ∷ []

 spaces : [ Parser P (List⁺ Tok) ]
 spaces = list⁺ space

 text : (t : String) {_ : T (not $ null $ String.toList t)} → [ Parser P (List⁺ Tok) ]
 text t {pr} with String.toList t | pr
 ... | []     | ()
 ... | x ∷ xs | _ = exacts $ NonEmpty.map ℂ.into $ x ∷ xs

 module _ {A : Set} where

  parens : [ □ Parser P A ⟶ Parser P A ]
  parens = between (char '(') (box (char ')'))

  parens? : [ Parser P A ⟶ Parser P A ]
  parens? = between? (char '(') (box (char ')'))

  withSpaces : [ Parser P A ⟶ Parser P A ]
  withSpaces A = spaces ?&> A <&? box spaces

 lowerAlpha : [ Parser P Tok ]
 lowerAlpha = anyOf (List.map ℂ.into $ String.toList "abcdefghijklmnopqrstuvwxyz")

 upperAlpha : [ Parser P Tok ]
 upperAlpha = anyOf (List.map ℂ.into $ String.toList "ABCDEFGHIJKLMNOPQRSTUVWXYZ")

 alpha : [ Parser P Tok ]
 alpha = lowerAlpha <|> upperAlpha

 num : [ Parser P ℕ ]
 num = decimalDigit

 alphanum : [ Parser P (Tok ⊎ ℕ) ]
 alphanum = alpha <⊎> num
