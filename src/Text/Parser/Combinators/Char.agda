{-# OPTIONS --without-K --safe #-}

module Text.Parser.Combinators.Char where

open import Data.Bool.Base using (T; not)
open import Data.Char.Base using (Char)
open import Data.List.Base as List using ([]; _∷_; null)
open import Data.List.NonEmpty as List⁺ using (_∷_)
open import Data.Nat.Base using (ℕ)
open import Data.String.Base as String using (String)
open import Data.Sum.Base using ()

open import Category.Monad using (RawMonadPlus)
open import Function.Base using (_∘′_; _$′_)

open import Relation.Unary
open import Induction.Nat.Strong using (□_)
open import Data.List.Sized.Interface using (Sized)
open import Data.Subset using (Subset; into)
open import Relation.Binary.PropositionalEquality.Decidable using (DecidableEquality)

open import Level.Bounded
open import Text.Parser.Types
open import Text.Parser.Combinators
open import Text.Parser.Combinators.Numbers

module _ {l} {P : Parameters l} (open Parameters P)
         {{𝕊 : Sized Tok Toks}}
         {{𝕄 : RawMonadPlus M}}
         {{𝔻 : DecidableEquality (theSet Tok)}}
         {{ℂ : Subset Char (theSet Tok)}}
         where

 module ℂ = Subset ℂ

 char : Char → ∀[ Parser P Tok ]
 char = exact ∘′ ℂ.into

 anyCharBut : Char → ∀[ Parser P Tok ]
 anyCharBut = anyTokenBut ∘′ ℂ.into

 space : ∀[ Parser P Tok ]
 space = anyOf $′ List.map ℂ.into $′ ' ' ∷ '\t' ∷ '\n' ∷ []

 spaces : ∀[ Parser P (List⁺ Tok) ]
 spaces = list⁺ space

 text : (t : String) {_ : T (not $′ null $′ String.toList t)} →
        ∀[ Parser P (List⁺ Tok) ]
 text t {pr} with String.toList t | pr
 ... | []     | ()
 ... | x ∷ xs | _ = exacts $′ List⁺.map ℂ.into (x ∷ xs)

 module _ {A : Set≤ l} where

  parens : ∀[ □ Parser P A ⇒ Parser P A ]
  parens = between (char '(') (box (char ')'))

  parens? : ∀[ Parser P A ⇒ Parser P A ]
  parens? = between? (char '(') (box (char ')'))

  withSpaces : ∀[ Parser P A ⇒ Parser P A ]
  withSpaces A = spaces ?&> A <&? box spaces

 lowerAlpha : ∀[ Parser P Tok ]
 lowerAlpha = anyOf
            $′ List.map ℂ.into
            $′ String.toList "abcdefghijklmnopqrstuvwxyz"

 upperAlpha : ∀[ Parser P Tok ]
 upperAlpha = anyOf
            $′ List.map ℂ.into
            $′ String.toList "ABCDEFGHIJKLMNOPQRSTUVWXYZ"

 alpha : ∀[ Parser P Tok ]
 alpha = lowerAlpha <|> upperAlpha

 alphas⁺ : ∀[ Parser P (List⁺ Tok) ]
 alphas⁺ = list⁺ alpha

 num : ∀[ Parser P [ ℕ ] ]
 num = decimalDigit

 alphanum : ∀[ Parser P (Tok ⊎ [ ℕ ]) ]
 alphanum = alpha <⊎> num
