{-# OPTIONS --without-K --safe #-}

open import Text.Parser.Types.Core using (Parameters)

module Text.Parser.Combinators.Char {l} {P : Parameters l} where

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
open import Text.Parser.Types P
open import Text.Parser.Combinators {P = P}
open import Text.Parser.Combinators.Numbers {P = P}
open Parameters P

module _ {{𝕊 : Sized Tok Toks}}
         {{𝕄 : RawMonadPlus M}}
         {{𝔻 : DecidableEquality (theSet Tok)}}
         {{ℂ : Subset Char (theSet Tok)}}
         where

 module ℂ = Subset ℂ

 char : Char → ∀[ Parser Tok ]
 char = exact ∘′ ℂ.into

 anyCharBut : Char → ∀[ Parser Tok ]
 anyCharBut = anyTokenBut ∘′ ℂ.into

 space : ∀[ Parser Tok ]
 space = anyOf $′ List.map ℂ.into $′ ' ' ∷ '\t' ∷ '\n' ∷ []

 spaces : ∀[ Parser (List⁺ Tok) ]
 spaces = list⁺ space

 text : (t : String) {_ : T (not $′ null $′ String.toList t)} →
        ∀[ Parser (List⁺ Tok) ]
 text t {pr} with String.toList t | pr
 ... | []     | ()
 ... | x ∷ xs | _ = exacts $′ List⁺.map ℂ.into (x ∷ xs)

 module _ {A : Set≤ l} where

  parens : ∀[ □ Parser A ⇒ Parser A ]
  parens = between (char '(') (box (char ')'))

  parens? : ∀[ Parser A ⇒ Parser A ]
  parens? = between? (char '(') (box (char ')'))

  withSpaces : ∀[ Parser A ⇒ Parser A ]
  withSpaces A = spaces ?&> A <&? box spaces

 lowerAlpha : ∀[ Parser Tok ]
 lowerAlpha = anyOf
            $′ List.map ℂ.into
            $′ String.toList "abcdefghijklmnopqrstuvwxyz"

 upperAlpha : ∀[ Parser Tok ]
 upperAlpha = anyOf
            $′ List.map ℂ.into
            $′ String.toList "ABCDEFGHIJKLMNOPQRSTUVWXYZ"

 alpha : ∀[ Parser Tok ]
 alpha = lowerAlpha <|> upperAlpha

 alphas⁺ : ∀[ Parser (List⁺ Tok) ]
 alphas⁺ = list⁺ alpha

 num : ∀[ Parser [ ℕ ] ]
 num = decimalDigit

 alphanum : ∀[ Parser (Tok ⊎ [ ℕ ]) ]
 alphanum = alpha <⊎> num
