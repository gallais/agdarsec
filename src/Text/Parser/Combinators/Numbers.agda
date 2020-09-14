{-# OPTIONS --without-K --safe #-}

module Text.Parser.Combinators.Numbers where

open import Data.Char.Base using (Char)
open import Data.Integer.Base using (ℤ; -_; +_)
open import Data.List.Base as List using ([]; _∷_)
open import Data.List.NonEmpty as List⁺ using ()
open import Data.Nat.Base using (ℕ; _+_; _*_)
open import Data.Product as Product using (_,_; uncurry)

open import Data.List.Sized.Interface
open import Data.Sum.Base using ([_,_]′)
open import Data.Maybe.Base using (maybe′)

open import Function.Base using (const; id; _$_; _∘′_)
open import Category.Monad using (RawMonadPlus)

open import Relation.Unary
open import Relation.Binary.PropositionalEquality.Decidable using (DecidableEquality)
open import Data.Subset using (Subset; into)

open import Level.Bounded using (theSet; [_])
open import Text.Parser.Types
open import Text.Parser.Combinators

module _ {l} {P : Parameters l} (open Parameters P)
         {{𝕄 : RawMonadPlus M}}
         {{𝕊 : Sized Tok Toks}}
         {{𝔻 : DecidableEquality (theSet Tok)}}
         {{ℂ : Subset Char (theSet Tok)}} where

 private module ℂ = Subset ℂ

 decimalDigit : ∀[ Parser P [ ℕ ] ]
 decimalDigit = alts $ List.map (uncurry $ λ v c → v <$ exact (ℂ.into c))
              $ (0 , '0') ∷ (1 , '1') ∷ (2 , '2') ∷ (3 , '3') ∷ (4 , '4')
              ∷ (5 , '5') ∷ (6 , '6') ∷ (7 , '7') ∷ (8 , '8') ∷ (9 , '9') ∷ []

 decimalℕ : ∀[ Parser P [ ℕ ] ]
 decimalℕ = convert <$> list⁺ decimalDigit where
  convert = List⁺.foldl (λ ih v → ih * 10 + v) id

 decimalℤ : ∀[ Parser P [ ℤ ] ]
 decimalℤ = uncurry convert <$> (sign <?&> decimalℕ) where
   sign    = anyOf (List.map ℂ.into $ '-' ∷ '−' ∷ []) <⊎> exact (ℂ.into '+')
   convert = λ s → maybe′ [ const (-_) , const id ]′ id s ∘′ +_
