{-# OPTIONS --without-K --safe #-}

open import Text.Parser.Types.Core using (Parameters)

module Text.Parser.Combinators.Numbers {l} {P : Parameters l} where

open import Data.Char.Base using (Char)
open import Data.Float.Base as Float using (Float; fromℕ; fromℤ)
open import Data.Integer.Base using (ℤ; -_; +_; _◃_)
open import Data.List.Base as List using ([]; _∷_)
open import Data.List.NonEmpty as List⁺ using (List⁺)
open import Data.List.Sized.Interface
open import Data.Maybe.Base using (Maybe; fromMaybe; maybe′)
open import Data.Nat.Base as ℕ using (ℕ; _+_; _*_)
import Data.Nat.GeneralisedArithmetic
open import Data.Product as Product using (_×_; _,_; uncurry)
open import Data.Sign.Base using (Sign)
open import Data.Sum.Base using ([_,_]′)

open import Function.Base using (const; id; _$_; _∘′_; case_of_)
open import Effect.Monad using (RawMonadPlus)

open import Relation.Unary
open import Relation.Binary.PropositionalEquality.Decidable using (DecidableEquality)
open import Data.Subset using (Subset; into)

open import Level.Bounded using (theSet; [_])
open import Text.Parser.Types P
open import Text.Parser.Combinators {P = P}
open Parameters P

module _ {{𝕄 : RawMonadPlus M}}
         {{𝕊 : Sized Tok Toks}}
         {{𝔻 : DecidableEquality (theSet Tok)}}
         {{ℂ : Subset Char (theSet Tok)}} where

 private module ℂ = Subset ℂ

 decimalDigit : ∀[ Parser [ ℕ ] ]
 decimalDigit = alts $ List.map (uncurry $ λ v c → v <$ exact (ℂ.into c))
              $ (0 , '0') ∷ (1 , '1') ∷ (2 , '2') ∷ (3 , '3') ∷ (4 , '4')
              ∷ (5 , '5') ∷ (6 , '6') ∷ (7 , '7') ∷ (8 , '8') ∷ (9 , '9') ∷ []

 hexadecimalDigit : ∀[ Parser [ ℕ ] ]
 hexadecimalDigit = decimalDigit <|> alts hex where
   hex = List.map (uncurry $ λ v c → v <$ exact (ℂ.into c))
       $ (10 , 'a') ∷ (11 , 'b') ∷ (12 , 'c')
       ∷ (13 , 'd') ∷ (14 , 'e') ∷ (15 , 'f') ∷ []

 private
   natFromDigits : List⁺ ℕ → ℕ
   natFromDigits = List⁺.foldl (λ ih v → ih * 10 + v) id

 sign : ∀[ Parser [ Sign ] ]
 sign = Sign.- <$ anyOf (List.map ℂ.into $ '-' ∷ '−' ∷ [])
    <|> Sign.+ <$ exact (ℂ.into '+')

 decimalℕ : ∀[ Parser [ ℕ ] ]
 decimalℕ = natFromDigits  <$> list⁺ decimalDigit

 decimalℤ : ∀[ Parser [ ℤ ] ]
 decimalℤ = uncurry convert <$> (sign <?&> decimalℕ) where
   convert : Maybe Sign → ℕ → ℤ
   convert ms n = fromMaybe Sign.+ ms ◃ n

 decimalFloat : ∀[ Parser [ Float ] ]
 decimalFloat = convert <$> rawDouble where

   fractional : ∀[ Parser [ List⁺ ℕ ] ]
   fractional = exact (ℂ.into '.') &> box (list⁺ decimalDigit)

   fromFractional : List⁺ ℕ → Float
   fromFractional ds = fromℕ (natFromDigits ds)
               Float.÷ fromℕ (10 ℕ.^ List⁺.length ds)

   eNotation : ∀[ Parser [ Maybe Sign × ℕ ] ]
   eNotation = anyOf (ℂ.into 'E' ∷ ℂ.into 'e' ∷ [])
             &> box (sign <?&> decimalℕ)

   fromENotation : Maybe Sign × ℕ → Float → Float
   fromENotation (ms , e) f = case fromMaybe Sign.+ ms of λ where
     Sign.- → f Float.÷ fromℕ (10 ℕ.^ e)
     Sign.+ → f Float.* fromℕ (10 ℕ.^ e)

   rawDouble : ∀[ Parser [ (ℤ × Maybe (List⁺ ℕ)) × Maybe (Maybe Sign × ℕ) ] ]
   rawDouble = (decimalℤ <&?> box fractional) <&?> box eNotation

   convert : (ℤ × Maybe (List⁺ ℕ)) × Maybe (Maybe Sign × ℕ) → Float
   convert ((int , mfrac) , menot)
     = maybe′ fromENotation id menot
     $ maybe′ (λ m f → f Float.+ fromFractional m) id mfrac
     $ fromℤ int
