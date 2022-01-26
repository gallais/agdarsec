{-# OPTIONS --without-K --safe #-}

open import Text.Parser.Types.Core using (Parameters)

module Text.Parser.Combinators.Char {l} {P : Parameters l} where

open import Data.Unit.Base
open import Data.Bool.Base using (T; not)
open import Data.Char.Base using (Char)
open import Data.List.Base as List using ([]; _∷_; null)
open import Data.List.NonEmpty as List⁺ using (_∷_)
open import Data.Maybe.Base using (nothing; just; maybe; fromMaybe)
open import Data.Nat.Base using (ℕ)
import Data.Nat.Show as ℕ
open import Data.Product using (_,_)
open import Data.String.Base as String using (String)
open import Data.Vec.Base as Vec using (toList)

open import Category.Monad using (RawMonadPlus)
open import Function.Base using (_∘′_; _$′_; _$_)

open import Relation.Nullary using (does)
open import Relation.Unary
open import Induction.Nat.Strong using (□_)
open import Data.List.Sized.Interface using (Sized)
open import Data.Subset using (Subset; into)
open import Relation.Binary.PropositionalEquality.Decidable using (DecidableEquality; decide)

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

 private module ℂ = Subset ℂ

 char : Char → ∀[ Parser Tok ]
 char = exact ∘′ ℂ.into

 anyCharBut : Char → ∀[ Parser Tok ]
 anyCharBut = anyTokenBut ∘′ ℂ.into

 noneOfChars : List.List Char → ∀[ Parser Tok ]
 noneOfChars = noneOf ∘′ List.map ℂ.into

 anyOfChars : List.List Char → ∀[ Parser Tok ]
 anyOfChars = anyOf ∘′ List.map ℂ.into

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

module _ {{𝕊 : Sized Tok Toks}}
         {{𝕄 : RawMonadPlus M}}
         {{𝔻 : DecidableEquality (theSet Tok)}}
         {{ℂ  : Subset Char (theSet Tok)}}
         {{ℂ⁻ : Subset (theSet Tok)  Char}}
         where

 private
   module ℂ = Subset ℂ
   module ℂ⁻ = Subset ℂ⁻

 stringLiteral : ∀[ Parser [ String ] ]
 stringLiteral =
   convert <$> (char '"'
           &?> box escaped
           <&> box (list⁺ (unescaped <&?> box escaped)
           <?& char '"'))

   where

     toks : Set≤ _
     toks = List⁺ Tok

     unescaped : ∀[ Parser toks ]
     unescaped = list⁺ (noneOfChars ('\\' ∷ '"' ∷ []))

     convertUnicode : Vec.Vec ℕ 4 → theSet toks
     convertUnicode ds = List⁺.map ℂ.into
                       $ '\\' ∷ 'u' ∷ List.map toChar (toList ds)

       where

         toChar : ℕ → Char -- only for hexadecimal digits
         toChar 0  = '0'
         toChar 1  = '1'
         toChar 2  = '2'
         toChar 3  = '3'
         toChar 4  = '4'
         toChar 5  = '5'
         toChar 6  = '6'
         toChar 7  = '7'
         toChar 8  = '8'
         toChar 9  = '9'
         toChar 10 = 'a'
         toChar 11 = 'b'
         toChar 12 = 'c'
         toChar 13 = 'd'
         toChar 14 = 'e'
         toChar _  = 'f'

     escaped : ∀[ Parser toks ]
     escaped =
       let unicode : ∀[ Parser (Maybe toks) ]
           unicode = just ∘′ convertUnicode <$> replicate 4 hexadecimalDigit

           chunks : ∀[ Parser (List⁺ toks) ]
           chunks = list⁺ ((λ (a , mb) → fromMaybe (a ∷ []) mb)
             <$> (char '\\' -- escaping
             &> box ((_, nothing) <$> anyOfChars ('"' ∷ '\\' ∷ 'r' ∷ 'n' ∷ 't' ∷ [])) -- special characters
               <|> char 'u' <&> box unicode))
       in List⁺.concat <$> chunks

     convert : theSet (Maybe toks × Maybe (List⁺ (toks × Maybe toks))) → String
     convert (mt , mts) = let open List in
       String.fromList $
         fromMToks mt ++
          maybe (concatMap (λ (ts , mts) → fromToks ts ++ fromMToks mts) ∘′ List⁺.toList) [] mts

       where

         fromToks : theSet toks → List.List Char
         fromToks = List⁺.toList ∘′ List⁺.map ℂ⁻.into

         fromMToks : theSet (Maybe toks) → List.List Char
         fromMToks = maybe fromToks []
