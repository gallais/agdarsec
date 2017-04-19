module Text.Parser.Char where

open import Data.Nat.Base
open import Data.Bool.Base
open import Data.Char
open import Data.String as String
open import Data.List.Base hiding ([_])
open import Data.List.NonEmpty as NonEmpty hiding ([_])
open import Category.Monad
open import Function

open import Relation.Unary.Indexed
open import Induction.Nat.Strong
open import Data.List.Sized.Interface
open import Text.Parser.Combinators

instance eqChar = Data.Char._≟_

module _ {Chars : ℕ → Set} {{𝕊 : Sized Char Chars}}
         {M : Set → Set} {{𝕄 : RawMonadPlus M}} where

 char : Char → [ Parser Char Chars M Char ]
 char = exact

 space : [ Parser Char Chars M Char ]
 space = anyOf (' ' ∷ '\t' ∷ '\n' ∷ [])

 spaces : [ Parser Char Chars M (List⁺ Char) ]
 spaces = list⁺ space

 text : (t : String) {_ : T (not $ null $ String.toList t)} → [ Parser Char Chars M String ]
 text t {pr} with String.toList t | pr
 ... | []     | ()
 ... | x ∷ xs | _ = String.fromList ∘ NonEmpty.toList <$> exacts (x ∷ xs)

 module _ {A : Set} where

  parens : [ □ Parser Char Chars M A ⟶ Parser Char Chars M A ]
  parens = between (char '(') (return (char ')'))

  parens? : [ Parser Char Chars M A ⟶ Parser Char Chars M A ]
  parens? = between? (char '(') (return (char ')'))

  withSpaces : [ Parser Char Chars M A ⟶ Parser Char Chars M A ]
  withSpaces A = spaces ?&> A <&? return spaces
