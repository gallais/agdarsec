module Text.Parser.Examples.Identifier where

open import Data.Nat.Base
open import Data.Char.Base
open import Data.Maybe as Maybe
open import Data.List as List hiding ([_])
open import Data.List.NonEmpty as NonEmpty hiding ([_])
open import Data.List.Sized.Interface using (Sized)
open import Data.Unit
open import Data.List.Sized
open import Data.String as String
open import Category.Monad
open import Function

open import Text.Parser.Types
open import Text.Parser.Instruments
open import Text.Parser.Examples.Base

record Identifier : Set where
  constructor mkIdentifier
  field getIdentifier : List⁺ Char

module _ (M   : Set → Set) {{_ : RawMonad M}} {{𝕄 : RawMonadPlus M}}
         (Chars : ℕ → Set) {{𝕊 : Sized Char Chars}}
         where

 identifier : [ Parser (vec Char Chars ⊤ M) Identifier ]
 identifier = mkIdentifier <$> list⁺ alpha

-- tests

instance
  _ = Maybe.monad

_ : "hi" ∈ {!identifier ? (∣List Char ∣≡_)!}
_ = {!!} -- mkIdentifier ('h' ∷ 'i' ∷ []) !
