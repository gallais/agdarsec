module Text.Parser.Examples.Decimal where

open import Data.Nat.Base
open import Data.Char.Base
open import Data.List.Base as List hiding ([_])
open import Data.List.NonEmpty as NonEmpty hiding ([_])
open import Data.Maybe
open import Data.Product
open import Function

open import Text.Parser.Examples.Base

digit : [ Parser Char Maybe ℕ ]
digit = 0 <$ char '0'
    <|> 1 <$ char '1'
    <|> 2 <$ char '2'
    <|> 3 <$ char '3'
    <|> 4 <$ char '4'
    <|> 5 <$ char '5'
    <|> 6 <$ char '6'
    <|> 7 <$ char '7'
    <|> 8 <$ char '8'
    <|> 9 <$ char '9'

decimal : [ Parser Char Maybe ℕ ]
decimal = proj₁ ∘ List.foldr (λ v → uncurry $ λ t d → t + v * d , 10 * d) (0 , 1)
        ∘ NonEmpty.toList <$> list⁺ digit


-- tests

_ : "1005" ∈ decimal
_ = 1005 !

_ : "1" ∈ decimal
_ = 1 !

_ : "00000" ∈ decimal
_ = 0 !
