module Text.Parser.Examples.Parentheses where

open import Data.Nat.Base
open import Data.Unit
open import Data.Maybe.Base
open import Data.Char
open import Data.List.Base as List hiding ([_])
open import Data.List.Sized.Interface
open import Data.Bool
open import Relation.Nullary
open import Relation.Binary
open import Agda.Builtin.Equality
open import Function

open import Text.Parser.Examples.Base

-- Well-parenthesised string
data PAR : Set where
  LPAR RPAR : PAR
  LCUR RCUR : PAR
  LSQU RSQU : PAR

instance
  {- eqPAR x y             -}
  {- C-c C-c x y           -}
  {- F3 C-c C-f C-c C-a F4 -}
  {- F4 (repeat ∣PAR∣^2)    -}
  eqPAR : Decidable {A = PAR} _≡_
  eqPAR LPAR LPAR = yes refl
  eqPAR LPAR RPAR = no (λ ())
  eqPAR LPAR LCUR = no (λ ())
  eqPAR LPAR RCUR = no (λ ())
  eqPAR LPAR LSQU = no (λ ())
  eqPAR LPAR RSQU = no (λ ())
  eqPAR RPAR LPAR = no (λ ())
  eqPAR RPAR RPAR = yes refl
  eqPAR RPAR LCUR = no (λ ())
  eqPAR RPAR RCUR = no (λ ())
  eqPAR RPAR LSQU = no (λ ())
  eqPAR RPAR RSQU = no (λ ())
  eqPAR LCUR LPAR = no (λ ())
  eqPAR LCUR RPAR = no (λ ())
  eqPAR LCUR LCUR = yes refl
  eqPAR LCUR RCUR = no (λ ())
  eqPAR LCUR LSQU = no (λ ())
  eqPAR LCUR RSQU = no (λ ())
  eqPAR RCUR LPAR = no (λ ())
  eqPAR RCUR RPAR = no (λ ())
  eqPAR RCUR LCUR = no (λ ())
  eqPAR RCUR RCUR = yes refl
  eqPAR RCUR LSQU = no (λ ())
  eqPAR RCUR RSQU = no (λ ())
  eqPAR LSQU LPAR = no (λ ())
  eqPAR LSQU RPAR = no (λ ())
  eqPAR LSQU LCUR = no (λ ())
  eqPAR LSQU RCUR = no (λ ())
  eqPAR LSQU LSQU = yes refl
  eqPAR LSQU RSQU = no (λ ())
  eqPAR RSQU LPAR = no (λ ())
  eqPAR RSQU RPAR = no (λ ())
  eqPAR RSQU LCUR = no (λ ())
  eqPAR RSQU RCUR = no (λ ())
  eqPAR RSQU LSQU = no (λ ())
  eqPAR RSQU RSQU = yes refl

  tokPAR : Tokenizer PAR
  tokPAR = mkTokenizer $ List.foldr (_++_ ∘ toPAR) [] where

    toPAR : Char → List PAR
    toPAR c = if c == '(' then LPAR ∷ []
         else if c == ')' then RPAR ∷ []
         else if c == '{' then LCUR ∷ []
         else if c == '}' then RCUR ∷ []
         else if c == '[' then LSQU ∷ []
         else if c == ']' then RSQU ∷ []
         else [] -- ignoring other characters as noise

module _ {PARS : ℕ → Set} {{𝕊 : Sized PAR PARS}} where

 PAR′ : [ Parser PAR PARS Maybe ⊤ ]
 PAR′ = fix (Parser PAR PARS Maybe ⊤) $ λ rec →
         tt <$ ((exact LPAR <&?> rec) <& return (exact RPAR <&?> rec))
     <|> tt <$ ((exact LCUR <&?> rec) <& return (exact RCUR <&?> rec))
     <|> tt <$ ((exact LSQU <&?> rec) <& return (exact RSQU <&?> rec))


-- tests

_ : "hel[{(lo({((wor))ld})wan)t}som{e()[n]o}i(s)e]?" ∈ PAR′
_ = _ !
