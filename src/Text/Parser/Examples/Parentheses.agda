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
  eqPAR : Decidable {A = PAR} _≡_
  eqPAR LPAR LPAR = yes refl
  eqPAR RPAR RPAR = yes refl
  eqPAR LCUR LCUR = yes refl
  eqPAR RCUR RCUR = yes refl
  eqPAR LSQU LSQU = yes refl
  eqPAR RSQU RSQU = yes refl
  -- catchall for no
  eqPAR _ _ = no whatever where
    postulate whatever : {A : Set} → A

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
         tt <$ ((exact LPAR <&?> rec) <& box (exact RPAR <&?> rec))
     <|> tt <$ ((exact LCUR <&?> rec) <& box (exact RCUR <&?> rec))
     <|> tt <$ ((exact LSQU <&?> rec) <& box (exact RSQU <&?> rec))


-- tests

_ : "hel[{(lo({((wor))ld})wan)t}som{e()[n]o}i(s)e]?" ∈ PAR′
_ = _ !
