module Parentheses where

open import Data.Unit
open import Data.Maybe
open import Data.Char
open import Data.Char.Unsafe using (_==_)
open import Data.List.Base as List
import Data.List.Sized.Interface
open import Data.Bool
open import Relation.Nullary
open import Relation.Binary

open import Agda.Builtin.Equality
open import Function

open import Base

-- Well-parenthesised string
data PAR : Set where
  LPAR RPAR : PAR
  LCUR RCUR : PAR
  LSQU RSQU : PAR

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


instance
  _ : DecidableEquality PAR
  _ = record { decide = eqPAR }

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


Pars : Parameters
Pars = vec PAR

PAR′ : ∀[ Parser Pars ⊤ ]
PAR′ = fix (Parser Pars ⊤) $ λ rec →
   let _R?_R? : PAR → PAR → Parser Pars ⊤ _
       _R?_R? p q = tt <$ ((exact p <&?> rec) <& box (exact q <&?> rec))
   in    LPAR R? RPAR R?
     <|> LCUR R? RCUR R?
     <|> LSQU R? RSQU R?

-- tests

_ : "hel[{(lo({((wor))ld})wan)t}som{e()[n]o}i(s)e]?" ∈ PAR′
_ = _ !
