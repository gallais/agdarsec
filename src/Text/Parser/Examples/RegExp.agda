module Text.Parser.Examples.RegExp where

open import Data.Bool.Base
open import Data.Char as Char
open import Data.List.Base     as List     hiding ([_])
open import Data.List.NonEmpty as NonEmpty hiding ([_])
open import Data.Maybe
open import Data.Product
open import Function
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Text.Parser.Examples.Base

infixr 5 _∥_
infixr 6 _∙_
infixl 7 _⋆

data Range : Set where
  singleton : Char            → Range
  interval  : (lb ub : Char) → Range

data RegExp : Set where
  ε     : RegExp
  `[_]  : (as : List⁺ Range) → RegExp
  `[^_] : (as : List Range) → RegExp
  _∥_   : (e₁ e₂ : RegExp) → RegExp
  _∙_   : (e₁ e₂ : RegExp) → RegExp
  _⋆    : (e : RegExp) → RegExp

literal : Char → RegExp
literal c = `[ NonEmpty.[ singleton c ] ]

data TOK : Set where
  OPEN NOPEN CLOSE : TOK
  ANY STAR DOTS OR : TOK
  LPAR RPAR        : TOK
  CHAR             : Char → TOK

isCHAR : TOK → Maybe Char
isCHAR (CHAR c) = just c
isCHAR _        = nothing

eqTOK : Decidable {A = TOK} _≡_
eqTOK OPEN     OPEN     = yes refl
eqTOK NOPEN    NOPEN    = yes refl
eqTOK CLOSE    CLOSE    = yes refl
eqTOK STAR     STAR     = yes refl
eqTOK ANY      ANY      = yes refl
eqTOK DOTS     DOTS     = yes refl
eqTOK OR       OR       = yes refl
eqTOK LPAR     LPAR     = yes refl
eqTOK RPAR     RPAR     = yes refl
eqTOK (CHAR c) (CHAR d) with c Char.≟ d
... | yes eq = yes (cong CHAR eq)
... | no ¬eq = no (¬eq ∘ cong (λ { (CHAR c) → c; _ → 'a' }))
eqTOK _ _ = no whatever where
  private postulate whatever : ∀ {A} → A

toTOKs : List Char → List TOK
toTOKs []               = []
toTOKs ('\\' ∷ c ∷ cs)  = CHAR c ∷ toTOKs cs
toTOKs ('[' ∷ '^' ∷ cs) = NOPEN  ∷ toTOKs cs
toTOKs ('[' ∷ cs)       = OPEN   ∷ toTOKs cs
toTOKs (']' ∷ cs)       = CLOSE  ∷ toTOKs cs
toTOKs ('.' ∷ '.' ∷ cs) = DOTS   ∷ toTOKs cs
toTOKs ('.' ∷ cs)       = ANY    ∷ toTOKs cs
toTOKs ('(' ∷ cs)       = LPAR   ∷ toTOKs cs
toTOKs (')' ∷ cs)       = RPAR   ∷ toTOKs cs
toTOKs ('*' ∷ cs)       = STAR   ∷ toTOKs cs
toTOKs ('|' ∷ cs)       = OR     ∷ toTOKs cs
toTOKs (c ∷ cs)         = CHAR c ∷ toTOKs cs

instance

  _ = eqTOK
  _ = mkTokenizer toTOKs

range : [ Parser TOK Maybe Range ]
range = (uncurry $ λ c md → maybe (interval c) (singleton c) md)
        <$> (maybeTok isCHAR <&?> (return $ exact DOTS &> return (maybeTok isCHAR)))

regexp : [ Parser TOK Maybe RegExp ]
regexp = fix (Parser TOK Maybe RegExp) $ λ rec →
         let lpar     = exact LPAR
             rpar     = return $ exact RPAR
             ranges   = (`[_] <$ exact OPEN <|> `[^_] ∘ toList <$ exact NOPEN) <*> list⁺ range <& return (exact CLOSE)
             literals = NonEmpty.foldr (_∙_ ∘ literal) literal <$> list⁺ (maybeTok isCHAR)
             base     = ranges <|> `[^ [] ] <$ exact ANY <|> literals <|> lpar &> rec <& rpar
             star     = (uncurry $ λ r → maybe (const $ r ⋆) r) <$> (base <&?> return (exact STAR))
             disj     = lpar ?&> chainr1 star (return $ _∥_ <$ exact OR) <&? rpar
         in NonEmpty.foldr _∙_ id <$> list⁺ disj

-- test

_ : "[a..zA..Z0..9-]*\\.agd(a|ai)" ∈ regexp
_ = `[ interval 'a' 'z' ∷ interval 'A' 'Z' ∷ interval '0' '9' ∷ singleton '-' ∷ [] ] ⋆
  ∙ (`[ singleton '.' ∷ [] ] ∙ `[ singleton 'a' ∷ [] ] ∙ `[ singleton 'g' ∷ [] ] ∙ `[ singleton 'd' ∷ [] ])
  ∙ (`[ singleton 'a' ∷ [] ]
  ∥  `[ singleton 'a' ∷ [] ] ∙ `[ singleton 'i' ∷ [] ]) !
