module RegExp where

import Level
open import Level.Bounded using ([_])
open import Data.Char as Char using (Char)
open import Data.List.Base as List using (List; []; _∷_)
open import Data.List.NonEmpty as List⁺ using (List⁺; toList; _∷_)
import Data.List.Sized.Interface
open import Data.Maybe using (Maybe; nothing; just; maybe)
open import Data.Product using (uncurry)

open import Function.Base using (_∘_; _$_; const; id)
open import Relation.Nullary using (yes; no)
open import Relation.Binary hiding (DecidableEquality)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import Base Level.zero

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
literal c = `[ List⁺.[ singleton c ] ]

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

  _ : DecidableEquality TOK
  _ = record { decide = eqTOK }
  _ : Tokenizer [ TOK ]
  _ = mkTokenizer toTOKs

P : Parameters Level.zero
P = vec [ TOK ]

aChar : ∀[ Parser P [ Char ] ]
aChar = maybeTok isCHAR

range : ∀[ Parser P [ Range ] ]
range = (uncurry $ λ c md → maybe (interval c) (singleton c) md)
        <$> (aChar <&?> (box $ exact DOTS &> box aChar))

regexp : ∀[ Parser P [ RegExp ] ]
regexp = fix (Parser P [ RegExp ]) $ λ rec →
         let parens   = between (exact LPAR) (box (exact RPAR))
             parens?  = between? (exact LPAR) (box (exact RPAR))
             ranges   = (`[_] <$ exact OPEN <|> `[^_] ∘ toList <$ exact NOPEN)
                        <*> box (list⁺ range <& box (exact CLOSE))
             literals = List⁺.foldr (_∙_ ∘ literal) literal <$> list⁺ aChar
             base     = ranges <|> `[^ [] ] <$ exact ANY <|> literals <|> parens rec
             star     : Parser P [ RegExp ] _
             star     = (uncurry $ λ r → maybe (const $ r ⋆) r) <$> (base <&?> box (exact STAR))
             disj     = chainr1 star (box $ _∥_ <$ exact OR)
         in List⁺.foldr _∙_ id <$> list⁺ (parens? disj)

-- test

_ : "[a..zA..Z0..9-]*\\.agd(a|ai)" ∈ regexp
_ = `[ interval 'a' 'z' ∷ interval 'A' 'Z' ∷ interval '0' '9' ∷ singleton '-' ∷ [] ] ⋆
  ∙ (literal '.' ∙ literal  'a' ∙ literal  'g' ∙ literal 'd')
  ∙ ((literal 'a')
  ∥  (literal 'a' ∙ literal 'i')) !
