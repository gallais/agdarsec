------------------------------------------------------------------------
-- An opinionated frontend for the parser combinator library.
-- This module re-exports specialised versions of the combinators.
-- The design choices are as follows:
--
-- * Everything at level 0 (see Text.Parser.Polymorphic otherwise)
-- * Char as the type of tokens
-- * Sized text as the type of token lists
-- * Position as the error annotation
--
------------------------------------------------------------------------

module Text.Parser where

open import Level using (0ℓ)
open import Level.Bounded as Level≤ using ([_])
open import Category.Monad using (RawMonad; RawMonadZero; RawMonadPlus)
open import Function.Base using (const; _∘′_; case_of_)
open import Function.Identity.Categorical as Identity
open import Data.Bool.Base using (Bool; T; not; if_then_else_)
open import Data.Char.Base using (Char)
open import Data.Empty using (⊥)
open import Data.Integer.Base using (ℤ)
open import Data.Float.Base using (Float)
open import Data.List.Base as List using (List; []; null)
open import Data.List.NonEmpty as List⁺ using (List⁺)
open import Data.Maybe.Base using (Maybe)
open import Data.Nat.Base using (ℕ; _≡ᵇ_; NonZero)
import Data.Nat.Properties as ℕₚ
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁)
open import Data.Sign.Base using (Sign)
open import Data.String.Base as String using (String)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Unit.Base using (⊤)
open import Data.Vec.Base using (Vec)
open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Binary.PropositionalEquality.Decidable

open import Data.Singleton as Singleton public using (_!)
open import Induction.Nat.Strong public using (□_; call)
open import Relation.Unary public using (IUniversal; _⇒_)


open import Text.Parser.Types.Core using (module Success)
import Text.Parser.Types {0ℓ} as Types
import Text.Parser.Monad as Monad
import Text.Parser.Monad.Result as Result

open import Text.Parser.Position as Position public hiding (show)
open import Data.List.Sized.Interface using (Sized)
open import Data.Subset
open import Data.Text.Sized renaming (text to sized-text)

private
  module TXT = Monad.Agdarsec 0ℓ [ Position ] Level≤.⊥ (record { into = proj₁ })
  P = Monad.AgdarsecT.raw {0ℓ} [ Position ] Level≤.⊥ Identity.monad (record { into = proj₁ })
  ParserM = Monad.AgdarsecT {0ℓ} [ Position ] Level≤.⊥ Identity

private instance

  P-monad : RawMonad ParserM
  P-monad  = TXT.monad

  P-monad0 : RawMonadZero ParserM
  P-monad0 = TXT.monadZero

  P-monad+ : RawMonadPlus ParserM
  P-monad+ = TXT.monadPlus

  P-sized : Sized {0ℓ} [ Char ] (λ n → [ Text n ])
  P-sized = sized-text

Parser : (A : Set) (n : ℕ) → Set
Parser A = Types.Parser P [ A ]

private
  variable
    A B C : Set

runParser : ∀[ Parser A ] → String → Position ⊎ A
runParser p str =
  let init  = Level≤.lift (start , [])
      input = Level≤.lift (mkText str refl)
  in case Result.toSum (Types.Parser.runParser p (ℕₚ.n≤1+n _) input init) of λ where
        (inj₂ (res , p)) → if Success.size res ≡ᵇ 0
                           then inj₂ (Level≤.lower (Success.value res))
                           else inj₁ (proj₁ (Level≤.lower p))
        (inj₁ p) → inj₁ (Level≤.lower p)

_∈_ : String → ∀[ Parser A ] → Set
str ∈ p = Singleton.fromInj₂ (runParser p str)

_∉_ : String → ∀[ Parser A ] → Set
str ∉ p = [ const ⊤ , const ⊥ ]′ (runParser p str)

import Text.Parser.Combinators {0ℓ} {P} as Combinators

anyTok : ∀[ Parser Char ]
anyTok = Combinators.anyTok

anyChar = anyTok

guardM : (A → Maybe B) → ∀[ Parser A ⇒ Parser B ]
guardM = Combinators.guardM

guard : (A → Bool) → ∀[ Parser A ⇒ Parser A ]
guard = Combinators.guard

maybeTok : (Char → Maybe A) → ∀[ Parser A ]
maybeTok = Combinators.maybeTok

maybeChar = maybeTok

box : ∀[ Parser A ⇒ □ Parser A ]
box = Combinators.box

fail : ∀[ Parser A ]
fail = Combinators.fail

infixr 3 _<|>_
_<|>_ : ∀[ Parser A ⇒ Parser A ⇒ Parser A ]
_<|>_ = Combinators._<|>_

lift2 : ∀[ Parser A ⇒ Parser B ⇒ Parser C ] →
        ∀[ □ (Parser A) ⇒ □ (Parser B) ⇒ □ (Parser C) ]
lift2 = Combinators.lift2

lift2l : ∀[ Parser A ⇒ Parser B ⇒ Parser C ] ->
         ∀[ □ (Parser A) ⇒ Parser B ⇒ □ (Parser C) ]
lift2l = Combinators.lift2l

lift2r : ∀[ Parser A ⇒ Parser B ⇒ Parser C ] ->
         ∀[ Parser A ⇒ □ (Parser B) ⇒ □ (Parser C) ]
lift2r = Combinators.lift2r

infixr 5 _<$>_
_<$>_ : (A → B) → ∀[ Parser A ⇒ Parser B ]
_<$>_ = Combinators._<$>_

infixr 5 _<$_
_<$_ : B → ∀[ Parser A ⇒ Parser B ]
_<$_ = Combinators._<$_

_&?>>=_ : {B : A → Set} →
          ∀ {n} → Parser A n → ((a : A) → (□ Parser (B a)) n) →
          Parser (Σ[ a ∈ A ] Maybe (B a)) n
_&?>>=_ = Combinators._&?>>=_

_&>>=_ : {B : A → Set} →
         ∀ {n} → Parser A n → ((a : A) → (□ Parser (B a)) n) → Parser (Σ A B) n
_&>>=_ = Combinators._&>>=_

_?&>>=_ : {B : Maybe A → Set} →
          ∀ {n} → Parser A n → ((ma : Maybe A) → Parser (B ma) n) →
          Parser (Σ[ ma ∈ Maybe A ] B ma) n
_?&>>=_ = Combinators._?&>>=_

_&?>>=′_ : ∀[ Parser A ⇒ (const A ⇒ □ Parser B) ⇒
             Parser (A × Maybe B) ]
_&?>>=′_ = Combinators._&?>>=′_

_&>>=′_ : ∀[ Parser A ⇒ (const A ⇒ □ Parser B) ⇒ Parser (A × B) ]
_&>>=′_ = Combinators._&>>=′_

_?&>>=′_ : ∀[ Parser A ⇒ (const (Maybe A) ⇒ Parser B) ⇒
              Parser (Maybe A × B) ]
_?&>>=′_ = Combinators._?&>>=′_

_>>=_ : ∀[ Parser A ⇒ (const A ⇒ □ Parser B) ⇒ Parser B ]
_>>=_ = Combinators._>>=_

infixl 4 _<&>_ _<&_ _&>_
_<&>_ : ∀[ Parser A ⇒ □ Parser B ⇒ Parser (A × B) ]
_<&>_ = Combinators._<&>_

_<&_ : ∀[ Parser A ⇒ □ Parser B ⇒ Parser A ]
_<&_ = Combinators._<&_

_&>_ : ∀[ Parser A ⇒ □ Parser B ⇒ Parser B ]
_&>_ = Combinators._&>_

alts : ∀[ List ∘′ Parser A ⇒ Parser A ]
alts = Combinators.alts

ands : ∀[ List⁺ ∘′ Parser A ⇒ Parser (List⁺ A) ]
ands = Combinators.ands

infixl 4 _<*>_
_<*>_ : ∀[ Parser (A → B) ⇒ □ Parser A ⇒ Parser B ]
_<*>_ = Combinators._<*>_

infixl 4 _<&?>_ _<&?_ _&?>_
_<&?>_ : ∀[ Parser A ⇒ □ Parser B ⇒ Parser (A × Maybe B) ]
_<&?>_ = Combinators._<&?>_

_<&?_ : ∀[ Parser A ⇒ □ Parser B ⇒ Parser A ]
_<&?_ = Combinators._<&?_

_&?>_ : ∀[ Parser A ⇒ □ Parser B ⇒ Parser (Maybe B) ]
_&?>_ = Combinators._&?>_

infixr 3 _<⊎>_
_<⊎>_ : ∀[ Parser A ⇒ Parser B ⇒ Parser (A ⊎ B) ]
_<⊎>_ = Combinators._<⊎>_

infixl 4 _<?&>_ _<?&_ _?&>_
_<?&>_ : ∀[ Parser A ⇒ Parser B ⇒ Parser (Maybe A × B) ]
_<?&>_ = Combinators._<?&>_

_<?&_ : ∀[ Parser A ⇒ Parser B ⇒ Parser (Maybe A) ]
_<?&_ = Combinators._<?&_

_?&>_ : ∀[ Parser A ⇒ Parser B ⇒ Parser B ]
_?&>_ = Combinators._?&>_

between : ∀[ Parser A ⇒ □ Parser C ⇒ □ Parser B ⇒ Parser B ]
between = Combinators.between

between? : ∀[ Parser A ⇒ □ Parser C ⇒ Parser B ⇒ Parser B ]
between? = Combinators.between?

anyOf : List Char → ∀[ Parser Char ]
anyOf = Combinators.anyOf

exact : Char → ∀[ Parser Char ]
exact = Combinators.exact

exacts : List⁺ Char → ∀[ Parser (List⁺ Char) ]
exacts = Combinators.exacts

noneOf : List Char → ∀[ Parser Char ]
noneOf = Combinators.noneOf

anyTokenBut : Char → ∀[ Parser Char ]
anyTokenBut = Combinators.anyTokenBut

anyCharBut = anyTokenBut

iterate : ∀[ Parser A ⇒ □ Parser (A → A) ⇒ Parser A ]
iterate = Combinators.iterate

hchainl : ∀[ Parser A ⇒ □ Parser (A → B → A) ⇒ □ Parser B ⇒ Parser A ]
hchainl = Combinators.hchainl

chainl1 : ∀[ Parser A ⇒ □ Parser (A → A → A) ⇒ Parser A ]
chainl1 = Combinators.chainl1

chainr1 : ∀[ Parser A ⇒ □ Parser (A → A → A) ⇒ Parser A ]
chainr1 = Combinators.chainr1

head+tail : ∀[ Parser A ⇒ □ Parser A ⇒ Parser (List⁺ A) ]
head+tail = Combinators.head+tail

list⁺ : ∀[ Parser A ⇒ Parser (List⁺ A) ]
list⁺ = Combinators.list⁺

replicate : (n : ℕ) → {NonZero n} → ∀[ Parser A ⇒ Parser (Vec A n) ]
replicate = Combinators.replicate

import Text.Parser.Combinators.Numbers {0ℓ} {P} as Numbers

decimalDigit : ∀[ Parser ℕ ]
decimalDigit = Numbers.decimalDigit

hexadecimalDigit : ∀[ Parser ℕ ]
hexadecimalDigit = Numbers.hexadecimalDigit

sign : ∀[ Parser Sign ]
sign = Numbers.sign

decimalℕ : ∀[ Parser ℕ ]
decimalℕ = Numbers.decimalℕ

decimalℤ : ∀[ Parser ℤ ]
decimalℤ = Numbers.decimalℤ

decimalFloat : ∀[ Parser Float ]
decimalFloat = Numbers.decimalFloat

import Text.Parser.Combinators.Char {0ℓ} {P} as Chars

char : Char → ∀[ Parser Char ]
char = Chars.char

noneOfChars : List Char → ∀[ Parser Char ]
noneOfChars = Chars.noneOfChars

anyOfChars : List Char → ∀[ Parser Char ]
anyOfChars = Chars.anyOfChars

space : ∀[ Parser Char ]
space = Chars.space

spaces : ∀[ Parser (List⁺ Char) ]
spaces = Chars.spaces

text : (t : String) {_ : T (not (null (String.toList t)))} →
       ∀[ Parser (List⁺ Char) ]
text = Chars.text

parens : ∀[ □ Parser A ⇒ Parser A ]
parens = Chars.parens

parens? : ∀[ Parser A ⇒ Parser A ]
parens? = Chars.parens?

withSpaces : ∀[ Parser A ⇒ Parser A ]
withSpaces = Chars.withSpaces

lowerAlpha : ∀[ Parser Char ]
lowerAlpha = Chars.lowerAlpha

upperAlpha : ∀[ Parser Char ]
upperAlpha = Chars.upperAlpha

alpha : ∀[ Parser Char ]
alpha = Chars.alpha

alphas⁺ : ∀[ Parser (List⁺ Char) ]
alphas⁺ = Chars.alphas⁺

num : ∀[ Parser ℕ ]
num = decimalDigit

alphanum : ∀[ Parser (Char ⊎ ℕ) ]
alphanum = Chars.alphanum

stringLiteral : ∀[ Parser String ]
stringLiteral = Chars.stringLiteral
