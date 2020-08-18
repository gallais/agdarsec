module SExp where

open import Data.Char.Base
open import Data.String.Base as String using (String)

data SExp : Set where
  Atom : String → SExp
  Pair : SExp → SExp → SExp

open import Category.Monad
open import Data.List.Sized.Interface
open import Data.List.NonEmpty as List⁺
open import Data.Maybe
open import Data.Product
open import Data.Subset
open import Function.Base
open import Induction.Nat.Strong
open import Relation.Unary using (IUniversal ; _⇒_)
open import Relation.Binary.PropositionalEquality.Decidable


open import Text.Parser.Types
open import Text.Parser.Combinators
open import Text.Parser.Combinators.Char

module _ {P : Parameters} (open Parameters P)
         {{𝕊 : Sized Tok Toks}}
         {{𝕄 : RawMonadPlus M}}
         {{𝔻 : DecidableEquality Tok}}
         {{ℂ : Subset Char Tok}}
         {{ℂ′ : Subset Tok Char}}
         where

  sexp : ∀[ Parser P SExp ]
  sexp = fix (Parser P SExp) $ λ rec →
    let atom = Atom ∘ String.fromList ∘ List⁺.toList ∘ List⁺.map (into ℂ′)
               <$> list⁺ alpha <&? box spaces

        sexp = (λ (a , mb) → maybe (Pair a) a mb)
               <$> parens (lift2 (λ p q → spaces ?&> p <&?> box (spaces ?&> q))
                                 rec
                                 rec) <&? box spaces
     in
     atom <|> sexp



open import Base

SEXP : ∀[ Parser chars SExp ]
SEXP = sexp

_ : "((this    is)
      ((a (  pair based))
          (S (expression))))   " ∈ SEXP
_ = Pair (Pair (Atom "this") (Atom "is"))
         (Pair (Pair (Atom "a")
                     (Pair (Atom "pair") (Atom "based")))
                (Pair (Atom "S")
                      (Atom "expression"))) !
