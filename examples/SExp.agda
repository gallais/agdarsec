module SExp where

import Level
open import Level.Bounded using (theSet; [_])
open import Data.Char.Base
open import Data.String.Base as String using (String)

data SExp : Set where
  Atom : String → SExp
  Pair : SExp → SExp → SExp

open import Category.Monad
open import Data.List.Sized.Interface
open import Data.List.NonEmpty as List⁺ using (List⁺)
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

module _ {l} (P : Parameters l) (open Parameters P)
         {{𝕊 : Sized Tok Toks}}
         {{𝕄 : RawMonadPlus M}}
         {{𝔻 : DecidableEquality (theSet Tok)}}
         {{ℂ : Subset Char (theSet Tok)}}
         {{ℂ′ : Subset (theSet Tok) Char}}
         where

  sexp : ∀[ Parser P [ SExp ] ]
  sexp =
    -- SExp is an inductive type so we build the parser as a fixpoint
    fix (Parser P [ SExp ]) $ λ rec →
        -- First we have atoms. Assuming we have already consumed the leading space, an
        -- atom is just a non empty list of alphabetical characters.

        -- We use `<$>` to turn that back into a string and apply the `Atom` constructor.
    let atom = Atom ∘ String.fromList ∘ List⁺.toList ∘ List⁺.map (into ℂ′)
               <$> list⁺ alpha

        -- Then we have subexpressions. Here we have to be a bit careful: we can have both
        -- * a sexp with additional parentheses à la `(e)`
        -- * pairing constructs à la `(e f)`

        -- In both cases they are surrounded by parentheses so we use `parens` and then we
        -- 1. unconditionally parse a subexpression thanks to `rec` introduced by the fixpoint earlier
        -- 2. _potentially_ consume a second subexpression (the `?`-tagged combinators are variants
        --    that are allowed to fail on the side the question mark is on).

        -- I give a bit more details about `lift` and `box` below.
        -- As for the previous case we use `<$>` to massage the result into a `SExp`.
        sexp = (λ (a , mb) → maybe (Pair a) a mb)
               <$> parens (lift2 (λ p q → (spaces ?&> p <&? box spaces) <&?> box (q <&? box spaces))
                                 rec
                                 rec)
     in

     -- Finally we can put the two things together by using a simple disjunction
     atom <|> sexp


        -- `lift`:
        -- parens is guaranteed to consume some of its input before calling its argument so
        -- the argument is guarded. We are however not making a direct call to `rec` in a guarded
        -- position: we are taking a (potentially failing) pairing of two sub-parsers, potentially
        -- eating some space, etc. So we use `lift2` as a way to distribute the proof that we are in
        -- a guarded position to the key elements that need it.

        -- `box`:
        -- sometimes on the other hand we have a guarded call but do not actually care. We can use
        -- `box` to discard the proof and use a normal parser in that guarded position.


  -- The full parser is obtained by disregarding spaces before & after the expression
  SEXP : ∀[ Parser P [ SExp ] ]
  SEXP = spaces ?&> sexp <&? box spaces

open import Base Level.zero

-- And we can run the thing on a test (which is very convenient when refactoring grammars!..):
_ : "((  this    is)
      ((a (  pair based))
          ((S)(expression  ))))   " ∈ SEXP chars
_ = Pair (Pair (Atom "this") (Atom "is"))
         (Pair (Pair (Atom "a")
                     (Pair (Atom "pair") (Atom "based")))
                (Pair (Atom "S")
                      (Atom "expression"))) !
