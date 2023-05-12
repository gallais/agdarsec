open import Level using (Level)

module Text.Parser.Polymorphic (l : Level) where

open import Function.Identity.Effectful using (Identity)
open import Effect.Monad
open import Data.Char.Base using (Char)
open import Data.Product using (proj₁)
open import Level.Bounded as Level≤ using (Set≤; theSet; [_]; lift; lower)
open import Relation.Unary using (IUniversal; _⇒_) public

open import Text.Parser.Types.Core
open import Text.Parser.Monad
open import Text.Parser.Position as Position using (Position; module Position) public

module CHARS = Agdarsec l [ Position ] Level≤.⊥ (record { into = proj₁ })

-- Our sized text is represented using vectors of characters

private
  ParserM : Set l → Set l
  ParserM = AgdarsecT [ Position ] Level≤.⊥ Identity

  P : Parameters l
  P = CHARS.chars

-- We re-export all of the combinators someone may need, specialised to CHARS

open Level≤ using ([_]) public
open import Text.Parser.Types               P hiding (runParser) public
open import Text.Parser.Combinators         {P = P} public
open import Text.Parser.Combinators.Numbers {P = P} public
open import Text.Parser.Combinators.Char    {P = P} public

-- We export all of the instances that are needed for the combinators to work
-- out of the box

open import Data.List.Sized.Interface using (vec) public
open import Data.Subset using (Subset-refl) public
open import Relation.Binary.PropositionalEquality.Decidable using (decide-char) public

instance

  P-monad : RawMonad ParserM
  P-monad  = CHARS.monad

  P-monad0 : RawMonadZero ParserM
  P-monad0 = CHARS.monadZero

  P-monad+ : RawMonadPlus ParserM
  P-monad+ = CHARS.monadPlus

-- Finally we define a function to run a parser and readily obtain a value

open import Data.Bool.Base using (if_then_else_)
open import Data.List.Base using ([])
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Nat.Base using (_≡ᵇ_)
import Data.Nat.Properties as ℕₚ
open import Data.Product using (_,_)
open import Data.String as String using (String)
open import Function.Base using (case_of_)

import Text.Parser.Monad.Result as Result
open import Text.Parser.Position using (start)

runParser : {A : Set≤ l} → ∀[ Parser A ] → String → Position ⊎ theSet A
runParser p str =
  let init  = lift (start , [])
      input = lift (String.toVec str)
  in case Result.toSum (Parser.runParser p (ℕₚ.n≤1+n _) input init) of λ where
        (inj₂ (res , p)) → let open Success in
                           if size res ≡ᵇ 0
                           then inj₂ (lower (value res))
                           else inj₁ (proj₁ (lower p))
        (inj₁ p) → inj₁ (lower p)
