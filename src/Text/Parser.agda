open import Level using (Level)

module Text.Parser (l : Level) where

open import Category.Monad
open import Data.Char.Base using (Char)
open import Level.Bounded as Level≤ using (Set≤; theSet; [_]; lift; lower)
open import Relation.Unary

open import Text.Parser.Types.Core
open import Text.Parser.Monad

-- Our sized text is represented using vectors of characters
CHARS : Parameters l
CHARS = Agdarsec′.vec [ Char ]

-- We re-export all of the combinators someone may need, specialised to CHARS

open import Text.Parser.Types               CHARS hiding (runParser) public
open import Text.Parser.Combinators         {P = CHARS} public
open import Text.Parser.Combinators.Numbers {P = CHARS} public
open import Text.Parser.Combinators.Char    {P = CHARS} public

-- We export all of the instances that are needed for the combinators to work
-- out of the box

open import Data.List.Sized.Interface using (vec) public
open import Data.Subset using (Subset-refl) public

instance

  CHARS-monad : RawMonad (Agdarsec {l} Level≤.⊤ Level≤.⊥)
  CHARS-monad  = Agdarsec′.monad

  CHARS-monad0 : RawMonadZero (Agdarsec {l} Level≤.⊤ Level≤.⊥)
  CHARS-monad0 = Agdarsec′.monadZero

  CHARS-monad+ : RawMonadPlus (Agdarsec {l} Level≤.⊤ Level≤.⊥)
  CHARS-monad+ = Agdarsec′.monadPlus

-- Finally we define a function to run a parser and readily obtain a value

open import Data.Bool.Base using (if_then_else_)
open import Data.List.Base using ([])
open import Data.Maybe.Base using (Maybe; nothing; just)
open import Data.Nat.Base using (_≡ᵇ_)
import Data.Nat.Properties as ℕₚ
open import Data.Product using (_,_)
open import Data.String as String using (String)
open import Function.Base using (case_of_)

open import Text.Parser.Monad.Result using (Value)
open import Text.Parser.Position using (start)

runParser : {A : Set≤ l} → ∀[ Parser A ] → String → Maybe (theSet A)
runParser p str =
  let init  = lift (start , [])
      input = lift (String.toVec str)
  in case Parser.runParser p (ℕₚ.n≤1+n _) input init of λ where
        (Value (res , _)) → let open Success in
                            if size res ≡ᵇ 0
                            then just (lower (value res))
                            else nothing
        _ → nothing
