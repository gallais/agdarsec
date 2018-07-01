module Text.Parser.Examples.Base where

open import Level
open import Data.Unit
open import Data.Nat.Base as Nat
open import Data.Nat.Properties
open import Data.Char.Base
open import Data.Product
open import Data.String as String
open import Data.List.Base as L hiding ([_] ; module List)
open import Data.List.Categorical as List
open import Data.List.Sized as Sized hiding (map) public
open import Data.List.Sized.Interface
open import Data.List.Any as Any
open import Data.Bool
open import Data.Maybe as Maybe
open import Data.Sum
open import Data.Empty
open import Function
open import Category.Monad
open import Category.Monad.State
open import Relation.Nullary
open import Relation.Nullary.Decidable

open import Relation.Unary.Indexed public
open import Relation.Binary.PropositionalEquality.Decidable public
open import Induction.Nat.Strong hiding (<-lower ; ≤-lower) public

open import Data.Subset public
open import Text.Parser.Types
open import Text.Parser.Position
open import Text.Parser.Combinators public
open import Text.Parser.Char public

infix 0 _!
data Singleton {A : Set} : A → Set where
  _! : (a : A) → Singleton a

record Tokenizer (A : Set) : Set where
  constructor mkTokenizer
  field tokenize : List Char → List A

  fromText : String → List A
  fromText = tokenize ∘ String.toList

instance tokChar = mkTokenizer id

record RawMonadRun (M : Set → Set) : Set₁ where
  field runM : ∀ {A} → M A → List A

open RawMonadRun {{...}}

instance

  runMaybe : RawMonadRun Maybe
  runMaybe = record { runM = maybe (_∷ []) [] }

  runList : RawMonadRun List
  runList = record { runM = id }

  runStateT : ∀ {M} {{𝕄 : RawMonadRun M}} → RawMonadRun (StateT (Position × ⊤) M)
  runStateT {{𝕄}} = record { runM = L.map proj₁ ∘ runM {{𝕄}} ∘ (_$ (start , tt)) }

  plusMaybe : RawMonadPlus {Level.zero} Maybe
  plusMaybe = Maybe.monadPlus

  plusList : RawMonadPlus {Level.zero} List
  plusList = List.monadPlus

module _ {P : Parameters} (open Parameters P)
         {{t : Tokenizer Tok}}
         {{𝕄 : RawMonadPlus M}}
         {{𝕊 : Sized Tok Toks}}
         {{𝕃 : ∀ n → Subset (∣List Tok ∣≡ n) (Toks n)}}
         {{ℝ  : RawMonadRun M}} where

 private module 𝕄 = RawMonadPlus 𝕄
 private module 𝕃 {n} = Subset (𝕃 n)

 _∈_ : {A : Set} → String → [ Parser P A ] → Set
 s ∈ A =
  let input = Sized.fromList $ Tokenizer.fromText t s
      parse = runParser A (n≤1+n _) (𝕃.into input)
      check = λ s → if ⌊ Success.size s Nat.≟ 0 ⌋
                    then just (Success.value s) else nothing
  in case mapM Maybe.monad check $ runM parse of λ where
       (just (a ∷ _)) → Singleton a
       _              → ⊥
