open import Level using (Level)

module Base (l : Level) where

open import Level.Bounded

import Data.Nat as Nat
open import Data.Nat.Properties
open import Data.Char.Base as Char using (Char)
import Data.Empty as Empty
open import Data.Product as Product using (_,_; proj₁)

open import Data.List.Base as List using ([]; _∷_)
open import Data.List.Categorical as List
open import Data.List.Sized.Interface

open import Data.String as String
open import Data.Vec as Vec using ()
open import Data.Bool
open import Data.Maybe as Maybe using (nothing; just; maybe′)
open import Data.Maybe.Categorical as MaybeCat
open import Data.Sum
open import Function
open import Category.Monad
open import Category.Monad.State
open import Relation.Nullary
open import Relation.Nullary.Decidable

open import Relation.Unary using (IUniversal; _⇒_) public
open import Relation.Binary.PropositionalEquality.Decidable public
open import Induction.Nat.Strong hiding (<-lower ; ≤-lower) public

open import Data.Subset                  public
open import Text.Parser.Types            public
open import Text.Parser.Position         public
open import Text.Parser.Combinators      public
open import Text.Parser.Combinators.Char public
open import Text.Parser.Monad public
open Agdarsec′ public

infix 0 _!
data Singleton {a} {A : Set a} : A → Set a where
  _! : (a : A) → Singleton a

record Tokenizer (A : Set≤ l) : Set (level (level≤ A)) where
  constructor mkTokenizer
  field tokenize : List.List Char → List.List (theSet A)

  fromText : String → List.List (theSet A)
  fromText = tokenize ∘ String.toList

instance
  tokChar : Tokenizer [ Char ]
  tokChar = mkTokenizer id

record RawMonadRun (M : Set l → Set l) : Set (Level.suc l) where
  field runM : ∀ {A} → M A → List.List A
open RawMonadRun

instance

  Agdarsec′M : RawMonad (Agdarsec {l} ⊤ ⊥)
  Agdarsec′M  = Agdarsec′.monad

  Agdarsec′M0 : RawMonadZero (Agdarsec {l} ⊤ ⊥)
  Agdarsec′M0 = Agdarsec′.monadZero

  Agdarsec′M+ : RawMonadPlus (Agdarsec {l} ⊤ ⊥)
  Agdarsec′M+ = Agdarsec′.monadPlus

  runMaybe : RawMonadRun Maybe.Maybe
  runMaybe = record { runM = maybe′ (_∷ []) [] }

  runList : RawMonadRun List.List
  runList = record { runM = id }

  runResult : {E : Set l} → RawMonadRun (Result E)
  runResult = record { runM = result (const []) (const []) (_∷ []) }

  runStateT : ∀ {M A} {{𝕄 : RawMonadRun M}} → RawMonadRun (StateT (Lift ([ Position ] × List A)) M)
  runStateT {{𝕄}} .RawMonadRun.runM =
    List.map proj₁
    ∘′ runM 𝕄
    ∘′ (_$ lift (start , []))

  monadMaybe : RawMonad {l} Maybe.Maybe
  monadMaybe = MaybeCat.monad

  plusMaybe : RawMonadPlus {l} Maybe.Maybe
  plusMaybe = MaybeCat.monadPlus

  monadList : RawMonad {l} List.List
  monadList = List.monad

  plusList : RawMonadPlus {l} List.List
  plusList = List.monadPlus

module _ {P : Parameters l} (open Parameters P)
         {{t : Tokenizer Tok}}
         {{𝕄 : RawMonadPlus M}}
         {{𝕊 : Sized Tok Toks}}
         {{𝕃 : ∀ {n} → Subset (theSet (Vec Tok n)) (theSet (Toks n))}}
         {{ℝ  : RawMonadRun M}} where

 private module 𝕄 = RawMonadPlus 𝕄
 private module 𝕃{n} = Subset (𝕃 {n})

 _∈_ : ∀ {A : Set≤ l} → String → ∀[ Parser P A ] → Set (level (level≤ A))
 s ∈ A =
  let input = Vec.fromList $ Tokenizer.fromText t s
      parse = runParser A (n≤1+n _) (lift $ 𝕃.into input)
      check = λ s → if ⌊ Success.size s Nat.≟ 0 ⌋
                    then just (Success.value s) else nothing
  in case List.TraversableM.mapM MaybeCat.monad check $ runM ℝ parse of λ where
       (just (a ∷ _)) → Singleton (lower a)
       _              → Lift ⊥
