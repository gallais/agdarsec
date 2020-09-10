module Text.Parser.Monad where

open import Level using (Level; _⊔_)
open import Data.Empty using (⊥)
open import Data.Unit.Base using (⊤)
open import Data.Char.Base using (Char)
open import Data.Product
open import Data.List hiding (fromMaybe ; [_])
open import Data.Vec using (Vec)
open import Data.Maybe hiding (fromMaybe; _>>=_)
open import Data.Subset
open import Function

open import Category.Functor
open import Category.Applicative
open import Category.Monad

open import Function.Identity.Categorical as Id using (Identity)
open import Category.Monad.State

open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

-- open import Relation.Unary
open import Text.Parser.Types
open import Text.Parser.Position

private
  variable
    a b l : Level
    A : Set a
    B : Set b
    E : Set l

--------------------------------------------------------------------------------
-- RESULTT

data Result (E : Set l) (A : Set l) : Set l where
  SoftFail : E → Result E A
  HardFail : E → Result E A
  Value    : A → Result E A

result : {E A B : Set l} (soft hard : E → B) (val : A → B) → Result E A → B
result soft hard val = λ where
  (SoftFail e) → soft e
  (HardFail e) → hard e
  (Value v)    → val v

fromMaybe : E → Maybe A → Result E A
fromMaybe = maybe′ Value ∘′ SoftFail

ResultT : {{_ : a ≤l l}} →
          Set l →           -- Error
          (Set l → Set l) → -- Monad
          (Set a → Set l)
ResultT {{pr}} E M A = M (Result E (Lift pr A))

Result-monadT : ∀ (E : Set l) {M} → RawMonad M → RawMonad (ResultT E M)
Result-monadT E M = record
  { return = M.pure ∘′ Value
  ; _>>=_  = λ m f → m M.>>= result (M.pure ∘′ SoftFail) (M.pure ∘′ HardFail) f
  } where module M = RawMonad M

Result-monad : (E : Set l) → RawMonad (Result E)
Result-monad E = Result-monadT E Id.monad

{-
--------------------------------------------------------------------------------
-- AGDARSECT

AgdarsecT : {a : Level} {{_ : a ≤l l}} →
            Set l →           -- Error
            Set l →           -- Annotation
            (Set l → Set l) → -- Monad
            (Set a → Set l)
AgdarsecT {{pr}} E Ann M = StateT (Position × List Ann) (Lift pr ∘ ResultT E M)

Agdarsec : (E : Set l) (Ann : Set l) → (Set l → Set l)
Agdarsec E Ann = AgdarsecT E Ann Identity

module AgdarsecT
        (E C : Set l) {M : Set l → Set l}
        (𝕄 : RawMonad M)
        (𝕊 : Subset (Position × List C) E)
        where

  private module 𝕄 = RawMonad 𝕄

  monadT : RawMonad (AgdarsecT E C M)
  monadT = StateTMonad _ (Result-monadT E 𝕄)

  applicative : RawApplicative (AgdarsecT E C M)
  applicative = RawMonad.rawIApplicative monadT

  applicativeZero : RawApplicativeZero (AgdarsecT E C M)
  applicativeZero = record
    { applicative = applicative
    ; ∅           = 𝕄.pure ∘′ SoftFail ∘′ into 𝕊
    }

  monadZero : RawMonadZero (AgdarsecT E C M)
  monadZero = record
    { monad           = monadT
    ; applicativeZero = applicativeZero
    }

  alternative : RawAlternative (AgdarsecT E C M)
  alternative = record
    { applicativeZero = applicativeZero
    ; _∣_             = λ ma₁ ma₂ s → ma₁ s 𝕄.>>= λ where
        (SoftFail _) → ma₂ s
        r            → 𝕄.pure r
    }

  monadPlus : RawMonadPlus (AgdarsecT E C M)
  monadPlus = record
    { monad       = monadT
    ; alternative = alternative
    }

  monadState : RawMonadState (Position × List C) (AgdarsecT E C M)
  monadState = StateTMonadState _ (Result-monadT E 𝕄)

  private module ST = RawMonadState monadState

  getPosition : AgdarsecT E C M Position
  getPosition = proj₁ ST.<$> ST.get

  getAnnotations : AgdarsecT E C M (List C)
  getAnnotations = proj₂ ST.<$> ST.get

  withAnnotation : ∀ {A} → C → AgdarsecT E C M A → AgdarsecT E C M A
  withAnnotation c ma = let open ST in do
    ST.modify (map₂ (c ∷_))
    a ← ma
    ST.modify (map₂ (drop 1))
    ST.pure a

  recordChar : Char → AgdarsecT E C M ⊤
  recordChar c = _ ST.<$ ST.modify (map₁ (update c))

  -- Commiting to a branch makes all the failures in that branch hard failures
  -- that we cannot recover from
  commit : ∀ {A} → AgdarsecT E C M A → AgdarsecT E C M A
  commit m s = result HardFail HardFail Value 𝕄.<$> m s

  param : ∀ Tok Toks recTok → Parameters l
  param Tok Toks recTok = record
    { Tok         = Tok
    ; Toks        = Toks
    ; M           = AgdarsecT E C M
    ; recordToken = recTok
    }

  chars : Parameters
  chars = param Char (Vec Char) recordChar

{-
module Agdarsec E C (𝕊 : Subset (Position × List C) E) where

  private module M = AgdarsecT E C Id.monad 𝕊
  open M public renaming (monadT to monad) hiding (commit)

  module _ {Tok Toks recTok} where

    private P = param Tok Toks recTok
    commit : ∀ {A} → ∀[ Parser P A ⇒ Parser P A ]
    runParser (commit p) m≤n s = M.commit (runParser p m≤n s)


module Agdarsec′ where

  open Agdarsec ⊤ ⊥ _ public

  vec : Set → Parameters
  vec Tok = record
    { Tok         = Tok
    ; Toks        = Vec Tok
    ; M           = Agdarsec ⊤ ⊥
    ; recordToken = λ _ → M.pure _
    } where module M = RawMonad monad
-}
-}
