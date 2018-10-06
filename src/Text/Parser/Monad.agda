module Text.Parser.Monad where

open import Data.Empty
open import Data.Unit
open import Data.Char
open import Data.Product as Prod hiding (,_)
open import Data.List hiding (fromMaybe ; [_])
open import Data.Vec using (Vec)
open import Data.Maybe hiding (monad ; monadT ; monadZero ; monadPlus)
open import Data.Subset
open import Function
open import Category.Functor
open import Category.Monad
open import Category.Monad.Identity
open import Category.Monad.State

open import Relation.Unary.Indexed
open import Text.Parser.Types
open import Text.Parser.Position

--------------------------------------------------------------------------------
-- RESULTT

data Result (E : Set) (A : Set) : Set where
  SoftFail : E → Result E A
  HardFail : E → Result E A
  Value    : A → Result E A

result : {E A B : Set} (soft hard : E → B) (val : A → B) → Result E A → B
result soft hard val = λ where
  (SoftFail e) → soft e
  (HardFail e) → hard e
  (Value v)    → val v

fromMaybe : ∀ {E A} → E → Maybe A → Result E A
fromMaybe = maybe′ Value ∘′ SoftFail

ResultT : Set → (Set → Set) → (Set → Set)
ResultT E M A = M (Result E A)

Result-monadT : ∀ E {M} → RawMonad M → RawMonad (ResultT E M)
Result-monadT E M = record
  { return = M.pure ∘′ Value
  ; _>>=_  = λ m f → m M.>>= result (M.pure ∘′ SoftFail) (M.pure ∘′ HardFail) f
  } where module M = RawMonad M

Result-monad : ∀ E → RawMonad (Result E)
Result-monad E = Result-monadT E IdentityMonad

--------------------------------------------------------------------------------
-- AGDARSECT

AgdarsecT : Set →         -- Error
            Set →         -- Annotation
            (Set → Set) → -- Monad
            (Set → Set)
AgdarsecT E C M = StateT (Position × List C) (ResultT E M)

Agdarsec : (E C : Set) → (Set → Set)
Agdarsec E C = AgdarsecT E C Identity

module AgdarsecT
        (E C : Set) {M : Set → Set}
        (𝕄 : RawMonad M)
        (𝕊 : Subset (Position × List C) E)
        where

  private module 𝕄 = RawMonad 𝕄

  monadT : RawMonad (AgdarsecT E C M)
  monadT = StateTMonad _ (Result-monadT E 𝕄)

  monadZero : RawMonadZero (AgdarsecT E C M)
  monadZero = record
    { monad = monadT
    ; ∅     = 𝕄.pure ∘′ SoftFail ∘′ into 𝕊
    }

  monadPlus : RawMonadPlus (AgdarsecT E C M)
  monadPlus = record
    { monadZero = monadZero
    ; _∣_       = λ ma₁ ma₂ s → ma₁ s 𝕄.>>= λ where
        (SoftFail _) → ma₂ s
        r            → 𝕄.pure r
    }

  monadState : RawMonadState (Position × List C) (AgdarsecT E C M)
  monadState = StateTMonadState _ (Result-monadT E 𝕄)

  private module ST = RawMonadState monadState

  getPosition : AgdarsecT E C M Position
  getPosition = proj₁ ST.<$> ST.get

  getAnnotations : AgdarsecT E C M (List C)
  getAnnotations = proj₂ ST.<$> ST.get

  withAnnotation : ∀ {A} → C → AgdarsecT E C M A → AgdarsecT E C M A
  withAnnotation c ma = let open ST in
    ST.modify (Prod.map id (c ∷_)) >>
    ma >>= λ a →
    ST.modify (Prod.map id (drop 1)) >>
    ST.pure a

  recordChar : Char → AgdarsecT E C M ⊤
  recordChar c = tt ST.<$ ST.modify (Prod.map (next c) id)

  -- Commiting to a branch makes all the failures in that branch hard failures
  -- that we cannot recover from
  commit : ∀ {A} → AgdarsecT E C M A → AgdarsecT E C M A
  commit m s = result HardFail HardFail Value 𝕄.<$> m s

  param : ∀ Tok Toks recTok → Parameters
  param Tok Toks recTok = record
    { Tok         = Tok
    ; Toks        = Toks
    ; M           = AgdarsecT E C M
    ; recordToken = recTok
    }

  chars : Parameters
  chars = param Char (Vec Char) recordChar

module Agdarsec E C (𝕊 : Subset (Position × List C) E) where

  private module M = AgdarsecT E C IdentityMonad 𝕊
  open M public renaming (monadT to monad) hiding (commit)

  module _ {Tok Toks recTok} where

    private P = param Tok Toks recTok
    commit : ∀ {A} → [ Parser P A ⟶ Parser P A ]
    runParser (commit p) m≤n s = M.commit (runParser p m≤n s)


module Agdarsec′ where

  open Agdarsec ⊤ ⊥ _ public

  vec : Set → Parameters
  vec Tok = record
    { Tok         = Tok
    ; Toks        = Vec Tok
    ; M           = Agdarsec ⊤ ⊥
    ; recordToken = λ _ → M.pure tt
    } where module M = RawMonad monad
