module Text.Parser.Monad.Result where

open import Level using (Level)
open import Level.Bounded using (Set≤; Lift)
open import Effect.Monad using (RawMonad; mkRawMonad)
open import Effect.Empty
open import Effect.Choice
open import Data.Maybe.Base using (Maybe; maybe′)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Function.Base using (_∘′_)
import Function.Identity.Effectful as Id

private
  variable
    l e a b : Level
    E : Set e
    A : Set a
    B : Set b

data Result (E : Set e) (A : Set a) : Set (a Level.⊔ e) where
  SoftFail : E → Result E A
  HardFail : E → Result E A
  Value    : A → Result E A

result : (soft hard : E → B) (val : A → B) → Result E A → B
result soft hard val = λ where
  (SoftFail e) → soft e
  (HardFail e) → hard e
  (Value v)    → val v

toSum : Result E A → E ⊎ A
toSum = result inj₁ inj₁ inj₂

fromMaybe : E → Maybe A → Result E A
fromMaybe = maybe′ Value ∘′ SoftFail

map : (A → B) → Result E A → Result E B
map f (SoftFail e) = SoftFail e
map f (HardFail e) = HardFail e
map f (Value v)    = Value (f v)

ResultT : Set≤ l →          -- Error
          (Set l → Set l) → -- Monad
          (Set l → Set l)
ResultT E M A = M (Result (Lift E) A)

Result-monadT : ∀ (E : Set≤ l) {M} → RawMonad M → RawMonad (ResultT E M)
Result-monadT E {M} monad-M = mkRawMonad (ResultT E M) pure _>>=_
  where
    module M = RawMonad monad-M
    pure : ∀ {A} → A → ResultT E M A
    pure = M.pure ∘′ Value
    _>>=_ : ∀ {A B} → ResultT E M A → (A → ResultT E M B) → ResultT E M B
    _>>=_ = λ m f → m M.>>= result (M.pure ∘′ SoftFail) (M.pure ∘′ HardFail) f

Result-monad : (E : Set≤ l) → RawMonad (Result (Lift E))
Result-monad E = Result-monadT E Id.monad

ResultT-choice : ∀ (E : Set≤ l) {M} → RawMonad M → RawChoice {ℓ = l} (ResultT E M)
ResultT-choice E M = record
  { _<|>_ = λ m₁ m₂ → m₁ >>= λ where
      (SoftFail _) → m₂
      r → pure r
  } where open RawMonad M
