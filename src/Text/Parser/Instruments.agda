module Text.Parser.Instruments where

open import Data.Unit
open import Data.Char
open import Data.Nat
open import Data.Product
open import Data.Maybe
open import Data.List
open import Data.List.Sized.Interface using (Sized)
open import Category.Monad
open import Category.Monad.State
open import Function

open import Text.Parser.Types
open import Text.Parser.Position as Position

-- An instrumented monad `M` for a parser processing tokens of type `Tok`.

record Instrumented (P : Parameters) : Set₁ where
  open Parameters P
  field

-- It is parametrised over two Sets: the set Pos of positions (in a file)
-- and the set Ann of annotations.

  -- `withAnnotation ann m` puts the annotation `ann` on the subcomputation `m`.
  -- Once `m` has finished the annotation should be discarded.
        withAnnotation : Ann → ∀ {A} → M A → M A
  -- `recordToken t` should be called every time a token `t` is read from the input
  -- list of tokens. It should update the position stored in `M` accordingly.
        recordToken    : Tok → M ⊤
        getPosition    : M Pos
        getAnnotation  : M (Maybe Ann)
open Instrumented public

module CharInstr
       {Chars : ℕ → Set} {{𝕊 : Sized Char Chars}}
       {M : Set → Set} {{𝕄 : RawMonad M}} {A : Set} where

  St = Position × List A
  M′ = StateT St M

  open RawMonadState (StateTMonadState St 𝕄)

  charInstr : Instrumented (vec Char Chars A M)
  withAnnotation charInstr ann ma = do
    modify (map₂ (ann ∷_))
    a ← ma
    modify (map₂ (drop 1))
    return a
  recordToken    charInstr t = do
    modify (map₁ (Position.next t))
    return tt
  getPosition    charInstr = proj₁ <$> get
  getAnnotation  charInstr = foldr (const ∘ just) nothing ∘ proj₂ <$> get

instance charInstr = CharInstr.charInstr

module IgnoreInstr {Tok : Set} {Toks : ℕ → Set}
                   {M : Set → Set} {{𝕄 : RawMonad M}} {A : Set} where

  module 𝕄 = RawMonad 𝕄

  ignoreInstr : Instrumented (unInstr Tok Toks M)
  withAnnotation ignoreInstr = λ _ ma → ma
  recordToken    ignoreInstr = λ _ → 𝕄.pure tt
  getPosition    ignoreInstr = 𝕄.pure tt
  getAnnotation  ignoreInstr = 𝕄.return nothing
