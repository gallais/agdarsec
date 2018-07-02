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

--------------------------------------------------------------------------------
-- An instrumented monad `M` for a parser parameterised by `P`

record Instrumented (P : Parameters) : Set₁ where
  open Parameters P
  field

-- In `P` the two sets we are most interested in are:
-- * Pos, the set of positions (in a file)
-- * Ann, the set of annotations

  -- `withAnnotation ann m` puts the annotation `ann` on the subcomputation `m`.
  -- Once `m` has finished the annotation should be discarded.
        withAnnotation : Ann → ∀ {A} → M A → M A
  -- `recordToken t` should be called every time a token `t` is read from the input
  -- list of tokens. It should update the position stored in `M` accordingly.
        recordToken    : Tok → M ⊤

  -- We also provide the user with the ability to ask for:
  -- * the current position in the file
  -- * the current annotation
  -- These capabilities can be used to put extra information in the AST produced
  -- by the parser for precise error-reporting later on in the pipeline.
        getPosition    : M Pos
        getAnnotation  : M (Maybe Ann)
open Instrumented public

--------------------------------------------------------------------------------
-- A typical implementation of Instruments for a character-based parser

module CharInstr
       {Chars : ℕ → Set} {{𝕊 : Sized Char Chars}}
       {M : Set → Set} {{𝕄 : RawMonad M}} {A : Set} where

-- This instrumentation uses a state to keep track of:
-- * the current position in the file (given by a Position aka a `line` & an `offset`)
-- * the stack of annotations pushed onto the current subcomputation

  St = Position × List A
  M′ = StateT St M

  open RawMonadState (StateTMonadState St 𝕄)

  charInstr : Instrumented (pos-ann Char Chars A M)

-- `withAnnotation ann ma` pushes `ann` onto the stack, runs `ma` and then drops `ann`
-- We assume that `ma` leaves the stack as it found it!

  withAnnotation charInstr ann ma = do
    modify (map₂ (ann ∷_))
    a ← ma
    modify (map₂ (drop 1))
    return a

-- `recordToken t` uses `Position`'s `next` to update the `line` & `offset`

  recordToken    charInstr t = do
    modify (map₁ (Position.next t))
    return tt

-- Finally, `getPosition` returns the current position
-- and `getAnnotation` returns the top of the stack (if it exists)

  getPosition    charInstr = proj₁ <$> get
  getAnnotation  charInstr = foldr (const ∘ just) nothing ∘ proj₂ <$> get

instance charInstr = CharInstr.charInstr


--------------------------------------------------------------------------------
-- A non-instrumented version of Instruments

-- Straightforward definition ignoring the additional opportunities provided by
-- `Instruments`.

module IgnoreInstr {Tok : Set} {Toks : ℕ → Set}
                   {M : Set → Set} {{𝕄 : RawMonad M}} where

  module 𝕄 = RawMonad 𝕄

  ignoreInstr : Instrumented (unInstr Tok Toks M)
  withAnnotation ignoreInstr = λ _ ma → ma
  recordToken    ignoreInstr = λ _ → 𝕄.pure tt
  getPosition    ignoreInstr = 𝕄.pure tt
  getAnnotation  ignoreInstr = 𝕄.return nothing

instance ignoreInstr = IgnoreInstr.ignoreInstr
