module Text.Parser.Types where

open import Data.Nat
open import Induction.Nat.Strong

--------------------------------------------------------------------------------
-- PARAMETERS

-- A parser is parametrised by some types an type constructors.

record Parameters : Set₁ where
   field
-- Token-related parameters:
-- * Tok: tokens
-- * Toks: sized input (~ Vec Tok)
     Tok  : Set
     Toks : ℕ → Set
-- Documentation-related parameters (cf. Text.Parser.Instruments):
-- * Pos: positions in the source file
-- * Ann: annotations tacked onto a subcomputation
     Pos  : Set
     Ann  : Set
-- The monad stack used
     M    : Set → Set


-- Some examples

open import Data.Empty
open import Data.Unit using (⊤ ; tt)
open import Data.List
open import Data.Product
open import Category.Monad
open import Category.Monad.State
open import Text.Parser.Position

pos-ann : (Tok : Set) (Toks : ℕ → Set) (A : Set) (M : Set → Set) → Parameters
pos-ann T Ts A M = record
  { Tok = T        ; Toks = Ts
  ; Pos = Position ; Ann = A
  ; M = StateT (Position × List A) M
  }

instance
  rawmonadplus-vec : ∀ {S} {M : Set → Set} {{𝕄 : RawMonadPlus M}} →
                     RawMonadPlus (StateT S M)
  rawmonadplus-vec {{𝕄}} = StateTMonadPlus _ 𝕄

unInstr : (Tok : Set) (Toks : ℕ → Set) (M : Set → Set) → Parameters
unInstr Tok Toks M = record
  { Tok = Tok ; Toks = Toks
  ; Pos = ⊤   ; Ann = ⊥
  ; M = M
  }

--------------------------------------------------------------------------------
-- SUCCESS

-- A successful partial parse of an A is a value A together leftovers
-- which are proven to be smaller than the input

infix 1 _^_,_
record Success (Toks : ℕ → Set) (A : Set) (n : ℕ) : Set where
  constructor _^_,_
  field
    value     : A
    {size}    : ℕ
    .small    : size < n
    leftovers : Toks size

--------------------------------------------------------------------------------
-- PARSER

-- A parser is the ability to, given an input, return a computation for
-- a success.

record Parser (P : Parameters) (A : Set) (n : ℕ) : Set where
  constructor mkParser
  open Parameters P
  field runParser : ∀ {m} → .(m ≤ n) → Toks m → M (Success Toks A m)
open Parser public
