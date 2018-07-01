module Text.Parser.Position where

open import Data.Nat
open import Data.Char
open import Data.Bool

record Position : Set where
  field line   : ℕ
        offset : ℕ
open Position public

start : Position
line   start = 0
offset start = 0

next : Char → Position → Position
next c p = if c == '\n'
  then record { line = suc (line p) ; offset = 0 }
  else record p { offset = suc (offset p) }
