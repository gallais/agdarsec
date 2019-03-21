{-# OPTIONS --without-K --safe #-}

module Text.Parser.Position where

open import Data.Bool
open import Data.Nat
import Data.Nat.Show as NShow
open import Data.Char using (Char; _==_)
open import Data.String using (String ; _++_; toList)
open import Data.List.Base using (foldl)
open import Function

record Position : Set where
  constructor _∶_
  field line   : ℕ
        offset : ℕ
open Position public

start : Position
line   start = 0
offset start = 0

update : Char → Position → Position
update c p = if c == '\n'
  then record { line = suc (line p) ; offset = 0 }
  else record p { offset = suc (offset p) }

updates : String → Position → Position
updates str p = foldl (flip update) p (toList str)

show : Position → String
show p = NShow.show (line p) ++ ":" ++ NShow.show (offset p)

-- Deprecated names

next = update
{-# WARNING_ON_USAGE next
"Warning: next was deprecated in v0.2.3.
Please use update instead."
#-}
