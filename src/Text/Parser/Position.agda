module Text.Parser.Position where

open import Data.Bool
open import Data.Nat
import Data.Nat.Show as NShow
open import Data.Char using (Char ; _==_)
open import Data.String using (String ; _++_)

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

show : Position → String
show p = NShow.show (line p) ++ ":" ++ NShow.show (offset p)
