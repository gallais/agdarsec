{-# OPTIONS --guardedness #-}

module Text.Parser.IO where

open import Data.String.Base as String using (String)
open import Data.Sum.Base using (inj₁; inj₂)
open import IO using (IO; pure)
open import Function.Base using (case_of_)
open import System.Exit

import Text.Parser.Position as Position
open import Text.Parser public

private
  variable
    A : Set

runParserIO : ∀[ Parser A ] → String → IO A
runParserIO p str = case runParser p str of λ where
  (inj₁ pos) → die ("Parse error at position: " String.++ Position.show pos)
  (inj₂ val) → pure val
