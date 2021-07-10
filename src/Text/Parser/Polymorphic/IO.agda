{-# OPTIONS --guardedness #-}

open import Level using (Level)

module Text.Parser.Polymorphic.IO (l : Level) where

open import Level.Bounded using (Set≤; theSet)
open import Data.String.Base as String using (String)
open import Data.Sum.Base using (inj₁; inj₂)
open import IO using (IO; pure)
open import Function.Base using (case_of_)
open import System.Exit

import Text.Parser.Position as Position
open import Text.Parser.Polymorphic l public

runParserIO : {A : Set≤ l} → ∀[ Parser A ] → String → IO (theSet A)
runParserIO p str = case runParser p str of λ where
  (inj₁ pos) → die ("Parse error at position: " String.++ Position.show pos)
  (inj₂ val) → pure val
